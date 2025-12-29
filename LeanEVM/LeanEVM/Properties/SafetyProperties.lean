import LeanEVM.Core.Types
import LeanEVM.Core.Execution
import LeanEVM.Contracts.ERC20

/-!
# Safety Properties Framework

Common smart contract safety property patterns.
-/

namespace LeanEVM.Properties

open LeanEVM
open LeanEVM.Contracts

/-! ## Access Control Properties -/

/-- An address has a specific role -/
structure Role where
  name : String
  members : Address → Bool

/-- Only role members can execute an action -/
def onlyRole {S : Type} (role : Role) (msg : MsgContext)
    (action : S → ExecResult S) (state : S) : ExecResult S :=
  if role.members msg.sender then
    action state
  else
    ExecResult.revert s!"AccessControl: account is missing role {role.name}"

/-- Property: action reverts for non-members -/
theorem onlyRole_reverts_non_member {S : Type} (role : Role) (msg : MsgContext)
    (action : S → ExecResult S) (state : S)
    (h_not_member : role.members msg.sender = false) :
    ∃ m, onlyRole role msg action state = ExecResult.revert m := by
  refine ⟨s!"AccessControl: account is missing role {role.name}", ?_⟩
  simp only [onlyRole, h_not_member]
  rfl

/-! ## Reentrancy Safety Properties -/

/-- Prove a guarded function is reentrancy safe -/
theorem guarded_is_reentrancy_safe {S : Type}
    (action : S → ExecResult S)
    (gs : GuardedState S)
    (h_locked : gs.isLocked = true) :
    ∃ m, withReentrancyGuard gs action = ExecResult.revert m := by
  refine ⟨"ReentrancyGuard: reentrant call", ?_⟩
  simp only [withReentrancyGuard, GuardedState.acquireLock, h_locked]
  rfl

/-! ## Vault Pattern -/

/-- Simple vault state -/
structure VaultState where
  deposits : Address → Nat
  totalDeposited : Nat

/-- Deposit into vault -/
def vaultDeposit (state : VaultState) (msg : MsgContext) (amount : Nat) :
    ExecResult VaultState := do
  require (amount > 0) "Vault: zero deposit"
  let newBal := state.deposits msg.sender + amount
  pure {
    deposits := fun a => if a == msg.sender then newBal else state.deposits a
    totalDeposited := state.totalDeposited + amount
  }

/-- Withdraw from vault -/
def vaultWithdraw (state : VaultState) (msg : MsgContext) (amount : Nat) :
    ExecResult VaultState := do
  require (amount > 0) "Vault: zero withdrawal"
  let userBal := state.deposits msg.sender
  require (userBal >= amount) "Vault: insufficient balance"
  pure {
    deposits := fun a => if a == msg.sender then userBal - amount else state.deposits a
    totalDeposited := state.totalDeposited - amount
  }

/-- Zero deposit reverts -/
theorem vault_zero_deposit_reverts (state : VaultState) (msg : MsgContext) :
    ∃ m, vaultDeposit state msg 0 = ExecResult.revert m := by
  refine ⟨"Vault: zero deposit", ?_⟩
  unfold vaultDeposit require
  simp only [bind, pure, ExecResult.bind, Nat.lt_irrefl]
  rfl

/-- Insufficient balance reverts -/
theorem vault_insufficient_balance_reverts
    (state : VaultState) (msg : MsgContext) (amount : Nat)
    (h_pos : amount > 0)
    (h_insufficient : state.deposits msg.sender < amount) :
    ∃ m, vaultWithdraw state msg amount = ExecResult.revert m := by
  refine ⟨"Vault: insufficient balance", ?_⟩
  unfold vaultWithdraw require
  simp only [bind, pure, ExecResult.bind]
  have h1 : decide (amount > 0) = true := by simp only [decide_eq_true_eq]; exact h_pos
  have h2 : decide (state.deposits msg.sender >= amount) = false := by
    simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]
    exact h_insufficient
  simp only [h1, h2]
  rfl

/-! ### Deposit Invariant -/

/-- Deposit increases user balance and total by same amount -/
theorem deposit_preserves_invariant_local
    (state state' : VaultState) (msg : MsgContext) (amount : Nat)
    (h_success : vaultDeposit state msg amount = ExecResult.success state') :
    state'.deposits msg.sender = state.deposits msg.sender + amount ∧
    state'.totalDeposited = state.totalDeposited + amount := by
  unfold vaultDeposit require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  cases h_success
  constructor
  · simp only [beq_self_eq_true, ite_true]
  · rfl

/-! ### Withdraw Invariant -/

/-- Withdraw decreases user balance and total by same amount -/
theorem withdraw_preserves_invariant_local
    (state state' : VaultState) (msg : MsgContext) (amount : Nat)
    (h_success : vaultWithdraw state msg amount = ExecResult.success state') :
    state'.deposits msg.sender = state.deposits msg.sender - amount ∧
    state'.totalDeposited = state.totalDeposited - amount := by
  unfold vaultWithdraw require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  cases h_success
  constructor
  · simp only [beq_self_eq_true, ite_true]
  · rfl

end LeanEVM.Properties
