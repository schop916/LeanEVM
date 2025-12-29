import LeanEVM.Core.Types
import LeanEVM.Core.Execution

/-!
# ERC-20 Token Contract Model

This module models the ERC-20 token standard in Lean 4.
We define the contract state, functions, and verifiable properties.
-/

namespace LeanEVM.Contracts

open LeanEVM

/-! ## Token State -/

/-- ERC-20 Token State -/
structure TokenState where
  /-- Token balances: owner → balance -/
  balances : Address → Nat
  /-- Allowances: owner → spender → amount -/
  allowances : Address → Address → Nat
  /-- Total supply (should be constant) -/
  totalSupply : Nat

namespace TokenState

/-- Create initial state with all tokens to deployer -/
def init (deployer : Address) (supply : Nat) : TokenState :=
  { balances := fun addr => if addr == deployer then supply else 0
  , allowances := fun _ _ => 0
  , totalSupply := supply }

/-- Get balance of an address -/
def balanceOf (state : TokenState) (owner : Address) : Nat :=
  state.balances owner

/-- Get allowance -/
def allowance (state : TokenState) (owner spender : Address) : Nat :=
  state.allowances owner spender

/-- Update balance -/
def setBalance (state : TokenState) (addr : Address) (bal : Nat) : TokenState :=
  { state with balances := fun a => if a == addr then bal else state.balances a }

/-- Update allowance -/
def setAllowance (state : TokenState) (owner spender : Address) (amount : Nat) : TokenState :=
  { state with allowances := fun o s =>
      if o == owner && s == spender then amount
      else state.allowances o s }

end TokenState

/-! ## Token Operations -/

/-- Transfer tokens from msg.sender to recipient -/
def transfer (state : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat) :
    ExecResult TokenState := do
  -- Check: cannot transfer to zero address
  require (!to_.isZero) "ERC20: transfer to zero address"
  -- Check: sender has sufficient balance
  let senderBal := state.balanceOf msg.sender
  require (senderBal >= amount) "ERC20: transfer amount exceeds balance"
  -- Effect: update balances
  let state' := state.setBalance msg.sender (senderBal - amount)
  let receiverBal := state'.balanceOf to_
  let state'' := state'.setBalance to_ (receiverBal + amount)
  pure state''

/-- Approve spender to spend tokens -/
def approve (state : TokenState) (msg : MsgContext) (spender : Address) (amount : Nat) :
    ExecResult TokenState := do
  -- Check: cannot approve zero address
  require (!spender.isZero) "ERC20: approve to zero address"
  -- Effect: set allowance
  pure (state.setAllowance msg.sender spender amount)

/-- Transfer tokens on behalf of owner (using allowance) -/
def transferFrom (state : TokenState) (msg : MsgContext)
    (from_ to_ : Address) (amount : Nat) : ExecResult TokenState := do
  -- Check: cannot transfer to zero address
  require (!to_.isZero) "ERC20: transfer to zero address"
  -- Check: sender has sufficient allowance
  let currentAllowance := state.allowance from_ msg.sender
  require (currentAllowance >= amount) "ERC20: insufficient allowance"
  -- Check: from has sufficient balance
  let fromBal := state.balanceOf from_
  require (fromBal >= amount) "ERC20: transfer amount exceeds balance"
  -- Effect: decrease allowance
  let state' := state.setAllowance from_ msg.sender (currentAllowance - amount)
  -- Effect: update balances
  let state'' := state'.setBalance from_ (fromBal - amount)
  let toBal := state''.balanceOf to_
  let state''' := state''.setBalance to_ (toBal + amount)
  pure state'''

/-! ## Verified Properties -/

section Properties

/-! ### Property 1: Transfer Conservation -/

/-- Transfer doesn't change total supply field -/
theorem transfer_preserves_totalSupply
    (state state' : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat)
    (h_success : transfer state msg to_ amount = ExecResult.success state') :
    state.totalSupply = state'.totalSupply := by
  unfold transfer require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all [TokenState.setBalance]
  split at h_success <;> try simp_all [TokenState.setBalance]
  · cases h_success
    rfl

/-! ### Property 2: Zero Address Safety -/

/-- Transfer to zero address reverts -/
theorem transfer_to_zero_reverts
    (state : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat)
    (h_zero : to_.isZero = true) :
    ∃ m, transfer state msg to_ amount = ExecResult.revert m := by
  refine ⟨"ERC20: transfer to zero address", ?_⟩
  unfold transfer require
  simp only [bind, pure, ExecResult.bind, h_zero, Bool.not_true]
  rfl

/-! ### Property 3: Insufficient Balance Reverts -/

/-- Transfer reverts if sender has insufficient balance -/
theorem transfer_insufficient_balance_reverts
    (state : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat)
    (h_not_zero : to_.isZero = false)
    (h_insufficient : state.balanceOf msg.sender < amount) :
    ∃ m, transfer state msg to_ amount = ExecResult.revert m := by
  refine ⟨"ERC20: transfer amount exceeds balance", ?_⟩
  unfold transfer require
  simp only [bind, pure, ExecResult.bind, h_not_zero, Bool.not_false]
  have h : decide (state.balanceOf msg.sender >= amount) = false := by
    simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]
    exact h_insufficient
  simp only [h]
  rfl

/-! ### Property 4: Allowance Reverts -/

/-- TransferFrom reverts if insufficient allowance -/
theorem transferFrom_insufficient_allowance_reverts
    (state : TokenState) (msg : MsgContext) (from_ to_ : Address) (amount : Nat)
    (h_not_zero : to_.isZero = false)
    (h_insufficient : state.allowance from_ msg.sender < amount) :
    ∃ m, transferFrom state msg from_ to_ amount = ExecResult.revert m := by
  refine ⟨"ERC20: insufficient allowance", ?_⟩
  unfold transferFrom require
  simp only [bind, pure, ExecResult.bind, h_not_zero, Bool.not_false]
  have h : decide (state.allowance from_ msg.sender >= amount) = false := by
    simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]
    exact h_insufficient
  simp only [h]
  rfl

/-! ### Property 5: Transfer Decreases Sender Balance -/

/-- Successful transfer decreases sender balance by amount (when sender ≠ receiver) -/
theorem transfer_decreases_sender
    (state state' : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat)
    (h_neq : msg.sender ≠ to_)
    (h_success : transfer state msg to_ amount = ExecResult.success state') :
    state'.balanceOf msg.sender = state.balanceOf msg.sender - amount := by
  unfold transfer require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  cases h_success
  simp only [TokenState.balanceOf, TokenState.setBalance, beq_self_eq_true, ite_true]
  have h : (msg.sender == to_) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, h_neq, not_false_eq_true]
  simp only [h]
  rfl

/-! ### Property 6: Transfer Increases Receiver Balance (when different from sender) -/

/-- Successful transfer increases receiver balance by amount (when sender ≠ receiver) -/
theorem transfer_increases_receiver
    (state state' : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat)
    (h_neq : msg.sender ≠ to_)
    (h_success : transfer state msg to_ amount = ExecResult.success state') :
    state'.balanceOf to_ = state.balanceOf to_ + amount := by
  unfold transfer require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  cases h_success
  simp only [TokenState.balanceOf, TokenState.setBalance, beq_self_eq_true, ite_true]
  have h : (to_ == msg.sender) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Ne.symm h_neq, not_false_eq_true]
  simp only [h]
  rfl

/-! ### Property 7: Transfer Conserves Local Balance -/

/-- Transfer conserves sum of sender and receiver balances (when different) -/
theorem transfer_conserves_local_balance
    (state state' : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat)
    (h_neq : msg.sender ≠ to_)
    (h_success : transfer state msg to_ amount = ExecResult.success state') :
    state.balanceOf msg.sender + state.balanceOf to_ =
    state'.balanceOf msg.sender + state'.balanceOf to_ := by
  -- Use the individual change theorems
  have h_sender := transfer_decreases_sender state state' msg to_ amount h_neq h_success
  have h_receiver := transfer_increases_receiver state state' msg to_ amount h_neq h_success
  rw [h_sender, h_receiver]
  -- Extract balance condition from success
  unfold transfer require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  rename_i h_bal
  -- Now we have h_bal : state.balanceOf msg.sender >= amount
  omega

/-! ### Property 8: Approve Sets Allowance -/

/-- Successful approve sets exact allowance -/
theorem approve_sets_allowance
    (state state' : TokenState) (msg : MsgContext) (spender : Address) (amount : Nat)
    (h_success : approve state msg spender amount = ExecResult.success state') :
    state'.allowance msg.sender spender = amount := by
  unfold approve require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  cases h_success
  simp only [TokenState.allowance, TokenState.setAllowance, beq_self_eq_true, Bool.and_self,
             ite_true]

/-! ### Property 9: TransferFrom Decreases Allowance -/

/-- Successful transferFrom decreases allowance by amount -/
theorem transferFrom_decreases_allowance
    (state state' : TokenState) (msg : MsgContext) (from_ to_ : Address) (amount : Nat)
    (h_success : transferFrom state msg from_ to_ amount = ExecResult.success state') :
    state'.allowance from_ msg.sender = state.allowance from_ msg.sender - amount := by
  unfold transferFrom require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  cases h_success
  simp only [TokenState.allowance, TokenState.setBalance, TokenState.setAllowance]
  simp only [beq_self_eq_true, Bool.and_self, ite_true]

end Properties

/-! ## Invariants -/

/-- The fundamental invariant: sum of balances equals total supply -/
def balancesSumToSupply (state : TokenState) (addresses : List Address) : Prop :=
  (addresses.map state.balanceOf).sum = state.totalSupply

end LeanEVM.Contracts
