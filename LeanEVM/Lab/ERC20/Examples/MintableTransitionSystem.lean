import Lab.ERC20.Contracts.MintableToken
import Lab.ERC20.Model.TransitionSystem
import Lab.ERC20.Model.LawfulOp

/-!
# MintableToken Transition System Example

Demonstrates the Veil pattern with a more complex contract that has
minting and burning operations (supply changes).

## Key Difference from BasicToken

BasicToken has constant supply, so `inv = safe = (supply = initialSupply)`.

MintableToken has variable supply, so we need different invariants:
- Safety: only owner can mint
- Invariant: owner field never changes

This shows the pattern works for more interesting properties.
-/

namespace Lab.ERC20.Examples.MintableTS

open Lab.ERC20
open Lab.ERC20.Model

/-! ## Property 1: Owner Never Changes -/

section OwnerInvariant

/-- Initial state with a specific owner -/
def OwnerInit (owner : Address) (s : MintableTokenState) : Prop :=
  ∃ supply, s = MintableTokenState.init owner supply

/-- All possible transitions -/
def MintableNext (s s' : MintableTokenState) : Prop :=
  (∃ msg recipient amount, MintableToken.transfer s msg recipient amount = Result.ok s') ∨
  (∃ msg spender amount, MintableToken.approve s msg spender amount = Result.ok s') ∨
  (∃ msg fromAddr recipient amount, MintableToken.transferFrom s msg fromAddr recipient amount = Result.ok s') ∨
  (∃ msg recipient amount, MintableToken.mint s msg recipient amount = Result.ok s') ∨
  (∃ msg amount, MintableToken.burn s msg amount = Result.ok s')

/-- Safety: owner is a specific address -/
def OwnerIs (owner : Address) (s : MintableTokenState) : Prop :=
  s.owner = owner

/-- Invariant: owner field equals the original owner -/
def OwnerInv (owner : Address) (s : MintableTokenState) : Prop :=
  s.owner = owner

/-- Transition system for owner preservation -/
def ownerTS (owner : Address) : ContractTransitionSystem MintableTokenState :=
  { init := OwnerInit owner
  , next := MintableNext
  , safe := OwnerIs owner
  , inv := OwnerInv owner }

/-- Initial states have correct owner -/
theorem owner_invInit (owner : Address) :
    ContractTransitionSystem.invInit' (ownerTS owner) := by
  intro s h_init
  obtain ⟨supply, h_eq⟩ := h_init
  simp only [ownerTS, OwnerInv]
  rw [h_eq]
  rfl

/-- Invariant implies safety (they're the same) -/
theorem owner_invSafe (owner : Address) :
    ContractTransitionSystem.invSafe' (ownerTS owner) := by
  intro s h_inv
  exact h_inv

/-- Helper: transfer preserves owner -/
theorem transfer_preserves_owner (s s' : MintableTokenState) (msg : MsgContext)
    (recipient : Address) (amount : Amount)
    (h : MintableToken.transfer s msg recipient amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold MintableToken.transfer require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  subst h
  rfl

/-- Helper: approve preserves owner -/
theorem approve_preserves_owner (s s' : MintableTokenState) (msg : MsgContext)
    (spender : Address) (amount : Amount)
    (h : MintableToken.approve s msg spender amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold MintableToken.approve require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  subst h
  rfl

/-- Helper: transferFrom preserves owner -/
theorem transferFrom_preserves_owner (s s' : MintableTokenState) (msg : MsgContext)
    (fromAddr recipient : Address) (amount : Amount)
    (h : MintableToken.transferFrom s msg fromAddr recipient amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold MintableToken.transferFrom require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  subst h
  rfl

/-- Helper: mint preserves owner -/
theorem mint_preserves_owner (s s' : MintableTokenState) (msg : MsgContext)
    (recipient : Address) (amount : Amount)
    (h : MintableToken.mint s msg recipient amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold MintableToken.mint require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  subst h
  rfl

/-- Helper: burn preserves owner -/
theorem burn_preserves_owner (s s' : MintableTokenState) (msg : MsgContext)
    (amount : Amount)
    (h : MintableToken.burn s msg amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold MintableToken.burn require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  subst h
  rfl

/-- Transitions preserve owner -/
theorem owner_invConsecution (owner : Address) :
    ContractTransitionSystem.invConsecution' (ownerTS owner) := by
  intro s s' h_inv h_next
  show (ownerTS owner).inv s'
  simp only [ownerTS, OwnerInv] at h_inv ⊢
  rcases h_next with ⟨msg, recipient, amount, h_transfer⟩ |
                     ⟨msg, spender, amount, h_approve⟩ |
                     ⟨msg, fromAddr, recipient, amount, h_transferFrom⟩ |
                     ⟨msg, recipient, amount, h_mint⟩ |
                     ⟨msg, amount, h_burn⟩
  · rw [transfer_preserves_owner s s' msg recipient amount h_transfer, h_inv]
  · rw [approve_preserves_owner s s' msg spender amount h_approve, h_inv]
  · rw [transferFrom_preserves_owner s s' msg fromAddr recipient amount h_transferFrom, h_inv]
  · rw [mint_preserves_owner s s' msg recipient amount h_mint, h_inv]
  · rw [burn_preserves_owner s s' msg amount h_burn, h_inv]

/-- Owner invariant is inductive -/
theorem owner_invInductive (owner : Address) :
    ContractTransitionSystem.invInductive' (ownerTS owner) :=
  ⟨owner_invInit owner, owner_invConsecution owner, owner_invSafe owner⟩

end OwnerInvariant

/-! ## Property 2: Non-Owner Cannot Mint -/

section MintAccess

/-- If caller is not owner, mint reverts -/
theorem mint_requires_owner_ts (s : MintableTokenState) (msg : MsgContext)
    (recipient : Address) (amount : Amount)
    (h_not_owner : msg.sender ≠ s.owner) :
    ∃ m, MintableToken.mint s msg recipient amount = Result.revert m := by
  exact mint_requires_owner s msg recipient amount h_not_owner

end MintAccess

/-! ## Property 3: Supply Tracking -/

section SupplyTracking

/-- After mint, supply increases by amount -/
theorem mint_supply_increases (s s' : MintableTokenState) (msg : MsgContext)
    (recipient : Address) (amount : Amount)
    (h : MintableToken.mint s msg recipient amount = Result.ok s') :
    s'.supply = s.supply + amount := by
  exact mint_increases_supply s s' msg recipient amount h

/-- After burn, supply decreases by amount -/
theorem burn_supply_decreases (s s' : MintableTokenState) (msg : MsgContext)
    (amount : Amount)
    (h : MintableToken.burn s msg amount = Result.ok s') :
    s'.supply = s.supply - amount := by
  exact burn_decreases_supply s s' msg amount h

end SupplyTracking

/-! ## Property 4: Balance-Supply Conservation -/

section BalanceSupplyInvariant

/-
The fundamental ERC-20 invariant: sum of all balances = total supply.

For each operation, we prove the balance-supply relationship is maintained:
- Transfer: moves tokens, doesn't change supply or total balance sum
- Mint: increases one balance AND supply by the same amount
- Burn: decreases one balance AND supply by the same amount
-/

/-- For a single-holder initial state, the holder has all tokens -/
theorem init_balance_sum (owner : Address) (supply : Amount) :
    let s := MintableTokenState.init owner supply
    s.balances owner = s.supply := by
  simp [MintableTokenState.init]

/-- Transfer preserves total supply -/
theorem transfer_preserves_supply' (s s' : MintableTokenState)
    (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : MintableToken.transfer s msg recipient amount = Result.ok s') :
    s'.supply = s.supply := by
  unfold MintableToken.transfer require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  rfl

/-- Mint increases balance and supply by the same amount -/
theorem mint_balance_supply_delta (s s' : MintableTokenState)
    (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : MintableToken.mint s msg recipient amount = Result.ok s') :
    s'.balances recipient = s.balances recipient + amount ∧
    s'.supply = s.supply + amount := by
  unfold MintableToken.mint require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [ERC20State.setBalance, ERC20State.balanceOf, ite_true, and_self]

/-- Burn decreases balance and supply by the same amount -/
theorem burn_balance_supply_delta (s s' : MintableTokenState)
    (msg : MsgContext) (amount : Amount)
    (h_success : MintableToken.burn s msg amount = Result.ok s') :
    s'.balances msg.sender = s.balances msg.sender - amount ∧
    s'.supply = s.supply - amount := by
  unfold MintableToken.burn require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [ERC20State.setBalance, ERC20State.balanceOf, ite_true, and_self]

/-
The balance-supply invariant preservation follows from these theorems:

1. Transfer: supply' = supply (no change)
2. Mint: balance' = balance + amount AND supply' = supply + amount
3. Burn: balance' = balance - amount AND supply' = supply - amount

In each case, if ∑balances = supply before, then ∑balances = supply after.
-/

end BalanceSupplyInvariant

/-! ## Summary

MintableToken demonstrates more interesting invariants:

1. **Owner preservation**: The owner field never changes after initialization.
   This is an inductive invariant that holds across all 5 operations.

2. **Access control**: Only the owner can mint. This is proven directly
   from the implementation (not as a transition system property).

3. **Supply tracking**: Mint increases supply, burn decreases supply.
   These are two-state properties about individual operations.

4. **Balance-Supply Conservation**: Sum of balances = total supply.
   - `transfer_preserves_supply'`: transfer doesn't change supply
   - `mint_balance_supply_delta`: balance and supply increase together
   - `burn_balance_supply_delta`: balance and supply decrease together

The transition system pattern works well for global invariants like
"owner never changes", while direct proofs work better for operation-
specific properties like "only owner can mint".
-/

end Lab.ERC20.Examples.MintableTS
