import Lab.ERC20.Contracts.BasicToken
import Lab.ERC20.Model.TransitionSystem
import Lab.ERC20.Model.LawfulOp

/-!
# Transition System Example

Demonstrates modeling BasicToken as a ContractTransitionSystem (Veil pattern).

## What This Shows

1. Define a contract as a transition system
2. Specify safety properties
3. Define inductive invariants
4. Prove invariant properties
-/

namespace Lab.ERC20.Examples.TransitionSystem

open Lab.ERC20
open Lab.ERC20.Model

/-! ## Step 1: Define Predicates -/

/-- A token initialized with exactly 1 million supply -/
def MillionTokenInit (s : BasicTokenState) : Prop :=
  ∃ deployer, s = BasicTokenState.init deployer 1000000

/-- Transition relation: any successful operation -/
def MillionTokenNext (s s' : BasicTokenState) : Prop :=
  (∃ msg recipient amount, BasicToken.transfer s msg recipient amount = Result.ok s') ∨
  (∃ msg spender amount, BasicToken.approve s msg spender amount = Result.ok s') ∨
  (∃ msg fromAddr recipient amount, BasicToken.transferFrom s msg fromAddr recipient amount = Result.ok s')

/-- Safety: supply is always 1 million -/
def MillionTokenSafe (s : BasicTokenState) : Prop :=
  s.supply = 1000000

/-- Invariant: supply equals 1 million -/
def MillionTokenInv (s : BasicTokenState) : Prop :=
  s.supply = 1000000

/-! ## Step 2: Define the Transition System -/

/-- Million token as a transition system -/
def millionTokenTS : ContractTransitionSystem BasicTokenState :=
  { init := MillionTokenInit
  , next := MillionTokenNext
  , safe := MillionTokenSafe
  , inv := MillionTokenInv }

/-! ## Step 3: Prove the Invariant is Inductive -/

/-- Initial states satisfy the invariant -/
theorem million_invInit : ContractTransitionSystem.invInit' millionTokenTS := by
  intro s h_init
  obtain ⟨deployer, h_eq⟩ := h_init
  simp only [millionTokenTS, MillionTokenInv]
  rw [h_eq]
  rfl

/-- Invariant implies safety -/
theorem million_invSafe : ContractTransitionSystem.invSafe' millionTokenTS := by
  intro s h_inv
  exact h_inv

/-- Transitions preserve the invariant -/
theorem million_invConsecution : ContractTransitionSystem.invConsecution' millionTokenTS := by
  intro s s' h_inv h_next
  show millionTokenTS.inv s'
  simp only [millionTokenTS, MillionTokenInv] at h_inv ⊢
  rcases h_next with ⟨msg, recipient, amount, h_transfer⟩ |
                     ⟨msg, spender, amount, h_approve⟩ |
                     ⟨msg, fromAddr, recipient, amount, h_transferFrom⟩
  -- Case 1: transfer preserves supply
  · have h := transfer_preserves_supply s s' msg recipient amount h_transfer
    rw [h, h_inv]
  -- Case 2: approve preserves supply
  · unfold BasicToken.approve require at h_approve
    simp only [Bind.bind, Pure.pure, Result.bind] at h_approve
    split at h_approve <;> try contradiction
    simp only [Result.ok.injEq] at h_approve
    subst h_approve
    exact h_inv
  -- Case 3: transferFrom preserves supply
  · unfold BasicToken.transferFrom require at h_transferFrom
    simp only [Bind.bind, Pure.pure, Result.bind] at h_transferFrom
    split at h_transferFrom <;> try contradiction
    split at h_transferFrom <;> try contradiction
    split at h_transferFrom <;> try contradiction
    simp only [Result.ok.injEq] at h_transferFrom
    subst h_transferFrom
    exact h_inv

/-- The invariant is inductive (all three properties hold) -/
theorem million_invInductive : ContractTransitionSystem.invInductive' millionTokenTS :=
  ⟨million_invInit, million_invConsecution, million_invSafe⟩

/-! ## Step 4: Using SupplyPreserving Typeclass -/

/-- Helper: transfer as a function of state only -/
def transferOp (msg : MsgContext) (recipient : Address) (amount : Amount) :
    BasicTokenState → Result BasicTokenState :=
  fun s => BasicToken.transfer s msg recipient amount

/-- Transfer preserves supply (typeclass instance) -/
instance transferSupplyPreserving (msg : MsgContext) (recipient : Address) (amount : Amount) :
    SupplyPreserving (transferOp msg recipient amount) where
  preserves := fun s s' h => (transfer_preserves_supply s s' msg recipient amount h).symm

/-! ## Summary

This example demonstrates the Veil pattern:

1. **Define** `ContractTransitionSystem` with init/next/safe/inv
2. **Prove** `invInit` - initial states satisfy invariant
3. **Prove** `invConsecution` - transitions preserve invariant
4. **Prove** `invSafe` - invariant implies safety
5. **Combine** into `invInductive` - the invariant is inductive

With an inductive invariant, we know all reachable states are safe!
-/

end Lab.ERC20.Examples.TransitionSystem
