import Plausible
import Lab.ERC20.Contracts.BasicToken
import Lab.ERC20.Model.TransitionSystem

/-!
# Plausible Integration for Contract Testing

Sampleable instances and property testing infrastructure for smart contracts.

## Features

- `Shrinkable` instances for contract types
- `SampleableExt` instances for random generation
- Property testing macros for invariants
- Counterexample generation for safety properties

## Usage

```lean
-- Find counterexamples to proposed properties
example : ∀ s : BasicTokenState, s.supply > 0 := by
  plausible  -- Will find counterexample: state with supply = 0
```
-/

namespace Lab.Automation.Testable

open Lab.ERC20
open Plausible

/-! ## Address Instances -/

/-- Shrink addresses to simpler values -/
instance : Shrinkable Address where
  shrink a :=
    if a.val = 0 then []
    else if a.val = 1 then [⟨0⟩]
    else [⟨0⟩, ⟨1⟩, ⟨a.val / 2⟩]

/-- Repr instance for Address -/
instance : Repr Address where
  reprPrec a _ := s!"Address({a.val})"

/-- Generate random addresses (small space for testing) -/
instance : SampleableExt Address := SampleableExt.mkSelfContained do
  let n ← Gen.choose Nat 0 999 (by omega)
  return ⟨n.val⟩

/-! ## MsgContext Instances -/

/-- Shrink message context -/
instance : Shrinkable MsgContext where
  shrink ctx := (Shrinkable.shrink ctx.sender).map fun s => { sender := s }

/-- Repr instance for MsgContext -/
instance : Repr MsgContext where
  reprPrec ctx _ := s!"MsgContext(sender: {ctx.sender.val})"

/-- Generate random message contexts -/
instance : SampleableExt MsgContext := SampleableExt.mkSelfContained do
  let addr ← Gen.choose Nat 0 999 (by omega)
  return { sender := ⟨addr.val⟩ }

/-! ## BasicTokenState Instances -/

/-- Shrink basic token state -/
instance : Shrinkable BasicTokenState where
  shrink s :=
    -- Shrink by reducing supply or simplifying balances
    if s.supply = 0 then []
    else [BasicTokenState.init ⟨0⟩ 0,
          BasicTokenState.init ⟨1⟩ (s.supply / 2),
          { s with supply := s.supply / 2 }]

/-- Repr instance for BasicTokenState -/
instance : Repr BasicTokenState where
  reprPrec s _ :=
    let bal0 := s.balances ⟨0⟩
    let bal1 := s.balances ⟨1⟩
    s!"BasicTokenState(supply: {s.supply}, bal[0]: {bal0}, bal[1]: {bal1})"

/-- Generate random basic token states -/
instance : SampleableExt BasicTokenState := SampleableExt.mkSelfContained do
  let supply ← Gen.choose Nat 0 1000000 (by omega)
  let deployer ← Gen.choose Nat 0 999 (by omega)
  return BasicTokenState.init ⟨deployer.val⟩ supply.val

/-! ## Result Instances -/

/-- Shrink Result values -/
instance {α : Type} [Shrinkable α] : Shrinkable (Result α) where
  shrink r := match r with
    | Result.ok a => (Shrinkable.shrink a).map Result.ok
    | Result.revert _ => []

/-- Repr instance for Result -/
instance {α : Type} [Repr α] : Repr (Result α) where
  reprPrec r _ := match r with
    | Result.ok a => s!"ok({repr a})"
    | Result.revert msg => s!"revert(\"{msg}\")"

/-! ## Property Testing Helpers -/

/-- Find counterexamples to invariants -/
macro "find_counterexample" : tactic =>
  `(tactic| plausible)

/-- Property test with custom configuration -/
macro "property_test" n:num : tactic =>
  `(tactic| plausible (config := { numInst := $n }))

/-! ## Example Properties -/

section Examples

open BasicToken

/-- Example: Supply is non-negative (trivially true for Nat) -/
example : ∀ (s : BasicTokenState), s.supply ≥ 0 := by
  intro s
  exact Nat.zero_le _

/-- Example: Initial state has correct supply -/
example : ∀ (addr : Address) (supply : Amount),
    (BasicTokenState.init addr supply).supply = supply := by
  intros
  rfl

end Examples

end Lab.Automation.Testable
