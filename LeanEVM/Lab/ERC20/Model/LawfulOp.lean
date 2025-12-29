import Lab.ERC20.Model.TransitionSystem

/-!
# Lawful Operations

Typeclass for proving operations satisfy key properties (inspired by Veil's LawfulAction).

## Concept

A "lawful" operation is one that:
1. Preserves specified invariants
2. Satisfies its specification (two-state property)
3. Has deterministic behavior

## Usage

```lean
instance : LawfulOp (BasicToken.transfer state msg recipient) where
  preservesInv := transfer_preserves_inv
  satisfiesSpec := transfer_satisfies_spec
```
-/

namespace Lab.ERC20.Model

open Lab.ERC20

/-! ## Lawful Operation Class -/

/-- An operation that preserves invariants and satisfies its spec -/
class LawfulOp {S : Type} (op : S → Result S) (inv : S → Prop) (spec : TwoStateProp S) where
  /-- Operation preserves the invariant -/
  preservesInv : ∀ s s', inv s → op s = Result.ok s' → inv s'
  /-- Operation satisfies its two-state specification -/
  satisfiesSpec : ∀ s s', op s = Result.ok s' → spec s s'

/-! ## Composition of Lawful Operations -/

/-- Two lawful operations composed are lawful (if specs compose) -/
theorem lawful_compose {S : Type} {op1 op2 : S → Result S}
    {inv : S → Prop} {spec1 spec2 : TwoStateProp S}
    [h1 : LawfulOp op1 inv spec1] [h2 : LawfulOp op2 inv spec2]
    (s s' s'' : S)
    (h_op1 : op1 s = Result.ok s')
    (h_op2 : op2 s' = Result.ok s'')
    (h_inv : inv s) :
    inv s'' := by
  have h_inv' := h1.preservesInv s s' h_inv h_op1
  exact h2.preservesInv s' s'' h_inv' h_op2

/-! ## Supply-Preserving Operations -/

/-- An operation that preserves total supply -/
class SupplyPreserving {S : Type} [ERC20State S] (op : S → Result S) where
  preserves : ∀ s s', op s = Result.ok s' →
    ERC20State.totalSupply s = ERC20State.totalSupply s'

namespace SupplyPreserving

variable {S : Type} [ERC20State S] {op : S → Result S} [SupplyPreserving op]

theorem supply_unchanged (s s' : S) (h : op s = Result.ok s') :
    ERC20State.totalSupply s = ERC20State.totalSupply s' :=
  preserves s s' h

end SupplyPreserving

/-! ## Balance-Conserving Operations -/

/-- An operation that conserves balance between two addresses -/
class BalanceConserving {S : Type} [ERC20State S]
    (op : S → Result S) (sender receiver : Address) where
  conserves : ∀ s s', op s = Result.ok s' →
    ERC20State.balanceOf s sender + ERC20State.balanceOf s receiver =
    ERC20State.balanceOf s' sender + ERC20State.balanceOf s' receiver

namespace BalanceConserving

variable {S : Type} [ERC20State S] {op : S → Result S} {sender receiver : Address}
variable [BalanceConserving op sender receiver]

theorem balance_sum_unchanged (s s' : S) (h : op s = Result.ok s') :
    ERC20State.balanceOf s sender + ERC20State.balanceOf s receiver =
    ERC20State.balanceOf s' sender + ERC20State.balanceOf s' receiver :=
  conserves s s' h

end BalanceConserving

/-! ## Reverting Operations -/

/-- Characterize when an operation reverts -/
class RevertCondition {S : Type} (op : S → Result S) (cond : S → Prop) where
  /-- If condition holds, operation reverts -/
  reverts_when : ∀ s, cond s → ∃ msg, op s = Result.revert msg
  /-- If operation succeeds, condition was false -/
  succeeds_when : ∀ s s', op s = Result.ok s' → ¬cond s

namespace RevertCondition

variable {S : Type} {op : S → Result S} {cond : S → Prop} [RevertCondition op cond]

theorem must_revert (s : S) (h : cond s) : ∃ msg, op s = Result.revert msg :=
  reverts_when s h

theorem condition_false (s s' : S) (h : op s = Result.ok s') : ¬cond s :=
  succeeds_when s s' h

end RevertCondition

end Lab.ERC20.Model
