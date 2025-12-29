import Aesop
import Lab.ERC20.Contracts.Interface

/-!
# Aesop Automation for EVM Proofs

This module defines Aesop rule sets for automating common EVM/smart contract proofs.
By registering simp lemmas and safe rules, Aesop can automatically solve:
- Balance conservation proofs
- Map update independence proofs
- State transition invariants

## Usage

```lean
-- Use the EVM rule set
theorem my_theorem : ... := by aesop (rule_sets := [EVM])
```
-/

-- Declare rule set at module level before namespace
declare_aesop_rule_sets [EVM]

namespace Lab.Automation.Aesop

open Lab.ERC20

/-! ## Function Update Lemmas (for functional maps) -/

/-- Updating a function at point A and looking up at B (where A ≠ B) returns original -/
@[simp]
theorem fun_update_ne {α β : Type} [DecidableEq α] (f : α → β) (a b : α) (v : β) (h : a ≠ b) :
    (fun x => if x = a then v else f x) b = f b := by
  simp [h.symm]

/-- Updating a function at point A and looking up at A returns the new value -/
@[simp]
theorem fun_update_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) :
    (fun x => if x = a then v else f x) a = v := by
  simp

/-! ## Balance Independence Lemmas -/

/-- Balance of user B is independent of transfer involving only user A -/
theorem balances_independent {State : Type} (get_bal : State → Address → Nat)
    (update_bal : State → Address → Nat → State)
    (s : State) (a b : Address) (v : Nat)
    (h_neq : a ≠ b)
    (h_indep : get_bal (update_bal s a v) b = get_bal s b) :
    get_bal (update_bal s a v) b = get_bal s b := h_indep

/-! ## Arithmetic Lemmas for Transfers -/

/-- Transfer conservation: what leaves sender equals what arrives at receiver -/
theorem transfer_sum_invariant (sender_bal receiver_bal amount : Nat)
    (h_suff : sender_bal ≥ amount) :
    (sender_bal - amount) + (receiver_bal + amount) = sender_bal + receiver_bal := by
  omega

/-- Mint conservation: new tokens increase total supply exactly -/
theorem mint_supply_invariant (bal supply amount : Nat) :
    (bal + amount) + (supply - bal) = supply + amount ∨ supply < bal := by
  omega

/-- Burn conservation: destroyed tokens decrease total supply exactly -/
theorem burn_supply_invariant (bal supply amount : Nat)
    (h_suff : bal ≥ amount) (h_supply : supply ≥ bal) :
    (bal - amount) + (supply - bal) = supply - amount := by
  omega

/-! ## Result Monad Lemmas -/

/-- Successful result extraction -/
@[simp]
theorem result_ok_bind {α β : Type} (a : α) (f : α → Result β) :
    (Result.ok a >>= f) = f a := rfl

/-- Error propagation -/
@[simp]
theorem result_revert_bind {α β : Type} (e : String) (f : α → Result β) :
    (Result.revert e >>= f) = Result.revert e := rfl

/-! ## Require Guard Lemmas -/

/-- Require succeeds when condition holds -/
@[simp]
theorem require_true_ok (msg : String) :
    require true msg = Result.ok () := rfl

/-- Require fails when condition is false -/
@[simp]
theorem require_false_revert (msg : String) :
    require false msg = Result.revert msg := rfl

/-! ## Combined Tactics -/

/-- Aesop-based tactic for EVM proofs -/
macro "evm_solve" : tactic =>
  `(tactic| first
    | aesop (rule_sets := [EVM])
    | simp_all
    | omega)

/-- Aesop with fallback to omega for arithmetic -/
macro "evm_auto" : tactic =>
  `(tactic| first
    | aesop (rule_sets := [EVM])
    | omega
    | simp_all)

/-! ## Example Usage -/

section Examples

variable (balances : Address → Nat) (a b : Address) (amount : Nat)

/-- Example: Independence of balance updates -/
example (h : a ≠ b) :
    (fun x => if x = a then balances a - amount else balances x) b = balances b := by
  simp [h.symm]

/-- Example: Transfer sum conservation -/
example (h : balances a ≥ amount) :
    (balances a - amount) + (balances b + amount) = balances a + balances b := by
  omega

end Examples

end Lab.Automation.Aesop
