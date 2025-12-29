import Lab.ERC20.Proofs.Tactics
import Lab.ERC20.Model.TransitionSystem
import Mathlib.Tactic
import Smt

/-!
# Contract Verification Automation

Custom decision procedures and tactics for verifying smart contract properties.

## Tactics

- `contract_simp` - Combined simplification for contract proofs
- `auto_arith` - Arithmetic automation (omega, linarith fallback)
- `smt_arith` - SMT-backed arithmetic (uses cvc5)

## Design

These tactics are designed to work with the ContractTransitionSystem framework,
automating common proof patterns for:
- Invariant initialization (invInit)
- Invariant preservation (invConsecution)
- Safety properties (invSafe)
-/

namespace Lab.Automation

open Lab.ERC20
open Lab.ERC20.Tactics

/-! ## SMT-Backed Automation -/

/-- SMT-backed arithmetic: uses cvc5 for complex goals -/
macro "smt_arith" : tactic =>
  `(tactic| first
    | smt
    | omega
    | nlinarith
    | decide)

/-! ## Core Arithmetic Automation -/

/-- Arithmetic automation: tries omega, then nlinarith, then decide -/
macro "auto_arith" : tactic =>
  `(tactic| first
    | omega
    | nlinarith
    | decide
    | exact Nat.zero_le _)

/-- Positivity reasoning for natural numbers -/
macro "nat_pos" : tactic =>
  `(tactic| first
    | exact Nat.zero_le _
    | omega
    | nlinarith)

/-! ## Contract-Specific Tactics -/

/-- Unfold common contract definitions and simplify -/
macro "contract_unfold" : tactic =>
  `(tactic| (
    unfold require
    simp only [Bind.bind, Pure.pure, Result.bind, Result.pure_eq_ok]
    first | split | skip))

/-- Simplify require guards -/
macro "require_simp" : tactic =>
  `(tactic| (
    simp only [require, Bind.bind, Result.bind, ite_eq_left_iff, ite_eq_right_iff]
    first | decide | omega | skip))

/-- Handle require-based reverts -/
macro "require_auto" : tactic =>
  `(tactic| (
    contract_unfold
    all_goals first | contradiction | decide | omega | skip))

/-! ## Transition System Tactics -/

/-- For invariant initialization proofs -/
macro "inv_init" : tactic =>
  `(tactic| (
    intro s h_init
    simp_all only []
    first | rfl | auto_arith | skip))

/-- For invariant safety proofs -/
macro "inv_safe" : tactic =>
  `(tactic| (
    intro s h_inv
    simp_all only []
    first | exact h_inv.1 | exact h_inv.2 | exact h_inv | skip))

/-! ## Balance Conservation Tactics -/

/-- Prove balance conservation across state transitions -/
macro "balance_conservation" : tactic =>
  `(tactic| (
    simp only [stateSimp]
    first | ring | omega | rfl))

/-- Prove supply conservation -/
macro "supply_conservation" : tactic =>
  `(tactic| (
    simp_all only [ge_iff_le]
    first | rfl | omega))

/-! ## Combined Automation -/

/-- Full contract simplification -/
macro "contract_simp" : tactic =>
  `(tactic| (
    simp only [contractSimp, resultSimp, stateSimp, Bind.bind, Pure.pure, Result.bind]
    all_goals first | split | skip
    all_goals first | contradiction | decide | omega | skip))

/-- Attempt to close goal with multiple strategies -/
macro "contract_auto" : tactic =>
  `(tactic| first
    | assumption
    | rfl
    | decide
    | omega
    | contradiction
    | simp_all)

/-! ## Revert Proof Tactics -/

/-- Prove that an operation reverts under given conditions -/
macro "prove_reverts" : tactic =>
  `(tactic| (
    refine ⟨_, ?_⟩
    contract_unfold
    all_goals first | decide | omega | simp_all))

/-! ## State Preservation Helpers -/

/-- Prove a field is preserved across state update -/
macro "field_preserved" : tactic =>
  `(tactic| first | rfl | simp_all | unfold_erc20)

/-! ## Result Monad Tactics -/

/-- Extract result from monadic computation -/
macro "result_cases" : tactic =>
  `(tactic| (
    simp only [Bind.bind, Pure.pure, Result.bind] at *
    all_goals first | split | skip
    all_goals first | contradiction | skip))

/-! ## Documentation Examples -/

section Examples

variable {S : Type} [Lab.ERC20.Model.ContractTransitionSystem S]

/-- Example: Using auto_arith for natural number goals -/
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by auto_arith

/-- Example: Using contract_auto for simple goals -/
example (p : Prop) (h : p) : p := by contract_auto

end Examples

end Lab.Automation
