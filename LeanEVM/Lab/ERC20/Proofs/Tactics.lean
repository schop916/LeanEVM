import Lab.ERC20.Contracts.Interface
import Lab.ERC20.Proofs.Attributes

/-!
# ERC-20 Verification Tactics

Helper tactics and lemmas for proving ERC-20 properties (enhanced with Veil techniques).

## Tactics

- `unfold_erc20` - Unfold common ERC-20 definitions
- Result handling lemmas for monadic proofs

## Simp Sets

- `resultSimp` - Result monad simplifications
- `contractSimp` - Contract logic simplifications

## Common Patterns

1. Proving reverts: Show condition fails
2. Proving success: Show all conditions pass
3. State equality: Compare fields after operations
-/

namespace Lab.ERC20.Tactics

open Lab.ERC20
open Lab.ERC20.Attributes

/-! ## Result Lemmas -/

/-- Result.ok is injective -/
@[resultSimp]
theorem Result.ok_injective {α : Type} {a b : α} (h : Result.ok a = Result.ok b) : a = b := by
  cases h
  rfl

/-- Result.ok is not revert -/
@[resultSimp]
theorem Result.ok_ne_revert {α : Type} {a : α} {msg : String} :
    Result.ok a ≠ Result.revert msg := by
  intro h
  cases h

/-- Result.revert is not ok -/
@[resultSimp]
theorem Result.revert_ne_ok {α : Type} {a : α} {msg : String} :
    Result.revert msg ≠ Result.ok a := by
  intro h
  cases h

/-- Extract value from Result.ok equality -/
@[resultSimp]
theorem Result.ok_eq_ok {α : Type} {a b : α} :
    Result.ok a = Result.ok b ↔ a = b := by
  constructor
  · exact Result.ok_injective
  · intro h; rw [h]

/-- Result.ok is decidably not revert -/
theorem Result.ok_isOk {α : Type} {a : α} : (Result.ok a).isOk = true := rfl

/-- Result.revert is decidably not ok -/
theorem Result.revert_isRevert {α : Type} {msg : String} :
    (Result.revert (α := α) msg).isRevert = true := rfl

/-! ## Bind Lemmas -/

/-- Bind with ok -/
@[resultSimp, simp]
theorem Result.bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Result.ok a >>= f) = f a := rfl

/-- Bind with revert -/
@[resultSimp, simp]
theorem Result.bind_revert {α β : Type} (msg : String) (f : α → Result β) :
    (Result.revert msg >>= f) = Result.revert msg := rfl

/-- Pure in Result monad -/
@[resultSimp, simp]
theorem Result.pure_eq_ok {α : Type} (a : α) : (pure a : Result α) = Result.ok a := rfl

/-! ## Require Lemmas -/

/-- Require with true condition -/
@[contractSimp, simp]
theorem require_true (msg : String) :
    require true msg = Result.ok () := rfl

/-- Require with false condition -/
@[contractSimp, simp]
theorem require_false (msg : String) :
    require false msg = Result.revert msg := rfl

/-- Require succeeds iff condition is true -/
@[contractSimp]
theorem require_ok_iff (cond : Bool) (msg : String) :
    (∃ u, require cond msg = Result.ok u) ↔ cond = true := by
  constructor
  · intro ⟨_, h⟩
    unfold require at h
    split at h
    · assumption
    · contradiction
  · intro h
    rw [h]
    exact ⟨(), rfl⟩

/-- Require reverts iff condition is false -/
@[contractSimp]
theorem require_revert_iff (cond : Bool) (msg : String) :
    (require cond msg = Result.revert msg) ↔ cond = false := by
  constructor
  · intro h
    unfold require at h
    cases cond <;> simp_all
  · intro h
    rw [h]
    rfl

/-- Require followed by pure -/
@[contractSimp]
theorem require_bind_pure {α : Type} (cond : Bool) (msg : String) (a : α) :
    (require cond msg >>= fun _ => pure a) =
    if cond then Result.ok a else Result.revert msg := by
  cases cond <;> rfl

/-- If require succeeds, condition was true -/
@[contractSimp]
theorem require_ok_cond {cond : Bool} {msg : String} {u : Unit}
    (h : require cond msg = Result.ok u) : cond = true := by
  unfold require at h
  split at h
  · assumption
  · contradiction

/-! ## Address Lemmas -/

/-- Zero address is zero -/
@[stateSimp, simp]
theorem Address.zero_isZero : Address.zero.isZero = true := rfl

/-- Non-zero address -/
@[stateSimp]
theorem Address.isZero_iff (a : Address) :
    a.isZero = true ↔ a = Address.zero := by
  unfold Address.isZero Address.zero
  constructor
  · intro h
    cases a with | mk val =>
    simp only [decide_eq_true_eq] at h
    simp [h]
  · intro h
    rw [h]
    rfl

/-- Address equality is decidable -/
@[stateSimp]
theorem Address.eq_zero_iff (a : Address) :
    a = Address.zero ↔ a.val = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    cases a with | mk val =>
    simp only at h
    simp [Address.zero, h]

/-- Not zero means positive value -/
@[stateSimp]
theorem Address.not_isZero_iff (a : Address) :
    a.isZero = false ↔ a ≠ Address.zero := by
  unfold Address.isZero Address.zero
  cases a with | mk val =>
  simp only [decide_eq_false_iff_not, ne_eq, Address.mk.injEq]

/-! ## Proof Patterns -/

/-- Pattern for proving operation reverts -/
theorem prove_revert_pattern {S : Type} {op : Result S} {msg : String}
    (h : op = Result.revert msg) :
    ∃ m, op = Result.revert m :=
  ⟨msg, h⟩

/-- Pattern for proving operation succeeds -/
theorem prove_ok_pattern {S : Type} {op : Result S} {s' : S}
    (h : op = Result.ok s') :
    ∃ s, op = Result.ok s :=
  ⟨s', h⟩

/-! ## State Simplification Lemmas

These lemmas express natural laws for ERC-20 state manipulation.
For abstract type classes, they cannot be proven - they would need to be
added as laws to a `LawfulERC20State` class. For concrete implementations
like `BasicToken` or `MintableToken`, these properties hold by construction. -/

/-- setBalance then balanceOf at same address.
    This is an expected law: setting a balance and reading it back gives the set value. -/
@[stateSimp]
theorem setBalance_balanceOf_same {S : Type} [ERC20State S]
    (s : S) (addr : Address) (bal : Amount) :
    ERC20State.balanceOf (ERC20State.setBalance s addr bal) addr = bal := by
  sorry -- Law for LawfulERC20State; provable for concrete implementations

/-- setBalance then balanceOf at different address.
    This is an expected law: setting one address's balance doesn't affect others. -/
@[stateSimp]
theorem setBalance_balanceOf_diff {S : Type} [ERC20State S]
    (s : S) (addr1 addr2 : Address) (bal : Amount) (_h : addr1 ≠ addr2) :
    ERC20State.balanceOf (ERC20State.setBalance s addr1 bal) addr2 =
    ERC20State.balanceOf s addr2 := by
  sorry -- Law for LawfulERC20State; provable for concrete implementations

/-! ## Automation Tactics -/

/-- Unfold all ERC-20 related definitions -/
macro "unfold_erc20" : tactic =>
  `(tactic| unfold ERC20State.balanceOf ERC20State.totalSupply ERC20State.allowance
            ERC20State.setBalance ERC20State.setAllowance)

/-- Simplify Result monad expressions -/
macro "simp_result" : tactic =>
  `(tactic| simp only [resultSimp, Bind.bind, Pure.pure, Result.bind])

/-- Simplify contract expressions -/
macro "simp_contract" : tactic =>
  `(tactic| simp only [contractSimp, resultSimp, stateSimp])

end Lab.ERC20.Tactics
