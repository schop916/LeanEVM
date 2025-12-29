import Mathlib.Tactic

/-!
# Verification Attributes

Simp attributes for organized proof automation (inspired by Veil).

## Attribute Categories

- `contractSimp` - Contract logic simplifications
- `resultSimp` - Result monad simplifications
- `stateSimp` - State accessor simplifications
- `balanceSimp` - Balance-related simplifications

## Usage

```lean
-- Register a lemma
@[contractSimp] theorem my_lemma : ... := ...

-- Use in proofs
simp only [contractSimp]
```
-/

namespace Lab.ERC20.Attributes

/-! ## Simp Attribute Registration -/

/-- Simplifications for contract logic (require, guards, etc.) -/
register_simp_attr contractSimp

/-- Simplifications for Result monad operations -/
register_simp_attr resultSimp

/-- Simplifications for state accessors (balanceOf, allowance, etc.) -/
register_simp_attr stateSimp

/-- Simplifications for balance arithmetic -/
register_simp_attr balanceSimp

/-- All contract-related simplifications combined -/
register_simp_attr erc20Simp

end Lab.ERC20.Attributes
