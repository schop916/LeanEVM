import Lab.Automation.Tactics
import Lab.Automation.Testable

/-!
# Contract Verification Automation

Phase 3 automation infrastructure for LeanEVM smart contract verification.

## Components

### 1. Custom Decision Procedures (`Tactics.lean`)

Domain-specific tactics for contract verification:

- `auto_arith` - Arithmetic automation (omega, nlinarith, decide fallback)
- `contract_simp` - Combined contract simplification
- `inv_init` - Invariant initialization proofs
- `inv_safe` - Invariant safety proofs
- `require_auto` - Discharge require/guard goals
- `balance_conservation` - Balance arithmetic proofs

### 2. Counterexample Generation (`Testable.lean`)

Plausible integration for property testing:

- `Shrinkable` instances for Address, MsgContext, BasicTokenState
- `SampleableExt` instances for random generation
- `find_counterexample` tactic macro
- `property_test` with configurable test count

## Usage

```lean
import Lab.Automation

-- Use custom tactics in proofs
theorem my_invariant_holds : ... := by
  inv_init
  auto_arith

-- Find counterexamples to proposed properties
example : ∀ s : BasicTokenState, s.supply > 0 := by
  find_counterexample  -- Uses plausible
```

## SMT Integration (Future)

When upgrading to Lean 4.24+, add lean-smt for full SMT support:
```lean
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "main"
```

cvc5 is already installed at ~/.local/bin/cvc5 (v1.3.2).
-/

-- All tactics and instances are available via imports above
