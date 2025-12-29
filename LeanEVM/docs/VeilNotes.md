# Veil Framework Analysis

Notes on the Veil framework for state transition system verification, with techniques applicable to LeanEVM.

**Source**: https://github.com/verse-lab/veil

## Overview

Veil is a foundational framework for specifying, implementing, testing, and proving safety properties of state transition systems in Lean 4. It provides:

1. **DSL for transition systems** - Embedded language for defining states, actions, invariants
2. **Automated verification** - SMT solver integration (z3, cvc5) for checking properties
3. **Bounded model checking** - `sat trace` and `unsat trace` for validation
4. **Proof reconstruction** - Convert SMT proofs back to Lean proofs

## Core Architecture

### RelationalTransitionSystem Class

```lean
class RelationalTransitionSystem (σ : Type) where
  init : σ → Prop           -- Initial state predicate
  assumptions : σ → Prop    -- Background assumptions
  next : σ -> σ -> Prop     -- Transition relation (pre → post)
  safe : σ → Prop           -- Safety property to verify
  inv : σ → Prop            -- Inductive invariant
```

Key definitions for invariant verification:
- `invSafe`: invariant implies safety (`inv s → safe s`)
- `invInit`: initial states satisfy invariant (`init s → inv s`)
- `invConsecution`: invariant preserved by transitions (`inv s → next s s' → inv s'`)
- `invInductive`: combines all three (sufficient for safety)

### Weakest Precondition (Wp) Monad

Veil uses an omni-style weakest precondition semantics:

```lean
abbrev Wp (m : Mode) (σ ρ : Type) := σ -> RProp σ ρ -> Prop
-- RProp is: σ → ρ → Prop (relates final state to return value)
```

Key operations:
- `Wp.pure` - Return a value
- `Wp.bind` - Sequence actions
- `Wp.assume` - Add assumption (mode-dependent behavior)
- `Wp.assert` - Add assertion
- `Wp.require` - Conditional based on mode (internal=assert, external=assume)
- `Wp.fresh` - Introduce fresh/havoc value
- `Wp.get` / `Wp.set` - State access
- `Wp.spec` - Specification with pre/post conditions

### Mode System

```lean
inductive Mode where
  | internal  -- require acts as assert
  | external  -- require acts as assume
```

This elegantly handles:
- **Internal mode**: Proving the implementation satisfies its preconditions
- **External mode**: Using the action assuming preconditions hold

### BigStep Semantics

Standard operational semantics for comparison/soundness:

```lean
inductive BigStep (act : Wp .internal σ ρ) : σ → σ → ρ → Prop
```

### LawfulAction Typeclass

Ensures soundness of Wp-to-BigStep conversion:

```lean
class LawfulAction (act : Wp .internal σ ρ) where
  inter : act.inter      -- Intermediacy property
  impl : act.impl        -- Implementation property
```

With soundness theorem:
```lean
theorem big_step_sound [LawfulAction act] :
    BigStep act s₀ s r → act.toTwoState s₀ s r
```

## DSL Commands

### Module Definition

```lean
veil module Ring
```

Creates a namespace with state management infrastructure.

### Type and Relation Declarations

```lean
type node                              -- Uninterpreted type
relation leader : node → Prop          -- State component
ghost relation aux : node → Prop       -- Ghost/specification state
immutable relation fixed : node → Prop -- Constant relation
```

### Initial State

```lean
after_init {
  leader N := False
  pending M N := False
}
```

### Actions

```lean
action send (n next : node) = {
  require btwn.btw n next (tot.succ n)
  pending n next := True
}
```

### Safety and Invariants

```lean
safety [single_leader] leader L1 ∧ leader L2 → L1 = L2
invariant [leader_greatest] leader L → le N L
```

### Code Generation

```lean
#gen_state        -- Generate state structure
#gen_spec         -- Generate transition system specification
#check_invariants -- Verify invariants with SMT
```

### Bounded Model Checking

```lean
sat trace {
  call send(n0, n1)
  call recv(n0, n1, n2)
  assert leader n0
} by { bmc_sat }

unsat trace {
  any send
  any recv
  assert leader L1 ∧ leader L2 ∧ L1 ≠ L2
} length 5 by { bmc_unsat }
```

## Simp Attributes

Veil uses precise control over simplification:

| Attribute | Purpose |
|-----------|---------|
| `smtSimp` | SMT-relevant simplifications |
| `logicSimp` | Logical simplifications |
| `quantifierSimp` | Quantifier handling |
| `invSimp` | Invariant simplification |
| `actSimp` | Action simplification |
| `wpSimp` | Weakest precondition simplification |
| `boolSimp` | Boolean simplifications |
| `stateSimp` | State access simplifications |

## VCGenStyle

Two verification condition generation styles:

```lean
inductive VCGenStyle where
  | wp         -- Ivy-style: direct Wp semantics
  | transition -- mypyvy-style: explicit transition relation
```

## Techniques Applicable to LeanEVM

### 1. State Machine Formalization

**Veil's approach**: `RelationalTransitionSystem` class with `init`, `next`, `safe`, `inv`.

**LeanEVM application**: Formalize EVM execution as a transition system:
```lean
class EVMTransitionSystem where
  init : EVMState → Prop
  step : EVMState → EVMState → Prop  -- Single opcode execution
  safe : EVMState → Prop             -- No undefined behavior
  inv : EVMState → Prop              -- Memory/stack bounds, etc.
```

### 2. Wp Monad for Contract Semantics

**Veil's approach**: Wp monad captures all possible outcomes with pre/post reasoning.

**LeanEVM application**: Define contract operations with Wp semantics:
```lean
def transfer : Wp .internal TokenState Unit := do
  require (balanceOf sender ≥ amount)
  modify (decreaseBalance sender amount)
  modify (increaseBalance recipient amount)
```

### 3. Mode-based Require

**Veil's approach**: `require` behaves as assert (internal) or assume (external).

**LeanEVM application**: Same pattern for contract function preconditions:
- Internal mode: Prove contract never violates requires
- External mode: Assume caller satisfies requires when composing

### 4. Simp Attribute Organization

**Veil's approach**: Multiple specialized simp sets for different proof phases.

**LeanEVM application**: Create attribute sets:
```lean
register_simp_attr evmSimp      -- EVM execution simplifications
register_simp_attr contractSimp -- Contract logic simplifications
register_simp_attr storageSimp  -- Storage model simplifications
```

### 5. Invariant Checking Pattern

**Veil's approach**: `#check_invariants` auto-verifies with SMT.

**LeanEVM application**: Create similar command for contract invariants:
```lean
#check_contract_invariants MyToken
-- Verifies: init → inv, inv ∧ op → inv', inv → safe
```

### 6. Bounded Model Checking

**Veil's approach**: `sat trace` / `unsat trace` for finding bugs or validating.

**LeanEVM application**: Trace-based testing for contracts:
```lean
sat trace {
  call transfer(alice, bob, 100)
  call transfer(bob, charlie, 50)
  assert balanceOf charlie = 50
} by { bmc_sat }
```

### 7. Ghost State

**Veil's approach**: `ghost relation` for specification-only state.

**LeanEVM application**: Track invariants that aren't on-chain:
```lean
ghost relation sumOfBalances : Amount  -- Track for proofs only
```

### 8. Two-State Predicates

**Veil's approach**: `Wp.toTwoState` converts to pre/post relation.

**LeanEVM application**: Express transfer correctness:
```lean
def transferCorrect (s s' : TokenState) : Prop :=
  balanceOf s' sender = balanceOf s sender - amount ∧
  balanceOf s' recipient = balanceOf s recipient + amount
```

### 9. LawfulAction Pattern

**Veil's approach**: Typeclass proving action implementations are sound.

**LeanEVM application**: Prove ERC-20 operations are lawful:
```lean
instance : LawfulAction (transfer amount) where
  inter := transfer_inter
  impl := transfer_impl
```

### 10. Compositional Verification

**Veil's approach**: `IsSubStateOf` class for state composition.

**LeanEVM application**: Compose token state with broader contract state:
```lean
instance : IsSubStateOf TokenState ContractState where
  proj := fun s => s.tokenState
  lift := fun s t => { s with tokenState := t }
```

## Example: Blockchain.lean Patterns

The `Examples/IvyBench/Blockchain.lean` example shows:

1. **Complex state modeling**:
```lean
relation last_committed_block : block → Prop
relation block_creator : block → node → Prop
relation parent : block → block → Prop
```

2. **Immutable relations** for constants:
```lean
immutable relation genesis_block : block → Prop
```

3. **Assumptions** about the environment:
```lean
assumption leader_unique ...
```

4. **Multi-invariant verification**:
```lean
invariant [decided_block_committed] ...
invariant [decided_prefix_closed] ...
```

## Implementation Notes for LeanEVM

### Priority Techniques

1. **Wp Monad** - Core abstraction for contract semantics
2. **Simp Attributes** - Essential for proof automation
3. **Two-State Relations** - Natural for contract state changes
4. **Invariant Framework** - Direct application to ERC-20, etc.

### Lower Priority

- SMT integration (complex, may not be needed initially)
- Bounded model checking (useful but secondary)
- Full DSL (can use simpler direct definitions)

### Architectural Recommendations

1. Define `ContractTransitionSystem` class mirroring `RelationalTransitionSystem`
2. Use Wp-style semantics for `Result` monad operations
3. Create `@[contractSimp]` attribute for contract-specific lemmas
4. Build `#verify_invariant` command for automated checking
5. Support ghost state for specification-only properties

## References

- Veil repository: https://github.com/verse-lab/veil
- Key files:
  - `Veil/Model/TransitionSystem.lean` - Core model
  - `Veil/DSL/Action/Theory.lean` - Wp semantics
  - `Examples/Tutorial/Ring.lean` - Complete tutorial
  - `Examples/IvyBench/Blockchain.lean` - Real-world example
