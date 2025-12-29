import LeanEVM.Core.Types
import LeanEVM.Core.Execution

/-!
# EVM Transition System

Models EVM execution as a transition system for formal verification.

## Core Concepts

The EVM is a stack-based virtual machine:
- **State**: Stack, memory, storage, PC, gas, etc.
- **Transitions**: Each opcode execution
- **Safety**: No stack underflow, valid memory access, sufficient gas
- **Invariants**: Stack depth ≤ 1024, PC within code bounds

## Verification Strategy

1. Define `EVMTransitionSystem` with init/next/safe/inv
2. Prove each opcode preserves invariants
3. Conclude all reachable states are safe
-/

namespace LeanEVM.Model

open LeanEVM

/-! ## EVM Constants -/

/-- Maximum stack depth (EVM limit) -/
def MAX_STACK_DEPTH : Nat := 1024

/-- Maximum memory size (practical limit) -/
def MAX_MEMORY_SIZE : Nat := 2^32

/-- Word size in bytes -/
def WORD_SIZE : Nat := 32

/-! ## EVM Execution State -/

/-- EVM stack (list of 256-bit words, head = top) -/
abbrev Stack := List Nat

/-- EVM memory (byte-addressable) -/
abbrev Memory := Nat → UInt8

/-- Program counter -/
abbrev PC := Nat

/-- Gas remaining -/
abbrev Gas := Nat

/-- EVM execution state -/
structure ExecState where
  /-- Operand stack -/
  stack : Stack
  /-- Memory -/
  memory : Memory
  /-- Contract storage -/
  storage : Storage
  /-- Program counter -/
  pc : PC
  /-- Gas remaining -/
  gas : Gas
  /-- Contract bytecode -/
  code : List UInt8
  /-- Call value (msg.value) -/
  callValue : Wei
  /-- Caller address (msg.sender) -/
  caller : Address

namespace ExecState

/-- Initial execution state -/
def init (code : List UInt8) (caller : Address) (value : Wei) (gas : Gas) : ExecState :=
  { stack := []
  , memory := fun _ => 0
  , storage := Storage.empty
  , pc := 0
  , gas := gas
  , code := code
  , callValue := value
  , caller := caller }

/-- Stack depth -/
def stackDepth (s : ExecState) : Nat := s.stack.length

/-- Push value onto stack -/
def push (s : ExecState) (val : Nat) : ExecState :=
  { s with stack := val :: s.stack }

/-- Pop value from stack -/
def pop (s : ExecState) : Option (Nat × ExecState) :=
  match s.stack with
  | [] => none
  | x :: xs => some (x, { s with stack := xs })

/-- Pop n values from stack -/
def popN (s : ExecState) (n : Nat) : Option (List Nat × ExecState) :=
  if s.stack.length < n then none
  else some (s.stack.take n, { s with stack := s.stack.drop n })

/-- Peek at top of stack -/
def peek (s : ExecState) : Option Nat :=
  s.stack.head?

/-- Peek at nth element from top -/
def peekN (s : ExecState) (n : Nat) : Option Nat :=
  s.stack.get? n

/-- Increment PC -/
def incPC (s : ExecState) (n : Nat := 1) : ExecState :=
  { s with pc := s.pc + n }

/-- Consume gas -/
def useGas (s : ExecState) (amount : Gas) : Option ExecState :=
  if s.gas >= amount then some { s with gas := s.gas - amount }
  else none

end ExecState

/-! ## Execution Result -/

/-- Result of executing a single opcode -/
inductive StepResult where
  /-- Execution continues with new state -/
  | continue : ExecState → StepResult
  /-- Execution stopped normally (STOP, RETURN) -/
  | stop : StepResult
  /-- Execution reverted -/
  | revert : String → StepResult
  /-- Out of gas -/
  | outOfGas : StepResult
  /-- Invalid opcode or state -/
  | invalid : String → StepResult

/-! ## Opcodes -/

/-- EVM opcodes (subset for demonstration) -/
inductive Opcode where
  | STOP
  | ADD
  | SUB
  | MUL
  | DIV
  | MOD
  | LT
  | GT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | NOT
  | POP
  | MLOAD
  | MSTORE
  | SLOAD
  | SSTORE
  | JUMP
  | JUMPI
  | PC
  | GAS
  | JUMPDEST
  | PUSH1 (val : UInt8)
  | PUSH32 (val : Nat)
  | DUP1
  | SWAP1
  | RETURN
  | REVERT
  | INVALID

/-! ## Opcode Execution -/

namespace Opcode

/-- Gas cost for opcodes (simplified) -/
def gasCost : Opcode → Gas
  | STOP => 0
  | ADD | SUB | LT | GT | EQ | ISZERO | AND | OR | XOR | NOT | POP => 3
  | MUL | DIV | MOD => 5
  | MLOAD | MSTORE => 3
  | SLOAD => 100  -- Cold access cost
  | SSTORE => 100 -- Simplified
  | JUMP | JUMPI => 8
  | PC | GAS => 2
  | JUMPDEST => 1
  | PUSH1 _ | PUSH32 _ => 3
  | DUP1 | SWAP1 => 3
  | RETURN | REVERT => 0
  | INVALID => 0

/-- Execute ADD: pop two, push sum -/
def execADD (s : ExecState) : StepResult :=
  match s.useGas (gasCost ADD) with
  | none => .outOfGas
  | some s' =>
    match s'.popN 2 with
    | none => .invalid "Stack underflow"
    | some ([a, b], s'') =>
      let result := wrapAdd a b
      .continue (s''.push result).incPC
    | _ => .invalid "Unexpected stack state"

/-- Execute SUB: pop two, push difference -/
def execSUB (s : ExecState) : StepResult :=
  match s.useGas (gasCost SUB) with
  | none => .outOfGas
  | some s' =>
    match s'.popN 2 with
    | none => .invalid "Stack underflow"
    | some ([a, b], s'') =>
      let result := wrapSub a b
      .continue (s''.push result).incPC
    | _ => .invalid "Unexpected stack state"

/-- Execute PUSH1: push 1-byte value -/
def execPUSH1 (s : ExecState) (val : UInt8) : StepResult :=
  match s.useGas (gasCost (PUSH1 val)) with
  | none => .outOfGas
  | some s' =>
    if s'.stackDepth >= MAX_STACK_DEPTH then
      .invalid "Stack overflow"
    else
      .continue ((s'.push val.toNat).incPC 2)

/-- Execute POP: pop and discard -/
def execPOP (s : ExecState) : StepResult :=
  match s.useGas (gasCost POP) with
  | none => .outOfGas
  | some s' =>
    match s'.pop with
    | none => .invalid "Stack underflow"
    | some (_, s'') => .continue s''.incPC

/-- Execute DUP1: duplicate top of stack -/
def execDUP1 (s : ExecState) : StepResult :=
  match s.useGas (gasCost DUP1) with
  | none => .outOfGas
  | some s' =>
    match s'.peek with
    | none => .invalid "Stack underflow"
    | some val =>
      if s'.stackDepth >= MAX_STACK_DEPTH then
        .invalid "Stack overflow"
      else
        .continue (s'.push val).incPC

/-- Execute ISZERO: push 1 if top is zero, else 0 -/
def execISZERO (s : ExecState) : StepResult :=
  match s.useGas (gasCost ISZERO) with
  | none => .outOfGas
  | some s' =>
    match s'.pop with
    | none => .invalid "Stack underflow"
    | some (val, s'') =>
      let result := if val == 0 then 1 else 0
      .continue (s''.push result).incPC

/-- Execute SLOAD: load from storage -/
def execSLOAD (s : ExecState) : StepResult :=
  match s.useGas (gasCost SLOAD) with
  | none => .outOfGas
  | some s' =>
    match s'.pop with
    | none => .invalid "Stack underflow"
    | some (slot, s'') =>
      let val := s''.storage.read slot
      .continue (s''.push val).incPC

/-- Execute SSTORE: store to storage -/
def execSSTORE (s : ExecState) : StepResult :=
  match s.useGas (gasCost SSTORE) with
  | none => .outOfGas
  | some s' =>
    match s'.popN 2 with
    | none => .invalid "Stack underflow"
    | some ([slot, val], s'') =>
      let storage' := s''.storage.write slot val
      .continue { s'' with storage := storage' }.incPC
    | _ => .invalid "Unexpected stack state"

/-- Execute STOP -/
def execSTOP (_s : ExecState) : StepResult := .stop

/-- Execute REVERT -/
def execREVERT (_s : ExecState) : StepResult := .revert "REVERT opcode"

/-- Execute a single opcode -/
def exec (op : Opcode) (s : ExecState) : StepResult :=
  match op with
  | STOP => execSTOP s
  | ADD => execADD s
  | SUB => execSUB s
  | PUSH1 val => execPUSH1 s val
  | POP => execPOP s
  | DUP1 => execDUP1 s
  | ISZERO => execISZERO s
  | SLOAD => execSLOAD s
  | SSTORE => execSSTORE s
  | REVERT => execREVERT s
  | _ => .invalid "Opcode not implemented"

end Opcode

/-! ## EVM Transition System -/

/-- EVM transition system class -/
class EVMTransitionSystem (S : Type) where
  /-- Initial state predicate -/
  init : S → Prop
  /-- Transition relation (single opcode step) -/
  step : S → S → Prop
  /-- Safety: state has no undefined behavior -/
  safe : S → Prop
  /-- Inductive invariant -/
  inv : S → Prop

namespace EVMTransitionSystem

variable {S : Type}

/-- Invariant is preserved -/
def invConsecution' (ts : EVMTransitionSystem S) : Prop :=
  ∀ s s', ts.inv s → ts.step s s' → ts.inv s'

/-- Initial states satisfy invariant -/
def invInit' (ts : EVMTransitionSystem S) : Prop :=
  ∀ s, ts.init s → ts.inv s

/-- Invariant implies safety -/
def invSafe' (ts : EVMTransitionSystem S) : Prop :=
  ∀ s, ts.inv s → ts.safe s

/-- Invariant is inductive -/
def invInductive' (ts : EVMTransitionSystem S) : Prop :=
  invInit' ts ∧ invConsecution' ts ∧ invSafe' ts

end EVMTransitionSystem

/-! ## ExecState as Transition System -/

/-- Safety predicate for EVM execution state -/
def ExecStateSafe (s : ExecState) : Prop :=
  -- Stack depth within bounds
  s.stackDepth ≤ MAX_STACK_DEPTH ∧
  -- PC within code bounds (or at end)
  s.pc ≤ s.code.length ∧
  -- Gas is non-negative (always true for Nat)
  True

/-- Core invariant for EVM execution -/
def ExecStateInv (s : ExecState) : Prop :=
  -- Stack depth within bounds
  s.stackDepth ≤ MAX_STACK_DEPTH ∧
  -- PC within code bounds
  s.pc ≤ s.code.length

/-- Initial state predicate -/
def ExecStateInit (code : List UInt8) (s : ExecState) : Prop :=
  s = ExecState.init code Address.zero 0 1000000

/-- Transition: successful opcode execution -/
def ExecStateStep (s s' : ExecState) : Prop :=
  ∃ op, Opcode.exec op s = StepResult.continue s'

/-! ## Safety Proofs -/

section SafetyProofs

/-- PUSH1 preserves stack bound when under limit -/
theorem push1_preserves_stackBound (s : ExecState) (val : UInt8)
    (h_bound : s.stackDepth < MAX_STACK_DEPTH)
    (h_gas : s.gas ≥ Opcode.gasCost (Opcode.PUSH1 val)) :
    ∀ s', Opcode.execPUSH1 s val = StepResult.continue s' →
    s'.stackDepth ≤ MAX_STACK_DEPTH := by
  intro s' h_exec
  -- Direct computation: execPUSH1 with sufficient gas and stack space returns continue
  unfold Opcode.execPUSH1 ExecState.useGas at h_exec
  simp only [h_gas, ↓reduceIte] at h_exec
  -- Now the gas check passed, check stack overflow
  unfold ExecState.stackDepth at h_bound
  simp only [MAX_STACK_DEPTH] at h_bound
  -- s.stack.length < 1024
  have h_no_overflow : ¬(s.stack.length ≥ MAX_STACK_DEPTH) := by
    simp only [MAX_STACK_DEPTH]; omega
  simp only [ExecState.stackDepth, h_no_overflow, ↓reduceIte, StepResult.continue.injEq] at h_exec
  rw [← h_exec]
  unfold ExecState.push ExecState.incPC ExecState.stackDepth MAX_STACK_DEPTH
  simp only [List.length_cons]
  omega

/-- Helper: pop returns shorter stack -/
theorem pop_stack_shorter {s s_out : ExecState} {x : Nat}
    (h : s.pop = some (x, s_out)) :
    s_out.stack.length < s.stack.length := by
  unfold ExecState.pop at h
  match h_stack : s.stack with
  | [] =>
    simp only [h_stack] at h
    contradiction
  | hd :: tl =>
    simp only [h_stack, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h_eq⟩ := h
    simp only [← h_eq, h_stack, List.length_cons]
    omega

/-- POP preserves stack bound -/
theorem pop_preserves_stackBound (s : ExecState)
    (h_bound : s.stackDepth ≤ MAX_STACK_DEPTH) :
    ∀ s', Opcode.execPOP s = StepResult.continue s' →
    s'.stackDepth ≤ MAX_STACK_DEPTH := by
  intro s' h_exec
  unfold Opcode.execPOP at h_exec
  -- Case on gas
  match h_gas : s.useGas (Opcode.gasCost .POP) with
  | none =>
    simp only [h_gas] at h_exec
    contradiction
  | some s_with_gas =>
    simp only [h_gas] at h_exec
    -- Case on pop
    match h_pop : s_with_gas.pop with
    | none =>
      simp only [h_pop] at h_exec
      contradiction
    | some (x, s_popped) =>
      simp only [h_pop, StepResult.continue.injEq] at h_exec
      rw [← h_exec]
      simp only [ExecState.incPC, ExecState.stackDepth, MAX_STACK_DEPTH]
      -- s_popped has shorter stack than s_with_gas, which has same stack as s
      have h_stack_eq : s_with_gas.stack = s.stack := by
        unfold ExecState.useGas at h_gas
        split at h_gas
        · simp only [Option.some.injEq] at h_gas
          rw [← h_gas]
        · contradiction
      have h_shorter := pop_stack_shorter h_pop
      rw [h_stack_eq] at h_shorter
      simp only [ExecState.stackDepth, MAX_STACK_DEPTH] at h_bound
      omega

/-- Initial state satisfies invariant -/
theorem init_satisfies_inv (code : List UInt8) :
    ExecStateInv (ExecState.init code Address.zero 0 1000000) := by
  unfold ExecStateInv ExecState.init ExecState.stackDepth
  simp only [List.length_nil, Nat.zero_le, Nat.le_refl, and_self]

/-- Invariant implies safety -/
theorem inv_implies_safe (s : ExecState) :
    ExecStateInv s → ExecStateSafe s := by
  intro h
  unfold ExecStateSafe ExecStateInv at *
  exact ⟨h.1, h.2, trivial⟩

end SafetyProofs

/-! ## Stack Underflow Protection -/

section StackUnderflow

/-- Operations that require n stack elements -/
def stackRequirement : Opcode → Nat
  | .STOP => 0
  | .ADD | .SUB | .MUL | .DIV | .MOD | .LT | .GT | .EQ | .AND | .OR | .XOR => 2
  | .ISZERO | .NOT | .POP => 1
  | .MLOAD => 1
  | .MSTORE | .SSTORE => 2
  | .SLOAD => 1
  | .JUMP => 1
  | .JUMPI => 2
  | .DUP1 => 1
  | .SWAP1 => 2
  | .RETURN | .REVERT => 2
  | .PUSH1 _ | .PUSH32 _ | .PC | .GAS | .JUMPDEST | .INVALID => 0

/-- Stack-safe: sufficient elements for operation -/
def stackSafe (op : Opcode) (s : ExecState) : Prop :=
  s.stackDepth ≥ stackRequirement op

/-- If stack-safe, operation doesn't underflow -/
theorem stack_safe_no_underflow (op : Opcode) (s : ExecState)
    (h_safe : stackSafe op s)
    (h_gas : s.gas ≥ Opcode.gasCost op) :
    Opcode.exec op s ≠ StepResult.invalid "Stack underflow" := by
  unfold stackSafe stackRequirement at h_safe
  cases op <;> simp [Opcode.exec]
  all_goals sorry  -- Individual cases would need detailed proofs

end StackUnderflow

/-! ## Summary

This module provides:

1. **ExecState**: Complete EVM execution state
2. **Opcode**: Subset of EVM opcodes with execution semantics
3. **EVMTransitionSystem**: Typeclass for transition system verification
4. **Safety proofs**:
   - `push1_preserves_stackBound`: PUSH1 keeps stack bounded
   - `pop_preserves_stackBound`: POP keeps stack bounded
   - `init_satisfies_inv`: Initial state is safe
   - `inv_implies_safe`: Invariant implies safety

The pattern:
- Define safety and invariant predicates
- Prove each opcode preserves the invariant
- Conclude all reachable states are safe
-/

end LeanEVM.Model
