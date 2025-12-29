import LeanEVM.Core.Runtime
import LeanEVM.Core.StackOps
import LeanEVM.Opcodes.Arithmetic
import LeanEVM.Opcodes.Comparison
import LeanEVM.Opcodes.ControlFlow
import LeanEVM.Opcodes.ContextOps

/-!
# EVM Opcode Dispatch Table

This module provides a unified dispatch mechanism for all EVM opcodes.
It integrates the individual opcode implementations into a single
step function.

## Architecture

```
┌─────────────────┐
│    step         │
│  (dispatcher)   │
└────────┬────────┘
         │ opcode
         ▼
    ┌────┴────┐
    │ match   │
    └────┬────┘
         │
    ┌────┼────┬────┬────┐
    ▼    ▼    ▼    ▼    ▼
  Arith Comp  Ctrl Mem  Stack
```

## Usage

```lean
let result := step s
let finalResult := execute s
```

The valid_jumpdests are now cached in MachineState, so no separate
analysis parameter is needed.
-/

namespace LeanEVM.Core.OpcodeTable

open LeanEVM.Core.Runtime
open LeanEVM.Core.StackOps
open LeanEVM.Opcodes
open LearnEVM.Fundamentals

/-! ## Opcode Categories -/

/-- Opcode category for documentation -/
inductive OpcodeCategory
  | arithmetic    -- 0x01-0x0b
  | comparison    -- 0x10-0x1d
  | keccak        -- 0x20
  | environment   -- 0x30-0x48
  | blockInfo     -- 0x40-0x48
  | stack         -- 0x50-0x5f, 0x80-0x9f
  | memory        -- 0x51-0x59
  | storage       -- 0x54-0x55
  | controlFlow   -- 0x56-0x5b
  | push          -- 0x5f-0x7f
  | dup           -- 0x80-0x8f
  | swap          -- 0x90-0x9f
  | log           -- 0xa0-0xa4
  | system        -- 0xf0-0xff
  | invalid
  deriving Repr, DecidableEq

/-- Classify an opcode by category -/
def classifyOpcode (op : UInt8) : OpcodeCategory :=
  let n := op.toNat
  if n >= 0x01 && n <= 0x0b then .arithmetic
  else if n >= 0x10 && n <= 0x1d then .comparison
  else if n == 0x20 then .keccak
  else if n >= 0x30 && n <= 0x3f then .environment
  else if n >= 0x40 && n <= 0x48 then .blockInfo
  else if n == 0x50 then .stack  -- POP
  else if n >= 0x51 && n <= 0x53 then .memory
  else if n >= 0x54 && n <= 0x55 then .storage
  else if n >= 0x56 && n <= 0x5b then .controlFlow
  else if n >= 0x5f && n <= 0x7f then .push
  else if n >= 0x80 && n <= 0x8f then .dup
  else if n >= 0x90 && n <= 0x9f then .swap
  else if n >= 0xa0 && n <= 0xa4 then .log
  else if n >= 0xf0 then .system
  else .invalid

/-! ## Stack Operations (POP, PUSH, DUP, SWAP) -/

/-- POP (0x50): Remove top stack item -/
def exec_pop (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (_, rest) ← pop1 stack
  let wordStack := rest.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/-- PUSH0 (0x5f): Push zero onto stack -/
def exec_push0 (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let final_stack ← push1 stack 0
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/-- PUSH1-PUSH32: Push n bytes onto stack -/
def exec_push (s : MachineState) (n : Nat) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"
  if s.pc + n >= s.code.size then throw "PUSH out of bounds"

  -- Read n bytes from code
  let mut val : Nat := 0
  for i in [:n] do
    val := val * 256 + (s.code.get! (s.pc + 1 + i)).toNat

  let stack := s.stack.map (·.val)
  let final_stack ← push1 stack val
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1 + n, stack := wordStack, gas := s.gas - 3 }

/-- DUP1-DUP16: Duplicate nth stack item -/
def exec_dup (s : MachineState) (n : Nat) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let final_stack ← dup stack n
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- SWAP1-SWAP16: Swap top with nth item -/
def exec_swap (s : MachineState) (n : Nat) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let final_stack ← swap stack n
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-! ## Memory Operations -/

/-- MLOAD (0x51): Load word from memory -/
def exec_mload (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (offset, rest) ← pop1 stack

  -- Read 32 bytes from memory (big-endian)
  let mut val : Nat := 0
  for i in [:32] do
    let idx := offset + i
    let byte := if idx < s.memory.size then s.memory.get! idx else 0
    val := val * 256 + byte.toNat

  let final_stack ← push1 rest val
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- MSTORE (0x52): Store word to memory -/
def exec_mstore (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (offset, value, rest) ← pop2 stack

  -- Expand memory if needed
  let needed := offset + 32
  let mut mem := s.memory
  while mem.size < needed do
    mem := mem.push 0

  -- Write 32 bytes (big-endian)
  let mut v := value
  for i in [:32] do
    let idx := offset + 31 - i
    mem := mem.set! idx (v % 256).toUInt8
    v := v / 256

  let wordStack := rest.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, memory := mem, gas := s.gas - 3 }

/-- MSTORE8 (0x53): Store single byte to memory -/
def exec_mstore8 (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (offset, value, rest) ← pop2 stack

  -- Expand memory if needed
  let mut mem := s.memory
  while mem.size <= offset do
    mem := mem.push 0

  -- Store lowest byte
  mem := mem.set! offset (value % 256).toUInt8

  let wordStack := rest.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, memory := mem, gas := s.gas - 3 }

/-! ## Storage Operations -/

/-- SLOAD (0x54): Load from storage -/
def exec_sload (s : MachineState) : Except String MachineState := do
  if s.gas < 100 then throw "Out of Gas"  -- Warm access cost

  let stack := s.stack.map (·.val)
  let (slot, rest) ← pop1 stack

  let value := s.world.getStorage s.self slot
  let final_stack ← push1 rest value
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 100 }

/-- SSTORE (0x55): Store to storage -/
def exec_sstore (s : MachineState) : Except String MachineState := do
  if s.gas < 100 then throw "Out of Gas"  -- Simplified cost

  let stack := s.stack.map (·.val)
  let (slot, value, rest) ← pop2 stack

  let world' := s.world.setStorage s.self slot value
  let wordStack := rest.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, world := world', gas := s.gas - 100 }

/-! ## Return/Revert Operations -/

/-- RETURN (0xf3): Halt with return data -/
def exec_return (s : MachineState) : Except String MachineState := do
  let stack := s.stack.map (·.val)
  let (offset, size, _) ← pop2 stack

  -- Extract return data from memory
  let mut output := ByteArray.emptyWithCapacity size
  for i in [:size] do
    let idx := offset + i
    let byte := if idx < s.memory.size then s.memory.get! idx else 0
    output := output.push byte

  throw s!"RETURN:{output.size}"

/-- REVERT (0xfd): Halt with revert data -/
def exec_revert (s : MachineState) : Except String MachineState := do
  let stack := s.stack.map (·.val)
  let (offset, size, _) ← pop2 stack

  let mut output := ByteArray.emptyWithCapacity size
  for i in [:size] do
    let idx := offset + i
    let byte := if idx < s.memory.size then s.memory.get! idx else 0
    output := output.push byte

  throw s!"REVERT:{output.size}"

/-! ## Main Dispatch Function -/

/--
Execute a single instruction with full opcode support.
Uses the cached valid_jumpdests from MachineState.
-/
def step (s : MachineState) : Except String MachineState := do
  -- Check end of code
  if s.pc >= s.code.size then throw "STOP"

  let opcode := s.code.get! s.pc
  let n := opcode.toNat

  -- Dispatch by opcode
  match n with
  -- STOP
  | 0x00 => throw "STOP"

  -- Arithmetic (0x01-0x0b)
  | 0x01 => Arithmetic.exec_add s
  | 0x02 => Arithmetic.exec_mul s
  | 0x03 => Arithmetic.exec_sub s
  | 0x04 => Arithmetic.exec_div s
  | 0x05 => Arithmetic.exec_sdiv s
  | 0x06 => Arithmetic.exec_mod s
  | 0x07 => Arithmetic.exec_smod s
  | 0x08 => Arithmetic.exec_addmod s
  | 0x09 => Arithmetic.exec_mulmod s
  | 0x0a => Arithmetic.exec_exp s
  | 0x0b => Arithmetic.exec_signextend s

  -- Comparison (0x10-0x1d)
  | 0x10 => Comparison.exec_lt s
  | 0x11 => Comparison.exec_gt s
  | 0x12 => Comparison.exec_slt s
  | 0x13 => Comparison.exec_sgt s
  | 0x14 => Comparison.exec_eq s
  | 0x15 => Comparison.exec_iszero s
  | 0x16 => Comparison.exec_and s
  | 0x17 => Comparison.exec_or s
  | 0x18 => Comparison.exec_xor s
  | 0x19 => Comparison.exec_not s
  | 0x1a => Comparison.exec_byte s
  | 0x1b => Comparison.exec_shl s
  | 0x1c => Comparison.exec_shr s
  | 0x1d => Comparison.exec_sar s

  -- Context/Environment (0x30-0x3f)
  | 0x30 => ContextOps.exec_address s
  | 0x32 => ContextOps.exec_origin s
  | 0x33 => ContextOps.exec_caller s
  | 0x34 => ContextOps.exec_callvalue s
  | 0x35 => ContextOps.exec_calldataload s
  | 0x36 => ContextOps.exec_calldatasize s
  | 0x37 => ContextOps.exec_calldatacopy s
  | 0x38 => ContextOps.exec_codesize s
  | 0x39 => ContextOps.exec_codecopy s
  | 0x3a => ContextOps.exec_gasprice s
  | 0x3d => ContextOps.exec_returndatasize s
  | 0x3e => ContextOps.exec_returndatacopy s

  -- Stack/Memory/Control (using cached valid_jumpdests)
  | 0x50 => exec_pop s
  | 0x51 => exec_mload s
  | 0x52 => exec_mstore s
  | 0x53 => exec_mstore8 s
  | 0x54 => exec_sload s
  | 0x55 => exec_sstore s
  | 0x56 => ControlFlow.exec_jump s      -- Uses s.valid_jumpdests
  | 0x57 => ControlFlow.exec_jumpi s     -- Uses s.valid_jumpdests
  | 0x58 => ControlFlow.exec_pc s
  | 0x59 => ControlFlow.exec_msize s
  | 0x5a => ControlFlow.exec_gas s
  | 0x5b => ControlFlow.exec_jumpdest s
  | 0x5f => exec_push0 s

  -- PUSH1-PUSH32 (0x60-0x7f)
  | _ =>
    if n >= 0x60 && n <= 0x7f then
      exec_push s (n - 0x60 + 1)
    -- DUP1-DUP16 (0x80-0x8f)
    else if n >= 0x80 && n <= 0x8f then
      exec_dup s (n - 0x80 + 1)
    -- SWAP1-SWAP16 (0x90-0x9f)
    else if n >= 0x90 && n <= 0x9f then
      exec_swap s (n - 0x90 + 1)
    -- RETURN
    else if n == 0xf3 then
      exec_return s
    -- REVERT
    else if n == 0xfd then
      exec_revert s
    -- INVALID
    else if n == 0xfe then
      throw "INVALID"
    else
      throw s!"Unknown Opcode: 0x{Nat.toDigits 16 n |> String.mk}"

/-! ## Execution Loop -/

/-- Extract memory segment as ByteArray -/
def extractMemory (mem : ByteArray) (offset size : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity size
  for i in [:size] do
    if offset + i < mem.size then
      out := out.push (mem.get! (offset + i))
    else
      out := out.push 0
  out

/--
Execution loop. Runs until STOP, RETURN, REVERT, or error.
-/
partial def loop (s : MachineState) : ExecResult :=
  match step s with
  | .ok nextState => loop nextState
  | .error msg =>
    if msg == "STOP" then
      .success s.gas ByteArray.empty s.world s.logs
    else if msg.startsWith "RETURN:" then
      let size := (msg.drop 7).toNat?.getD 0
      let output := extractMemory s.memory 0 size
      .success s.gas output s.world s.logs
    else if msg.startsWith "REVERT:" then
      let size := (msg.drop 7).toNat?.getD 0
      let output := extractMemory s.memory 0 size
      .revert s.gas output
    else
      .halt msg

/--
Execute bytecode from an initialized MachineState.
The valid_jumpdests are already cached in the state from initExecution.
-/
def execute (s : MachineState) : ExecResult :=
  loop s

end LeanEVM.Core.OpcodeTable
