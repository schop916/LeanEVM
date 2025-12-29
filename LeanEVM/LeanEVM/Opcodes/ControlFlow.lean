import LeanEVM.Core.Runtime
import LeanEVM.Core.StackOps

/-!
# EVM Control Flow Opcodes

Implementation of EVM control flow opcodes: JUMP, JUMPI, PC, GAS, JUMPDEST.

## Jump Safety

All jump destinations must be validated against the set of valid JUMPDESTs
stored in `MachineState.valid_jumpdests`. This cache is computed once at
initialization time by scanning the bytecode.

Jumping to an invalid destination causes execution to halt with an error.

## Opcodes Implemented

| Opcode   | Hex  | Gas | Description |
|----------|------|-----|-------------|
| JUMP     | 0x56 | 8   | Unconditional jump |
| JUMPI    | 0x57 | 10  | Conditional jump |
| PC       | 0x58 | 2   | Program counter |
| MSIZE    | 0x59 | 2   | Memory size |
| GAS      | 0x5a | 2   | Remaining gas |
| JUMPDEST | 0x5b | 1   | Jump destination marker |
-/

namespace LeanEVM.Opcodes.ControlFlow

open LeanEVM.Core.Runtime
open LeanEVM.Core.StackOps
open LearnEVM.Fundamentals

/-! ## Control Flow Opcodes -/

/--
JUMP (0x56): Unconditional jump to destination on stack.
Gas: 8

Pops destination from stack and jumps to it.
Throws error if destination is not a valid JUMPDEST.

Uses the cached `valid_jumpdests` from MachineState.
-/
def exec_jump (s : MachineState) : Except String MachineState := do
  -- 1. Gas (Mid-tier cost: 8)
  if s.gas < 8 then throw "Out of Gas"

  -- 2. Pop Destination
  let stack := s.stack.map (·.val)
  let (dest, rest) ← pop1 stack

  -- 3. Verify Validity using cached jumpdests
  if !s.valid_jumpdests.contains dest then
    throw s!"Invalid Jump Destination: {dest}"

  -- 4. Update PC (go exactly to dest, not pc + 1)
  let wordStack := rest.map Word.ofNat

  return { s with
    pc := dest,
    stack := wordStack,
    gas := s.gas - 8
  }

/--
JUMPI (0x57): Conditional jump.
Gas: 10

Pops destination and condition from stack.
Jumps to destination if condition is non-zero.
Otherwise, continues to next instruction.
-/
def exec_jumpi (s : MachineState) : Except String MachineState := do
  -- 1. Gas (High-tier cost: 10)
  if s.gas < 10 then throw "Out of Gas"

  -- 2. Pop arguments
  let stack := s.stack.map (·.val)
  let (dest, cond, rest) ← pop2 stack

  let wordStack := rest.map Word.ofNat

  if cond != 0 then
    -- Condition is True: Jump
    if !s.valid_jumpdests.contains dest then
      throw s!"Invalid Jump Destination: {dest}"

    return { s with
      pc := dest,
      stack := wordStack,
      gas := s.gas - 10
    }
  else
    -- Condition is False: No Jump, just move to next instruction
    return { s with
      pc := s.pc + 1,
      stack := wordStack,
      gas := s.gas - 10
    }

/--
JUMPDEST (0x5b): Mark valid jump destination.
Gas: 1

This opcode does nothing during execution - it's just a marker
that allows JUMP/JUMPI to target this location.
-/
def exec_jumpdest (s : MachineState) : Except String MachineState := do
  if s.gas < 1 then throw "Out of Gas"
  return { s with pc := s.pc + 1, gas := s.gas - 1 }

/--
PC (0x58): Push program counter.
Gas: 2

Pushes the current program counter (before this instruction) onto the stack.
-/
def exec_pc (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let final_stack ← push1 stack s.pc
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
MSIZE (0x59): Push memory size.
Gas: 2

Pushes the size of active memory in bytes (rounded up to nearest word).
-/
def exec_msize (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  -- Memory size is always a multiple of 32
  let memSize := ((s.memory.size + 31) / 32) * 32
  let final_stack ← push1 stack memSize
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
GAS (0x5a): Push remaining gas.
Gas: 2

Pushes the remaining gas (after this instruction) onto the stack.
-/
def exec_gas (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  -- Push gas remaining after this instruction
  let final_stack ← push1 stack (s.gas - 2)
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
STOP (0x00): Halt execution.
Gas: 0

Stops execution with success and no return data.
-/
def exec_stop (_s : MachineState) : Except String MachineState :=
  throw "STOP"

/--
INVALID (0xfe): Invalid instruction.
Gas: all remaining

Consumes all gas and halts with error.
-/
def exec_invalid (_s : MachineState) : Except String MachineState :=
  throw "INVALID"

/-! ## Dispatch -/

/--
Dispatch control flow opcodes.
All opcodes now use the cached valid_jumpdests from MachineState.
-/
def dispatch (opcode : UInt8) (s : MachineState) : Option (Except String MachineState) :=
  match opcode.toNat with
  | 0x00 => some (exec_stop s)
  | 0x56 => some (exec_jump s)
  | 0x57 => some (exec_jumpi s)
  | 0x58 => some (exec_pc s)
  | 0x59 => some (exec_msize s)
  | 0x5a => some (exec_gas s)
  | 0x5b => some (exec_jumpdest s)
  | 0xfe => some (exec_invalid s)
  | _ => none

end LeanEVM.Opcodes.ControlFlow
