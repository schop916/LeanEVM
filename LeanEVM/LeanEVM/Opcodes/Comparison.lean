import LeanEVM.Core.Runtime
import LeanEVM.Core.StackOps

/-!
# EVM Comparison and Bitwise Opcodes

Implementation of comparison and bitwise logic opcodes.

## Opcodes Implemented

### Comparison (0x10-0x15)
| Opcode | Hex  | Gas | Description |
|--------|------|-----|-------------|
| LT     | 0x10 | 3   | a < b       |
| GT     | 0x11 | 3   | a > b       |
| SLT    | 0x12 | 3   | signed a < b |
| SGT    | 0x13 | 3   | signed a > b |
| EQ     | 0x14 | 3   | a == b      |
| ISZERO | 0x15 | 3   | a == 0      |

### Bitwise (0x16-0x1d)
| Opcode | Hex  | Gas | Description |
|--------|------|-----|-------------|
| AND    | 0x16 | 3   | a & b       |
| OR     | 0x17 | 3   | a \| b      |
| XOR    | 0x18 | 3   | a ^ b       |
| NOT    | 0x19 | 3   | ~a          |
| BYTE   | 0x1a | 3   | byte n of x |
| SHL    | 0x1b | 3   | shift left  |
| SHR    | 0x1c | 3   | shift right |
| SAR    | 0x1d | 3   | arith shift |
-/

namespace LeanEVM.Opcodes.Comparison

open LeanEVM.Core.Runtime
open LeanEVM.Core.StackOps
open LearnEVM.Fundamentals

/-! ## Comparison Opcodes -/

/-- LT (0x10): Pop 2, Push 1 if a < b, else 0 -/
def exec_lt (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let result := if a < b then 1 else 0
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- GT (0x11): Pop 2, Push 1 if a > b, else 0 -/
def exec_gt (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let result := if a > b then 1 else 0
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- SLT (0x12): Signed less than -/
def exec_slt (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let sa := toSigned a
  let sb := toSigned b
  let result := if sa < sb then 1 else 0
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- SGT (0x13): Signed greater than -/
def exec_sgt (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let sa := toSigned a
  let sb := toSigned b
  let result := if sa > sb then 1 else 0
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- EQ (0x14): Pop 2, Push 1 if a == b, else 0 -/
def exec_eq (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let result := if a == b then 1 else 0
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- ISZERO (0x15): Pop 1, Push 1 if a == 0, else 0 -/
def exec_iszero (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, rest) ← pop1 stack
  let result := if a == 0 then 1 else 0
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-! ## Bitwise Opcodes -/

/-- AND (0x16): Bitwise AND -/
def exec_and (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let result := a &&& b
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- OR (0x17): Bitwise OR -/
def exec_or (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let result := a ||| b
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- XOR (0x18): Bitwise XOR -/
def exec_xor (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let result := a ^^^ b
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- NOT (0x19): Bitwise NOT -/
def exec_not (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, rest) ← pop1 stack
  -- NOT is (2^256 - 1) - a, which flips all bits
  let result := U256_MAX - a
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- BYTE (0x1a): Extract byte at position i -/
def exec_byte (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (i, x, rest) ← pop2 stack

  -- Byte 0 is the most significant byte
  let result :=
    if i >= 32 then 0
    else (x / (2 ^ (8 * (31 - i)))) % 256

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- SHL (0x1b): Shift left -/
def exec_shl (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (shift, value, rest) ← pop2 stack

  let result :=
    if shift >= 256 then 0
    else wrap256 (value * (2 ^ shift))

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- SHR (0x1c): Logical shift right -/
def exec_shr (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (shift, value, rest) ← pop2 stack

  let result :=
    if shift >= 256 then 0
    else value / (2 ^ shift)

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-- SAR (0x1d): Arithmetic shift right (sign-preserving) -/
def exec_sar (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (shift, value, rest) ← pop2 stack

  let signed := toSigned value
  let shifted :=
    if shift >= 256 then
      if signed < 0 then -1 else 0
    else
      signed / (Int.ofNat (2 ^ shift))
  let result := fromSigned shifted

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/-! ## Dispatch -/

def dispatch (opcode : UInt8) (s : MachineState) : Option (Except String MachineState) :=
  match opcode.toNat with
  | 0x10 => some (exec_lt s)
  | 0x11 => some (exec_gt s)
  | 0x12 => some (exec_slt s)
  | 0x13 => some (exec_sgt s)
  | 0x14 => some (exec_eq s)
  | 0x15 => some (exec_iszero s)
  | 0x16 => some (exec_and s)
  | 0x17 => some (exec_or s)
  | 0x18 => some (exec_xor s)
  | 0x19 => some (exec_not s)
  | 0x1a => some (exec_byte s)
  | 0x1b => some (exec_shl s)
  | 0x1c => some (exec_shr s)
  | 0x1d => some (exec_sar s)
  | _ => none

end LeanEVM.Opcodes.Comparison
