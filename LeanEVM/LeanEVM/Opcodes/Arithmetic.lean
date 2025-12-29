import LeanEVM.Core.Runtime
import LeanEVM.Core.StackOps

/-!
# EVM Arithmetic Opcodes

Implementation of EVM arithmetic opcodes with proper 256-bit modular arithmetic.

## Critical: Modular Arithmetic

The EVM uses modulo 2^256 arithmetic. All operations wrap on overflow.
We use `Nat` with explicit `% U256_MOD` for correctness.

## Opcodes Implemented

| Opcode | Hex  | Gas | Description |
|--------|------|-----|-------------|
| ADD    | 0x01 | 3   | a + b       |
| MUL    | 0x02 | 5   | a * b       |
| SUB    | 0x03 | 3   | a - b       |
| DIV    | 0x04 | 5   | a / b       |
| SDIV   | 0x05 | 5   | signed div  |
| MOD    | 0x06 | 5   | a % b       |
| SMOD   | 0x07 | 5   | signed mod  |
| ADDMOD | 0x08 | 8   | (a+b) % N   |
| MULMOD | 0x09 | 8   | (a*b) % N   |
| EXP    | 0x0a | 10+ | a ^ b       |
| SIGNEXTEND | 0x0b | 5 | sign extend |
-/

namespace LeanEVM.Opcodes.Arithmetic

open LeanEVM.Core.Runtime
open LeanEVM.Core.StackOps
open LearnEVM.Fundamentals

/-! ## Gas Costs -/

def GAS_VERYLOW : Nat := 3   -- ADD, SUB, LT, GT, etc.
def GAS_LOW : Nat := 5       -- MUL, DIV, MOD, etc.
def GAS_MID : Nat := 8       -- ADDMOD, MULMOD
def GAS_EXP_BASE : Nat := 10 -- EXP base cost
def GAS_EXP_BYTE : Nat := 50 -- EXP per byte of exponent

/-! ## Arithmetic Opcode Implementations -/

/--
ADD (0x01): Pop 2, Push (a + b) % 2^256
Gas: 3
-/
def exec_add (s : MachineState) : Except String MachineState := do
  -- 1. Gas Check
  if s.gas < GAS_VERYLOW then throw "Out of Gas"

  -- 2. Stack Ops (using Nat representation)
  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack

  -- 3. Arithmetic Logic (Wrap around!)
  let result := wrap256 (a + b)

  -- 4. Push Result
  let final_stack ← push1 rest result

  -- 5. Convert back to Word list
  let wordStack := final_stack.map Word.ofNat

  return { s with
    pc := s.pc + 1,
    stack := wordStack,
    gas := s.gas - GAS_VERYLOW
  }

/--
MUL (0x02): Pop 2, Push (a * b) % 2^256
Gas: 5
-/
def exec_mul (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_LOW then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack
  let result := wrap256 (a * b)
  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_LOW }

/--
SUB (0x03): Pop 2, Push (a - b) % 2^256
Gas: 3
Note: If a < b, we wrap around using two's complement.
-/
def exec_sub (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_VERYLOW then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack

  -- Subtraction in modular arithmetic
  let result :=
    if a >= b then a - b
    else (a + U256_MOD) - b

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_VERYLOW }

/--
DIV (0x04): Pop 2, Push a / b (0 if b = 0)
Gas: 5
-/
def exec_div (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_LOW then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack

  -- Division by zero returns 0 in EVM
  let result := if b = 0 then 0 else a / b

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_LOW }

/--
SDIV (0x05): Signed division
Gas: 5
-/
def exec_sdiv (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_LOW then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack

  let result :=
    if b = 0 then 0
    else
      let sa := toSigned a
      let sb := toSigned b
      -- Handle special case: -2^255 / -1 = -2^255 (overflow)
      if sa = Int.negOfNat (U256_MOD / 2) && sb = -1 then
        U256_MOD / 2  -- Returns -2^255 as unsigned
      else
        fromSigned (sa / sb)

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_LOW }

/--
MOD (0x06): Pop 2, Push a % b (0 if b = 0)
Gas: 5
-/
def exec_mod (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_LOW then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack

  -- Modulo by zero returns 0 in EVM
  let result := if b = 0 then 0 else a % b

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_LOW }

/--
SMOD (0x07): Signed modulo
Gas: 5
-/
def exec_smod (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_LOW then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack

  let result :=
    if b = 0 then 0
    else
      let sa := toSigned a
      let sb := toSigned b
      -- Result has same sign as dividend
      fromSigned (sa % sb)

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_LOW }

/--
ADDMOD (0x08): Pop 3, Push (a + b) % N (0 if N = 0)
Gas: 8
Note: Addition is done WITHOUT modular wrap before the final mod.
-/
def exec_addmod (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_MID then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, n, rest) ← pop3 stack

  -- (a + b) % N, where a + b is computed with infinite precision
  let result := if n = 0 then 0 else (a + b) % n

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_MID }

/--
MULMOD (0x09): Pop 3, Push (a * b) % N (0 if N = 0)
Gas: 8
Note: Multiplication is done WITHOUT modular wrap before the final mod.
-/
def exec_mulmod (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_MID then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (a, b, n, rest) ← pop3 stack

  -- (a * b) % N, where a * b is computed with infinite precision
  let result := if n = 0 then 0 else (a * b) % n

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_MID }

/--
EXP (0x0a): Pop 2, Push a ^ b % 2^256
Gas: 10 + 50 * byte_size_of_exponent
-/
def exec_exp (s : MachineState) : Except String MachineState := do
  let stack := s.stack.map (·.val)
  let (a, b, rest) ← pop2 stack

  -- Calculate byte size of exponent for gas
  let byteSize := if b = 0 then 0 else (Nat.log2 b / 8) + 1
  let gasCost := GAS_EXP_BASE + GAS_EXP_BYTE * byteSize

  if s.gas < gasCost then throw "Out of Gas"

  -- Modular exponentiation
  let result := Nat.pow a b % U256_MOD

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - gasCost }

/--
SIGNEXTEND (0x0b): Sign extend a value
Gas: 5
Extends sign from byte position b.
-/
def exec_signextend (s : MachineState) : Except String MachineState := do
  if s.gas < GAS_LOW then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (b, x, rest) ← pop2 stack

  let result :=
    if b >= 31 then x  -- No extension needed
    else
      let bitPos := 8 * (b + 1) - 1
      let signBit := (x / (2 ^ bitPos)) % 2
      if signBit = 0 then
        -- Positive: mask high bits
        x % (2 ^ (bitPos + 1))
      else
        -- Negative: fill high bits with 1s
        let mask := U256_MOD - (2 ^ (bitPos + 1))
        mask + (x % (2 ^ (bitPos + 1)))

  let final_stack ← push1 rest result
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - GAS_LOW }

/-! ## Dispatch Helper -/

/--
Dispatch arithmetic opcodes.
Returns None if not an arithmetic opcode.
-/
def dispatch (opcode : UInt8) (s : MachineState) : Option (Except String MachineState) :=
  match opcode.toNat with
  | 0x01 => some (exec_add s)
  | 0x02 => some (exec_mul s)
  | 0x03 => some (exec_sub s)
  | 0x04 => some (exec_div s)
  | 0x05 => some (exec_sdiv s)
  | 0x06 => some (exec_mod s)
  | 0x07 => some (exec_smod s)
  | 0x08 => some (exec_addmod s)
  | 0x09 => some (exec_mulmod s)
  | 0x0a => some (exec_exp s)
  | 0x0b => some (exec_signextend s)
  | _ => none

end LeanEVM.Opcodes.Arithmetic
