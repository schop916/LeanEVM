import LeanEVM.Core.Runtime
import LeanEVM.Core.StackOps

/-!
# EVM Context Opcodes

These opcodes provide the bridge between the "outside world" (the transaction)
and the "inside world" (the stack). Without them, a contract is isolated
and cannot interact with users.

## Verification Perspective

These opcodes introduce **Environmental Non-Determinism**. When verifying:
- `exec_add` is always `a + b` (deterministic)
- `exec_caller` could be anyone (non-deterministic)

When writing proofs, treat `s.caller` as a symbolic variable (e.g., `∀ user, user ≠ 0`).
By isolating these opcodes, you can swap concrete implementations for symbolic ones.

## Opcodes Implemented

| Opcode       | Hex  | Gas | Description |
|--------------|------|-----|-------------|
| ADDRESS      | 0x30 | 2   | Current contract address |
| ORIGIN       | 0x32 | 2   | Transaction origin (tx.origin) |
| CALLER       | 0x33 | 2   | Message sender (msg.sender) |
| CALLVALUE    | 0x34 | 2   | Message value (msg.value) |
| CALLDATALOAD | 0x35 | 3   | Load 32 bytes from calldata |
| CALLDATASIZE | 0x36 | 2   | Size of calldata |
| CALLDATACOPY | 0x37 | 3+  | Copy calldata to memory |
| CODESIZE     | 0x38 | 2   | Size of code |
| CODECOPY     | 0x39 | 3+  | Copy code to memory |
-/

namespace LeanEVM.Opcodes.ContextOps

open LeanEVM.Core.Runtime
open LeanEVM.Core.StackOps
open LearnEVM.Fundamentals

/-! ## Context Opcodes -/

/--
ADDRESS (0x30): Push the current contract's address.
Gas: 2
Stack: [] -> [address]
-/
def exec_address (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let addrNat := s.self.value  -- Address wraps a Nat
  let final_stack ← push1 stack addrNat
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
ORIGIN (0x32): Push the transaction origin (tx.origin).
Gas: 2
Stack: [] -> [address]

Note: This is the original sender of the transaction, NOT msg.sender.
In a call chain A -> B -> C, ORIGIN in C returns A.
-/
def exec_origin (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  -- For now, we use caller as origin (simplified model)
  -- A full implementation would track tx.origin separately
  let stack := s.stack.map (·.val)
  let originNat := s.caller.value
  let final_stack ← push1 stack originNat
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
CALLER (0x33): Push the address of the message sender (msg.sender).
Gas: 2
Stack: [] -> [address]

The address is a 160-bit number, but fits in a 256-bit stack word.
-/
def exec_caller (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let addrNat := s.caller.value  -- Address wraps a Nat
  let final_stack ← push1 stack addrNat
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
CALLVALUE (0x34): Push the amount of Wei sent with the message (msg.value).
Gas: 2
Stack: [] -> [value]
-/
def exec_callvalue (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let final_stack ← push1 stack s.callValue
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
CALLDATALOAD (0x35): Load 32 bytes from calldata starting at offset.
Gas: 3
Stack: [offset] -> [data_word]

CRITICAL: If offset is past the end of data, returns zeros.
Data is read as big-endian (first byte is most significant).
-/
def exec_calldataload (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (offset, rest) ← pop1 stack

  -- Read 32 bytes from calldata at offset (big-endian)
  let mut valNat : Nat := 0
  for i in [:32] do
    let idx := offset + i
    let byteVal : Nat :=
      if idx < s.calldata.size then
        (s.calldata.get! idx).toNat
      else
        0  -- Padding with zero if out of bounds
    valNat := (valNat * 256) + byteVal

  let final_stack ← push1 rest valNat
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 3 }

/--
CALLDATASIZE (0x36): Push the size of the input calldata.
Gas: 2
Stack: [] -> [size]
-/
def exec_calldatasize (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let size := s.calldata.size
  let final_stack ← push1 stack size
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
CALLDATACOPY (0x37): Copy calldata to memory.
Gas: 3 + 3*ceil(size/32)
Stack: [destOffset, offset, size] -> []

Copies `size` bytes from calldata starting at `offset` to memory at `destOffset`.
Pads with zeros if reading past calldata end.
-/
def exec_calldatacopy (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (destOffset, srcOffset, size, rest) ← pop3 stack

  -- Calculate gas cost: 3 + 3 * ceil(size / 32)
  let wordCount := (size + 31) / 32
  let gasCost := 3 + 3 * wordCount
  if s.gas < gasCost then throw "Out of Gas"

  -- Expand memory if needed
  let needed := destOffset + size
  let mut mem := s.memory
  while mem.size < needed do
    mem := mem.push 0

  -- Copy bytes from calldata to memory
  for i in [:size] do
    let srcIdx := srcOffset + i
    let byte : UInt8 :=
      if srcIdx < s.calldata.size then
        s.calldata.get! srcIdx
      else
        0  -- Zero padding
    mem := mem.set! (destOffset + i) byte

  let wordStack := rest.map Word.ofNat

  return { s with
    pc := s.pc + 1,
    stack := wordStack,
    memory := mem,
    gas := s.gas - gasCost
  }

/--
CODESIZE (0x38): Push the size of the current contract's code.
Gas: 2
Stack: [] -> [size]
-/
def exec_codesize (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let size := s.code.size
  let final_stack ← push1 stack size
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
CODECOPY (0x39): Copy code to memory.
Gas: 3 + 3*ceil(size/32)
Stack: [destOffset, offset, size] -> []

Copies `size` bytes from code starting at `offset` to memory at `destOffset`.
Pads with zeros if reading past code end.
-/
def exec_codecopy (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (destOffset, srcOffset, size, rest) ← pop3 stack

  -- Calculate gas cost: 3 + 3 * ceil(size / 32)
  let wordCount := (size + 31) / 32
  let gasCost := 3 + 3 * wordCount
  if s.gas < gasCost then throw "Out of Gas"

  -- Expand memory if needed
  let needed := destOffset + size
  let mut mem := s.memory
  while mem.size < needed do
    mem := mem.push 0

  -- Copy bytes from code to memory
  for i in [:size] do
    let srcIdx := srcOffset + i
    let byte : UInt8 :=
      if srcIdx < s.code.size then
        s.code.get! srcIdx
      else
        0  -- Zero padding
    mem := mem.set! (destOffset + i) byte

  let wordStack := rest.map Word.ofNat

  return { s with
    pc := s.pc + 1,
    stack := wordStack,
    memory := mem,
    gas := s.gas - gasCost
  }

/--
GASPRICE (0x3a): Push the gas price of the transaction.
Gas: 2
Stack: [] -> [gasPrice]

Note: Simplified implementation - returns 0 (would need TxContext for real value)
-/
def exec_gasprice (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  -- Simplified: gas price would come from transaction context
  let gasPrice : Nat := 0
  let final_stack ← push1 stack gasPrice
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
RETURNDATASIZE (0x3d): Push the size of the return data from last call.
Gas: 2
Stack: [] -> [size]
-/
def exec_returndatasize (s : MachineState) : Except String MachineState := do
  if s.gas < 2 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let size := s.returnData.size
  let final_stack ← push1 stack size
  let wordStack := final_stack.map Word.ofNat

  return { s with pc := s.pc + 1, stack := wordStack, gas := s.gas - 2 }

/--
RETURNDATACOPY (0x3e): Copy return data to memory.
Gas: 3 + 3*ceil(size/32)
Stack: [destOffset, offset, size] -> []

Unlike CALLDATACOPY, this throws if reading past returnData bounds.
-/
def exec_returndatacopy (s : MachineState) : Except String MachineState := do
  if s.gas < 3 then throw "Out of Gas"

  let stack := s.stack.map (·.val)
  let (destOffset, srcOffset, size, rest) ← pop3 stack

  -- Check bounds - RETURNDATACOPY throws if out of bounds
  if srcOffset + size > s.returnData.size then
    throw "Return Data Out of Bounds"

  -- Calculate gas cost
  let wordCount := (size + 31) / 32
  let gasCost := 3 + 3 * wordCount
  if s.gas < gasCost then throw "Out of Gas"

  -- Expand memory if needed
  let needed := destOffset + size
  let mut mem := s.memory
  while mem.size < needed do
    mem := mem.push 0

  -- Copy bytes from returnData to memory
  for i in [:size] do
    let byte := s.returnData.get! (srcOffset + i)
    mem := mem.set! (destOffset + i) byte

  let wordStack := rest.map Word.ofNat

  return { s with
    pc := s.pc + 1,
    stack := wordStack,
    memory := mem,
    gas := s.gas - gasCost
  }

/-! ## Dispatch -/

/--
Dispatch context opcodes (0x30-0x3f range).
-/
def dispatch (opcode : UInt8) (s : MachineState) : Option (Except String MachineState) :=
  match opcode.toNat with
  | 0x30 => some (exec_address s)
  | 0x32 => some (exec_origin s)
  | 0x33 => some (exec_caller s)
  | 0x34 => some (exec_callvalue s)
  | 0x35 => some (exec_calldataload s)
  | 0x36 => some (exec_calldatasize s)
  | 0x37 => some (exec_calldatacopy s)
  | 0x38 => some (exec_codesize s)
  | 0x39 => some (exec_codecopy s)
  | 0x3a => some (exec_gasprice s)
  | 0x3d => some (exec_returndatasize s)
  | 0x3e => some (exec_returndatacopy s)
  | _ => none

end LeanEVM.Opcodes.ContextOps
