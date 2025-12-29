import Std.Data.HashSet

/-!
# EVM Bytecode Analysis

This module provides static analysis of EVM bytecode, particularly for
identifying valid jump destinations.

## Jump Destination Analysis

The EVM requires that all JUMP/JUMPI targets land on a JUMPDEST (0x5B) opcode.
However, 0x5B can also appear as data within PUSH instructions - these are
NOT valid jump targets.

We must scan the bytecode linearly, skipping PUSH data bytes, to build
an accurate set of valid jump destinations.

## Example

```
Bytecode: 60 5B 5B 00
          ^^ ^^ ^^ ^^
          |  |  |  STOP
          |  |  JUMPDEST (valid!)
          |  Data byte (0x5B but NOT valid!)
          PUSH1
```

The 0x5B at position 1 is PUSH data, not a JUMPDEST.
Only the 0x5B at position 2 is a valid jump target.
-/

namespace LeanEVM.Core.Analysis

/-! ## Jump Destination Analysis -/

/--
Scan bytecode to find all valid JUMPDEST (0x5B) locations.
Skips over PUSH data bytes to ensure we don't mark data as valid targets.

Uses tail recursion for efficiency and cleaner reasoning.

Returns a HashSet of program counter positions that are valid jump destinations.
-/
def analyze_jumpdests (code : ByteArray) : Std.HashSet Nat :=
  let rec loop (pc : Nat) (valid : Std.HashSet Nat) : Std.HashSet Nat :=
    if h : pc >= code.size then
      valid
    else
      let op := code.get! pc

      -- CHECK: Is it a PUSH instruction? (0x60..0x7F)
      if op >= 0x60 && op <= 0x7F then
        let push_bytes := (op.toNat - 0x60) + 1
        -- Skip the opcode + data
        loop (pc + 1 + push_bytes) valid

      -- CHECK: Is it a JUMPDEST? (0x5B)
      else if op == 0x5B then
        loop (pc + 1) (valid.insert pc)

      else
        -- Standard opcode, move to next
        loop (pc + 1) valid
  termination_by code.size - pc

  loop 0 {}

/-- Alias for compatibility -/
abbrev analyzeJumpdests := analyze_jumpdests

/--
Check if a given position is a valid jump destination.
-/
def isValidJumpdest (code : ByteArray) (dest : Nat) : Bool :=
  let valid := analyzeJumpdests code
  valid.contains dest

/-! ## Code Analysis Helpers -/

/--
Get the size of a PUSH instruction's data.
PUSH1 = 1, PUSH2 = 2, ..., PUSH32 = 32
Returns 0 if not a PUSH instruction.
-/
def pushDataSize (opcode : UInt8) : Nat :=
  if opcode >= 0x60 && opcode <= 0x7F then
    (opcode.toNat - 0x60) + 1
  else
    0

/--
Check if an opcode is a PUSH instruction.
-/
def isPush (opcode : UInt8) : Bool :=
  opcode >= 0x60 && opcode <= 0x7F

/--
Check if an opcode terminates execution.
These are: STOP, RETURN, REVERT, INVALID, SELFDESTRUCT
-/
def isTerminating (opcode : UInt8) : Bool :=
  opcode == 0x00 ||  -- STOP
  opcode == 0xF3 ||  -- RETURN
  opcode == 0xFD ||  -- REVERT
  opcode == 0xFE ||  -- INVALID
  opcode == 0xFF     -- SELFDESTRUCT

/--
Check if an opcode is a jump instruction.
-/
def isJump (opcode : UInt8) : Bool :=
  opcode == 0x56 || opcode == 0x57  -- JUMP or JUMPI

/-! ## Basic Block Analysis (for future CFG construction) -/

/--
A basic block in the control flow graph.
-/
structure BasicBlock where
  startPc : Nat
  endPc : Nat
  isJumpTarget : Bool
  terminates : Bool
  deriving Repr

/--
Analyze bytecode into basic blocks.
A new block starts after: JUMP, JUMPI, or at a JUMPDEST.
-/
def analyzeBasicBlocks (code : ByteArray) : Array BasicBlock := Id.run do
  let jumpdests := analyzeJumpdests code
  let mut blocks : Array BasicBlock := #[]
  let mut blockStart : Nat := 0
  let mut pc : Nat := 0

  while pc < code.size do
    let op := code.get! pc

    -- Handle PUSH: skip data
    if isPush op then
      let dataSize := pushDataSize op
      pc := pc + 1 + dataSize
    -- Handle terminating instructions
    else if isTerminating op then
      blocks := blocks.push {
        startPc := blockStart
        endPc := pc
        isJumpTarget := jumpdests.contains blockStart
        terminates := true
      }
      blockStart := pc + 1
      pc := pc + 1
    -- Handle JUMP/JUMPI
    else if isJump op then
      blocks := blocks.push {
        startPc := blockStart
        endPc := pc
        isJumpTarget := jumpdests.contains blockStart
        terminates := false
      }
      blockStart := pc + 1
      pc := pc + 1
    -- Handle JUMPDEST: start new block
    else if op == 0x5B then
      if pc > blockStart then
        blocks := blocks.push {
          startPc := blockStart
          endPc := pc - 1
          isJumpTarget := jumpdests.contains blockStart
          terminates := false
        }
      blockStart := pc
      pc := pc + 1
    else
      pc := pc + 1

  -- Handle remaining code
  if blockStart < code.size then
    blocks := blocks.push {
      startPc := blockStart
      endPc := code.size - 1
      isJumpTarget := jumpdests.contains blockStart
      terminates := false
    }

  return blocks

/-! ## Verification Properties -/

-- Note: HashSet equality proofs require decidability instances
-- that are complex to establish. Properties can be verified at runtime
-- or through testing.

end LeanEVM.Core.Analysis
