import LeanEVM.Core.Types
import LeanEVM.Core.Analysis
import LearnEVM.Fundamentals.Stack
import LearnEVM.Opcodes.Arithmetic
import Std.Data.HashSet
-- Note: StackOps and MemoryOps not imported to avoid gasCost naming conflict
-- We implement memory/stack ops directly in the step function

/-!
# EVM Execution Runtime

This module implements the core execution loop for the EVM.
It bridges the static state representations with dynamic execution.

## Architecture

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  Transaction    │────▶│  MachineState   │────▶│  ExecResult     │
│  + WorldState   │     │  (volatile)     │     │  (final)        │
└─────────────────┘     └─────────────────┘     └─────────────────┘
                              │
                              ▼
                        ┌─────────────────┐
                        │  step function  │◀───┐
                        │  (fetch/decode) │    │
                        └────────┬────────┘    │
                                 │             │
                                 └─────────────┘
                                   (loop)
```

## Key Components

1. **MachineState**: Volatile state that changes with each opcode
2. **ExecResult**: Final outcome of execution
3. **step**: Single instruction execution
4. **loop**: Recursive execution until termination
-/

namespace LeanEVM.Core.Runtime

open LeanEVM
open LearnEVM.Fundamentals
open LearnEVM.Opcodes

/-! ## World State -/

/-- Account state in world state -/
structure Account where
  nonce   : Nat
  balance : Wei
  code    : ByteArray
  storage : Storage
  deriving Inhabited

/-- World state: mapping from addresses to accounts -/
structure WorldState where
  accounts : Address → Option Account
  deriving Inhabited

namespace WorldState

/-- Empty world with no accounts -/
def empty : WorldState := ⟨fun _ => none⟩

/-- Get account at address -/
def getAccount (w : WorldState) (addr : Address) : Option Account :=
  w.accounts addr

/-- Set account at address -/
def setAccount (w : WorldState) (addr : Address) (acct : Account) : WorldState :=
  ⟨fun a => if a == addr then some acct else w.accounts a⟩

/-- Get balance of address -/
def getBalance (w : WorldState) (addr : Address) : Wei :=
  (w.accounts addr).map (·.balance) |>.getD 0

/-- Get code at address -/
def getCode (w : WorldState) (addr : Address) : ByteArray :=
  (w.accounts addr).map (·.code) |>.getD ByteArray.empty

/-- Get storage value -/
def getStorage (w : WorldState) (addr : Address) (slot : StorageSlot) : StorageValue :=
  match w.accounts addr with
  | some acct => acct.storage slot
  | none => 0

/-- Set storage value -/
def setStorage (w : WorldState) (addr : Address) (slot : StorageSlot) (val : StorageValue) : WorldState :=
  match w.accounts addr with
  | some acct =>
    let newStorage := acct.storage.write slot val
    w.setAccount addr { acct with storage := newStorage }
  | none =>
    -- Create new account with just this storage slot
    let newAcct : Account := {
      nonce := 0
      balance := 0
      code := ByteArray.empty
      storage := Storage.empty.write slot val
    }
    w.setAccount addr newAcct

end WorldState

/-! ## Transaction Context -/

/-- Full transaction context for execution -/
structure ExecutionTx where
  origin    : Address        -- tx.origin
  caller    : Address        -- msg.sender
  target    : Option Address -- None for contract creation
  value     : Wei            -- msg.value
  gasLimit  : Nat            -- Gas limit
  gasPrice  : Nat            -- Gas price
  txData    : ByteArray      -- Calldata / init code
  deriving Inhabited

/-! ## Log Entry -/

/-- EVM log entry (for events) -/
structure LogEntry where
  address : Address
  topics  : List Nat        -- Up to 4 topics
  data    : ByteArray
  deriving Inhabited

/-! ## Machine State -/

/--
The volatile machine state.
This changes with every single opcode execution.
-/
structure MachineState where
  /-- Program counter -/
  pc       : Nat
  /-- The EVM stack (using Word = Fin 2^256) -/
  stack    : List Word
  /-- Volatile memory -/
  memory   : ByteArray
  /-- Gas remaining -/
  gas      : Nat
  /-- The bytecode being executed -/
  code     : ByteArray
  /-- Reference to the global world state -/
  world    : WorldState
  /-- Input calldata -/
  calldata : ByteArray
  /-- Accumulated log entries -/
  logs     : List LogEntry
  /-- Return data from last call -/
  returnData : ByteArray
  /-- Current execution address -/
  self     : Address
  /-- Message caller -/
  caller   : Address
  /-- Call value -/
  callValue : Wei
  /-- Cache of valid jump destinations (computed once at init) -/
  valid_jumpdests : Std.HashSet Nat
  deriving Inhabited

/-! ## Execution Result -/

/-- The result of EVM execution -/
inductive ExecResult
  | success (gasLeft : Nat) (output : ByteArray) (finalWorld : WorldState) (logs : List LogEntry)
  | revert  (gasLeft : Nat) (output : ByteArray)
  | halt    (reason : String)
  deriving Inhabited

/-! ## Initialization -/

/-- Initialize machine state from transaction and world state -/
def initExecution (tx : ExecutionTx) (world : WorldState) (contractAddr : Address) : MachineState :=
  -- If target is None, we are creating a contract (init code is in txData)
  -- If target is Some, we load that account's code
  let code := match tx.target with
    | none => tx.txData  -- Contract creation: txData is init code
    | some addr => world.getCode addr

  -- RUN ANALYSIS ONCE at initialization
  let jumps := Analysis.analyze_jumpdests code

  {
    pc := 0
    stack := []
    memory := ByteArray.empty
    gas := tx.gasLimit
    code := code
    world := world
    calldata := tx.txData
    logs := []
    returnData := ByteArray.empty
    self := contractAddr
    caller := tx.caller
    callValue := tx.value
    valid_jumpdests := jumps  -- Store the analyzed jumpdests
  }

/-! ## Gas Costs -/

/-- Gas cost for common opcodes -/
def gasCostOf (opcode : UInt8) : Nat :=
  match opcode.toNat with
  | 0x00 => 0      -- STOP
  | 0x01 => 3      -- ADD
  | 0x02 => 5      -- MUL
  | 0x03 => 3      -- SUB
  | 0x04 => 5      -- DIV
  | 0x05 => 5      -- SDIV
  | 0x06 => 5      -- MOD
  | 0x07 => 5      -- SMOD
  | 0x08 => 8      -- ADDMOD
  | 0x09 => 8      -- MULMOD
  | 0x0a => 10     -- EXP (base, dynamic for exponent size)
  | 0x10 => 3      -- LT
  | 0x11 => 3      -- GT
  | 0x12 => 3      -- SLT
  | 0x13 => 3      -- SGT
  | 0x14 => 3      -- EQ
  | 0x15 => 3      -- ISZERO
  | 0x16 => 3      -- AND
  | 0x17 => 3      -- OR
  | 0x18 => 3      -- XOR
  | 0x19 => 3      -- NOT
  | 0x1a => 3      -- BYTE
  | 0x1b => 3      -- SHL
  | 0x1c => 3      -- SHR
  | 0x1d => 3      -- SAR
  | 0x20 => 30     -- KECCAK256 (base, plus dynamic)
  | 0x30 => 2      -- ADDRESS
  | 0x31 => 100    -- BALANCE (cold: 2600)
  | 0x32 => 2      -- ORIGIN
  | 0x33 => 2      -- CALLER
  | 0x34 => 2      -- CALLVALUE
  | 0x35 => 3      -- CALLDATALOAD
  | 0x36 => 2      -- CALLDATASIZE
  | 0x37 => 3      -- CALLDATACOPY (base)
  | 0x38 => 2      -- CODESIZE
  | 0x39 => 3      -- CODECOPY (base)
  | 0x50 => 2      -- POP
  | 0x51 => 3      -- MLOAD
  | 0x52 => 3      -- MSTORE
  | 0x53 => 3      -- MSTORE8
  | 0x54 => 100    -- SLOAD (cold: 2100)
  | 0x55 => 100    -- SSTORE (complex gas rules)
  | 0x56 => 8      -- JUMP
  | 0x57 => 10     -- JUMPI
  | 0x58 => 2      -- PC
  | 0x59 => 2      -- MSIZE
  | 0x5a => 2      -- GAS
  | 0x5b => 1      -- JUMPDEST
  | 0x5f => 2      -- PUSH0
  | _ =>
    -- PUSH1-PUSH32: 0x60-0x7f
    if opcode.toNat >= 0x60 && opcode.toNat <= 0x7f then 3
    -- DUP1-DUP16: 0x80-0x8f
    else if opcode.toNat >= 0x80 && opcode.toNat <= 0x8f then 3
    -- SWAP1-SWAP16: 0x90-0x9f
    else if opcode.toNat >= 0x90 && opcode.toNat <= 0x9f then 3
    -- LOG0-LOG4: 0xa0-0xa4
    else if opcode.toNat >= 0xa0 && opcode.toNat <= 0xa4 then 375
    else 0

/-! ## Stack Helpers -/

/-- Pop one value from stack -/
def popStack (stack : List Word) : Except String (Word × List Word) :=
  match stack with
  | [] => .error "Stack Underflow"
  | w :: rest => .ok (w, rest)

/-- Pop two values from stack -/
def pop2Stack (stack : List Word) : Except String (Word × Word × List Word) :=
  match stack with
  | a :: b :: rest => .ok (a, b, rest)
  | _ => .error "Stack Underflow"

/-- Pop three values from stack -/
def pop3Stack (stack : List Word) : Except String (Word × Word × Word × List Word) :=
  match stack with
  | a :: b :: c :: rest => .ok (a, b, c, rest)
  | _ => .error "Stack Underflow"

/-- Push value onto stack (with overflow check) -/
def pushStack (stack : List Word) (w : Word) : Except String (List Word) :=
  if stack.length >= 1024 then
    .error "Stack Overflow"
  else
    .ok (w :: stack)

/-! ## Memory Helpers -/

/-- Read 32 bytes from memory at offset -/
def mload (mem : ByteArray) (offset : Nat) : Word := Id.run do
  let mut val : Nat := 0
  for i in [:32] do
    let idx := offset + i
    let byte := if idx < mem.size then mem.get! idx else 0
    val := val * 256 + byte.toNat
  Word.ofNat val

/-- Write 32 bytes to memory at offset -/
def mstore (mem : ByteArray) (offset : Nat) (val : Word) : ByteArray := Id.run do
  -- Expand memory if needed
  let mut m := mem
  let needed := offset + 32
  while m.size < needed do
    m := m.push 0
  -- Write bytes (big-endian)
  let mut v := val.val
  for i in [:32] do
    let idx := offset + 31 - i
    m := m.set! idx (v % 256).toUInt8
    v := v / 256
  return m

/-- Write single byte to memory -/
def mstore8 (mem : ByteArray) (offset : Nat) (val : UInt8) : ByteArray := Id.run do
  let mut m := mem
  while m.size <= offset do
    m := m.push 0
  m.set! offset val

/-! ## The Step Function (Fetch-Decode-Execute) -/

/--
Execute a single instruction.
Returns Either an error message (halt/stop/revert) or the next state.
-/
def step (s : MachineState) : Except String MachineState := do
  -- 1. Check if we've reached end of code
  if s.pc >= s.code.size then
    throw "STOP"

  -- 2. Fetch opcode
  let opcode := s.code.get! s.pc
  let cost := gasCostOf opcode

  -- 3. Check gas
  if s.gas < cost then
    throw "Out of Gas"

  -- 4. Decode & Execute
  match opcode.toNat with
  | 0x00 => -- STOP
    throw "STOP"

  | 0x01 => -- ADD
    let (a, b, rest) ← pop2Stack s.stack
    let result := add a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x02 => -- MUL
    let (a, b, rest) ← pop2Stack s.stack
    let result := mul a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x03 => -- SUB
    let (a, b, rest) ← pop2Stack s.stack
    let result := sub a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x04 => -- DIV
    let (a, b, rest) ← pop2Stack s.stack
    let result := div a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x06 => -- MOD
    let (a, b, rest) ← pop2Stack s.stack
    let result := mod a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x10 => -- LT
    let (a, b, rest) ← pop2Stack s.stack
    let result := lt a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x11 => -- GT
    let (a, b, rest) ← pop2Stack s.stack
    let result := gt a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x14 => -- EQ
    let (a, b, rest) ← pop2Stack s.stack
    let result := eq a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x15 => -- ISZERO
    let (a, rest) ← popStack s.stack
    let result := iszero a
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x16 => -- AND
    let (a, b, rest) ← pop2Stack s.stack
    let result := and a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x17 => -- OR
    let (a, b, rest) ← pop2Stack s.stack
    let result := or a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x18 => -- XOR
    let (a, b, rest) ← pop2Stack s.stack
    let result := xor a b
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x19 => -- NOT
    let (a, rest) ← popStack s.stack
    let result := not a
    let stack' ← pushStack rest result
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x34 => -- CALLVALUE
    let stack' ← pushStack s.stack (Word.ofNat s.callValue)
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x35 => -- CALLDATALOAD
    let (offset, rest) ← popStack s.stack
    -- Read 32 bytes from calldata at offset
    let mut val : Nat := 0
    for i in [:32] do
      let idx := offset.val + i
      let byte := if idx < s.calldata.size then s.calldata.get! idx else 0
      val := val * 256 + byte.toNat
    let stack' ← pushStack rest (Word.ofNat val)
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x36 => -- CALLDATASIZE
    let stack' ← pushStack s.stack (Word.ofNat s.calldata.size)
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x50 => -- POP
    let (_, rest) ← popStack s.stack
    return { s with pc := s.pc + 1, stack := rest, gas := s.gas - cost }

  | 0x51 => -- MLOAD
    let (offset, rest) ← popStack s.stack
    let val := mload s.memory offset.val
    let stack' ← pushStack rest val
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x52 => -- MSTORE
    let (offset, val, rest) ← pop2Stack s.stack
    let mem' := mstore s.memory offset.val val
    return { s with pc := s.pc + 1, stack := rest, memory := mem', gas := s.gas - cost }

  | 0x53 => -- MSTORE8
    let (offset, val, rest) ← pop2Stack s.stack
    let mem' := mstore8 s.memory offset.val (val.val % 256).toUInt8
    return { s with pc := s.pc + 1, stack := rest, memory := mem', gas := s.gas - cost }

  | 0x54 => -- SLOAD
    let (slot, rest) ← popStack s.stack
    let val := s.world.getStorage s.self slot.val
    let stack' ← pushStack rest (Word.ofNat val)
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x55 => -- SSTORE
    let (slot, val, rest) ← pop2Stack s.stack
    let world' := s.world.setStorage s.self slot.val val.val
    return { s with pc := s.pc + 1, stack := rest, world := world', gas := s.gas - cost }

  | 0x56 => -- JUMP
    let (dest, rest) ← popStack s.stack
    -- Should validate JUMPDEST, simplified here
    return { s with pc := dest.val, stack := rest, gas := s.gas - cost }

  | 0x57 => -- JUMPI
    let (dest, cond, rest) ← pop2Stack s.stack
    let newPc := if cond.val != 0 then dest.val else s.pc + 1
    return { s with pc := newPc, stack := rest, gas := s.gas - cost }

  | 0x58 => -- PC
    let stack' ← pushStack s.stack (Word.ofNat s.pc)
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x59 => -- MSIZE
    let size := ((s.memory.size + 31) / 32) * 32  -- Round up to word
    let stack' ← pushStack s.stack (Word.ofNat size)
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x5a => -- GAS
    let stack' ← pushStack s.stack (Word.ofNat (s.gas - cost))
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | 0x5b => -- JUMPDEST
    -- No-op, just marks valid jump destination
    return { s with pc := s.pc + 1, gas := s.gas - cost }

  | 0x5f => -- PUSH0
    let stack' ← pushStack s.stack Word.zero
    return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

  | n =>
    -- PUSH1-PUSH32 (0x60-0x7f)
    if n >= 0x60 && n <= 0x7f then
      let pushSize := n - 0x60 + 1
      if s.pc + pushSize >= s.code.size then
        throw "PUSH out of bounds"
      -- Read pushSize bytes
      let mut val : Nat := 0
      for i in [:pushSize] do
        val := val * 256 + (s.code.get! (s.pc + 1 + i)).toNat
      let stack' ← pushStack s.stack (Word.ofNat val)
      return { s with pc := s.pc + 1 + pushSize, stack := stack', gas := s.gas - cost }

    -- DUP1-DUP16 (0x80-0x8f)
    else if n >= 0x80 && n <= 0x8f then
      let dupIdx := n - 0x80  -- 0-indexed
      match s.stack[dupIdx]? with
      | none => throw "Stack Underflow (DUP)"
      | some w =>
        let stack' ← pushStack s.stack w
        return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }

    -- SWAP1-SWAP16 (0x90-0x9f)
    else if n >= 0x90 && n <= 0x9f then
      let swapIdx := n - 0x90 + 1  -- 1-indexed (SWAP1 swaps with 2nd element)
      if s.stack.length < swapIdx + 1 then
        throw "Stack Underflow (SWAP)"
      else
        match s.stack[0]?, s.stack[swapIdx]? with
        | some top, some nth =>
          let stack' := s.stack.set 0 nth |>.set swapIdx top
          return { s with pc := s.pc + 1, stack := stack', gas := s.gas - cost }
        | _, _ => throw "Stack Underflow (SWAP)"

    -- RETURN (0xf3)
    else if n == 0xf3 then
      let (offset, size, _) ← pop2Stack s.stack
      -- Extract return data from memory
      let mut output := ByteArray.emptyWithCapacity size.val
      for i in [:size.val] do
        let idx := offset.val + i
        let byte := if idx < s.memory.size then s.memory.get! idx else 0
        output := output.push byte
      throw s!"RETURN:{output.size}"  -- Special encoding for return

    -- REVERT (0xfd)
    else if n == 0xfd then
      let (offset, size, _) ← pop2Stack s.stack
      let mut output := ByteArray.emptyWithCapacity size.val
      for i in [:size.val] do
        let idx := offset.val + i
        let byte := if idx < s.memory.size then s.memory.get! idx else 0
        output := output.push byte
      throw s!"REVERT:{output.size}"

    -- INVALID (0xfe)
    else if n == 0xfe then
      throw "INVALID"

    else
      throw s!"Unknown Opcode: 0x{Nat.toDigits 16 n |> String.mk}"

/-! ## The Execution Loop -/

/--
Execute until termination.
Uses `partial` since termination depends on gas consumption.
-/
partial def loop (s : MachineState) : ExecResult :=
  match step s with
  | .ok nextState =>
    loop nextState
  | .error msg =>
    if msg == "STOP" then
      -- Successful termination with no return data
      .success s.gas ByteArray.empty s.world s.logs
    else if msg.startsWith "RETURN:" then
      -- Successful return with data
      let sizeStr := msg.drop 7
      let size := sizeStr.toNat?.getD 0
      -- Extract return data from memory
      let output := Id.run do
        let mut out := ByteArray.emptyWithCapacity size
        for i in [:size] do
          if i < s.memory.size then
            out := out.push (s.memory.get! i)
          else
            out := out.push 0
        out
      .success s.gas output s.world s.logs
    else if msg.startsWith "REVERT:" then
      -- Revert with data
      let sizeStr := msg.drop 7
      let size := sizeStr.toNat?.getD 0
      let output := Id.run do
        let mut out := ByteArray.emptyWithCapacity size
        for i in [:size] do
          if i < s.memory.size then
            out := out.push (s.memory.get! i)
          else
            out := out.push 0
        out
      .revert s.gas output
    else
      .halt msg

/-! ## Main Entry Points -/

/-- Execute a transaction against a world state -/
def execute (world : WorldState) (tx : ExecutionTx) : ExecResult :=
  let contractAddr := match tx.target with
    | some addr => addr
    | none => Address.zero  -- Simplified: real impl computes CREATE address
  let initialState := initExecution tx world contractAddr
  loop initialState

/-- Execute bytecode directly (for testing) -/
def executeBytecode (bytecode : ByteArray) (calldata : ByteArray := ByteArray.empty)
    (gasLimit : Nat := 1000000) : ExecResult :=
  let tx : ExecutionTx := {
    origin := Address.zero
    caller := Address.zero
    target := some Address.zero
    value := 0
    gasLimit := gasLimit
    gasPrice := 1
    txData := calldata
  }
  let world := WorldState.empty.setAccount Address.zero {
    nonce := 0
    balance := 0
    code := bytecode
    storage := Storage.empty
  }
  execute world tx

/-! ## Examples -/

section Examples

/-- Simple ADD test: PUSH1 0x02 PUSH1 0x03 ADD STOP -/
def simpleAddBytecode : ByteArray :=
  ByteArray.mk #[0x60, 0x02, 0x60, 0x03, 0x01, 0x00]

/-- Return value test: PUSH1 0x42 PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 RETURN -/
def returnValueBytecode : ByteArray :=
  ByteArray.mk #[0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]

end Examples

end LeanEVM.Core.Runtime
