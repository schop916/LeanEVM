import Lean.Data.Json
import Std.Data.HashMap
import LeanEVM.Core.Types

/-!
# Ethereum Test State Parser

This module provides utilities for parsing Ethereum JSON test files into
executable EVM state. It handles hex string parsing and converts between
the JSON test format and internal Lean types.

## Architecture

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│   JSON File     │────▶│  Hex Parsing    │────▶│  setup_state    │
│ (ArithmeticTest)│     │ (strings→bytes) │     │ (build EVMState)│
└─────────────────┘     └─────────────────┘     └─────────────────┘
                                                        │
                                                        ▼
                                               ┌─────────────────┐
                                               │  EVMState       │
                                               │  (ready to run) │
                                               └─────────────────┘
```

## Usage

```lean
let content ← IO.FS.readFile "test.json"
let json ← IO.ofExcept (Json.parse content)
let preState ← IO.ofExcept (fromJson? json)
let evmState ← IO.ofExcept (setup_state preState)
```
-/

namespace LeanEVM.Testing.Parser

open Lean Json

/-! ## Hex String Parsing -/

/-- Convert a single hex character to its numeric value -/
def hexCharToNat (c : Char) : Option Nat :=
  if c ≥ '0' && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if c ≥ 'a' && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if c ≥ 'A' && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a hex string (with or without 0x prefix) to Nat -/
def hexToNat (s : String) : Option Nat := do
  let s := if s.startsWith "0x" then s.drop 2 else s
  if s.isEmpty then return 0
  let rec loop (chars : List Char) (acc : Nat) : Option Nat :=
    match chars with
    | [] => some acc
    | c :: rest => do
      let v ← hexCharToNat c
      loop rest (acc * 16 + v)
  loop s.toList 0

/-- Parse a hex string to ByteArray -/
def hexToByteArray (s : String) : Option ByteArray := do
  let s := if s.startsWith "0x" then s.drop 2 else s
  if s.isEmpty then return ByteArray.empty
  -- Pad to even length if needed
  let s := if s.length % 2 != 0 then "0" ++ s else s
  let rec loop (idx : Nat) (arr : ByteArray) : Option ByteArray :=
    if idx >= s.length then some arr
    else do
      let hi ← hexCharToNat (s.get ⟨idx⟩)
      let lo ← hexCharToNat (s.get ⟨idx + 1⟩)
      loop (idx + 2) (arr.push ((hi * 16 + lo).toUInt8))
  loop 0 ByteArray.empty

/-- Parse hex string to UInt64 -/
def hexToUInt64 (s : String) : Option UInt64 := do
  let n ← hexToNat s
  if n > UInt64.size then none
  else some n.toUInt64

/-- Convert ByteArray to hex string -/
def bytesToHex (bytes : ByteArray) : String :=
  "0x" ++ String.join (bytes.data.toList.map fun b =>
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let toHexChar n := if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)
    String.mk [toHexChar hi, toHexChar lo])

/-- Convert Nat to 32-byte hex string -/
def natToHex32 (n : Nat) : String := Id.run do
  let bytes := natToBytes32 n
  bytesToHex bytes
where
  natToBytes32 (n : Nat) : ByteArray := Id.run do
    let mut bytes := ByteArray.emptyWithCapacity 32
    let mut val := n
    for _ in [:32] do
      bytes := ByteArray.mk #[val.toUInt8] ++ bytes
      val := val / 256
    return bytes

/-! ## JSON Structures (Ethereum Test Format) -/

/-- Account state from JSON test file -/
structure JsonAccount where
  balance : String
  code : String
  nonce : String
  storage : Std.HashMap String String  -- slot → value (hex strings)
deriving Repr

instance : FromJson JsonAccount where
  fromJson? json := do
    let balance ← json.getObjValAs? String "balance"
    let code ← json.getObjValAs? String "code" <|> pure "0x"
    let nonce ← json.getObjValAs? String "nonce" <|> pure "0x0"
    -- Parse storage
    let storageJson ← json.getObjValAs? Json "storage" <|> pure (Json.mkObj [])
    let storage := match storageJson with
      | Json.obj kvs =>
        kvs.toList.foldl (fun m (k, v) =>
          match v with
          | Json.str s => m.insert k s
          | _ => m
        ) {}
      | _ => {}
    return { balance, code, nonce, storage }

/-- Pre-state: map of address → account -/
abbrev JsonPreState := Std.HashMap String JsonAccount

instance : FromJson JsonPreState where
  fromJson? json := do
    match json with
    | Json.obj kvs =>
      let mut m : JsonPreState := {}
      for (addr, acctJson) in kvs.toList do
        let acct ← FromJson.fromJson? acctJson
        m := m.insert addr acct
      return m
    | _ => throw "Expected object for pre-state"

/-- Transaction from JSON test file -/
structure JsonTransaction where
  data : String
  gasLimit : String
  gasPrice : String
  nonce : String
  to : String
  value : String
  secretKey : String
deriving Repr

instance : FromJson JsonTransaction where
  fromJson? json := do
    let data ← json.getObjValAs? String "data" <|> pure "0x"
    let gasLimit ← json.getObjValAs? String "gasLimit" <|> pure "0xffffffff"
    let gasPrice ← json.getObjValAs? String "gasPrice" <|> pure "0x1"
    let nonce ← json.getObjValAs? String "nonce" <|> pure "0x0"
    let to ← json.getObjValAs? String "to" <|> pure "0x"
    let value ← json.getObjValAs? String "value" <|> pure "0x0"
    let secretKey ← json.getObjValAs? String "secretKey" <|> pure "0x"
    return { data, gasLimit, gasPrice, nonce, to, value, secretKey }

/-! ## Internal EVM Types -/

/-- Account in EVM state -/
structure EVMAccount where
  nonce : Nat
  balance : Nat
  code : ByteArray
  storage : Std.HashMap Nat Nat  -- slot → value
deriving Inhabited

/-- Full EVM state -/
structure EVMState where
  accounts : Std.HashMap Nat EVMAccount  -- address → account
  blockNumber : Nat := 0
  timestamp : Nat := 0
  coinbase : Nat := 0
  gasLimit : Nat := 0
  difficulty : Nat := 0
deriving Inhabited

/-! ## State Setup -/

/-- Helper for Option to Except conversion -/
def optionToExcept {α : Type} (msg : String) (o : Option α) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error msg

/-- Convert parsed JSON pre-state into executable EVM state -/
def setup_state (jsonPre : JsonPreState) : Except String EVMState := do
  let mut evmAccounts : Std.HashMap Nat EVMAccount := {}

  for (addrStr, jsonAcc) in jsonPre.toList do
    -- 1. Parse Address
    let addrNat ← (hexToNat addrStr) |> optionToExcept s!"Invalid address hex: {addrStr}"

    -- 2. Parse Balance & Nonce
    let bal ← (hexToNat jsonAcc.balance) |> optionToExcept s!"Invalid balance: {jsonAcc.balance}"
    let nonce ← (hexToNat jsonAcc.nonce) |> optionToExcept s!"Invalid nonce: {jsonAcc.nonce}"

    -- 3. Parse Code
    let code ← (hexToByteArray jsonAcc.code) |> optionToExcept s!"Invalid code: {jsonAcc.code}"

    -- 4. Parse Storage
    let mut storage : Std.HashMap Nat Nat := {}
    for (keyStr, valStr) in jsonAcc.storage.toList do
      let k ← (hexToNat keyStr) |> optionToExcept s!"Invalid storage key: {keyStr}"
      let v ← (hexToNat valStr) |> optionToExcept s!"Invalid storage value: {valStr}"
      storage := storage.insert k v

    -- 5. Construct Account and Insert
    let acc : EVMAccount := { nonce, balance := bal, code, storage }
    evmAccounts := evmAccounts.insert addrNat acc

  return { accounts := evmAccounts }

/-- Setup state with environment info -/
def setup_state_with_env (jsonPre : JsonPreState)
    (blockNum timestamp coinbase gasLimit difficulty : Nat) : Except String EVMState := do
  let state ← setup_state jsonPre
  return { state with
    blockNumber := blockNum
    timestamp := timestamp
    coinbase := coinbase
    gasLimit := gasLimit
    difficulty := difficulty
  }

/-! ## Transaction Parsing -/

/-- Parsed transaction ready for execution -/
structure ParsedTransaction where
  sender : Nat
  to : Option Nat  -- None for contract creation
  value : Nat
  data : ByteArray
  gasLimit : Nat
  gasPrice : Nat
  nonce : Nat

/-- Parse JSON transaction -/
def parseTransaction (tx : JsonTransaction) (senderAddr : Nat) : Except String ParsedTransaction := do
  let to := if tx.to == "" || tx.to == "0x" then none else hexToNat tx.to
  let value ← (hexToNat tx.value) |> optionToExcept s!"Invalid value: {tx.value}"
  let data ← (hexToByteArray tx.data) |> optionToExcept s!"Invalid data: {tx.data}"
  let gasLimit ← (hexToNat tx.gasLimit) |> optionToExcept s!"Invalid gasLimit: {tx.gasLimit}"
  let gasPrice ← (hexToNat tx.gasPrice) |> optionToExcept s!"Invalid gasPrice: {tx.gasPrice}"
  let nonce ← (hexToNat tx.nonce) |> optionToExcept s!"Invalid nonce: {tx.nonce}"
  return { sender := senderAddr, to, value, data, gasLimit, gasPrice, nonce }

/-! ## Post-State Verification -/

/-- Compare two EVM states for equality -/
def statesEqual (s1 s2 : EVMState) : Bool := Id.run do
  -- Check same accounts
  if s1.accounts.size != s2.accounts.size then return false

  for (addr, acc1) in s1.accounts.toList do
    match s2.accounts.get? addr with
    | none => return false
    | some acc2 =>
      if acc1.nonce != acc2.nonce then return false
      if acc1.balance != acc2.balance then return false
      if acc1.code != acc2.code then return false
      if acc1.storage.size != acc2.storage.size then return false
      for (slot, val1) in acc1.storage.toList do
        match acc2.storage.get? slot with
        | none => return false
        | some val2 => if val1 != val2 then return false

  return true

/-- Compute state root hash (placeholder - needs proper MPT implementation) -/
def computeStateRoot (state : EVMState) : ByteArray :=
  -- Placeholder: real implementation needs Merkle Patricia Trie
  ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## Test File Loading -/

/-- Load pre-state from a test file -/
def loadPreState (path : System.FilePath) : IO EVMState := do
  let content ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse content)

  -- Navigate to pre-state (format depends on test type)
  -- For GeneralStateTests: testName -> pre
  let preJson ← match json with
    | Json.obj kvs =>
      match kvs.toList.head? with
      | some (_, testObj) => IO.ofExcept (testObj.getObjValAs? Json "pre")
      | none => throw (IO.userError "Empty test file")
    | _ => throw (IO.userError "Expected object at top level")

  let preState ← IO.ofExcept (FromJson.fromJson? preJson : Except String JsonPreState)
  IO.ofExcept (setup_state preState)

/-! ## Main Test Loader -/

/-- Load and setup a complete test -/
def loadTest (path : System.FilePath) : IO (EVMState × ParsedTransaction) := do
  let content ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse content)

  match json with
  | Json.obj kvs =>
    match kvs.toList.head? with
    | some (testName, testObj) =>
      IO.println s!"Loading test: {testName}"

      -- Parse pre-state
      let preJson ← IO.ofExcept (testObj.getObjValAs? Json "pre")
      let preState ← IO.ofExcept (FromJson.fromJson? preJson : Except String JsonPreState)
      let evmState ← IO.ofExcept (setup_state preState)

      -- Parse transaction
      let txJson ← IO.ofExcept (testObj.getObjValAs? Json "transaction")
      let jsonTx ← IO.ofExcept (FromJson.fromJson? txJson : Except String JsonTransaction)

      -- Get sender address from secret key (simplified - real impl needs ECDSA)
      let sender ← IO.ofExcept ((hexToNat jsonTx.secretKey) |> optionToExcept "Invalid secret key")
      let tx ← IO.ofExcept (parseTransaction jsonTx sender)

      return (evmState, tx)
    | none => throw (IO.userError "Empty test file")
  | _ => throw (IO.userError "Expected object at top level")

/-! ## Example Usage -/

/-- Example: Load a test file and display state -/
def example_load (path : String) : IO Unit := do
  let evmState ← loadPreState (System.FilePath.mk path)
  IO.println s!"Loaded state with {evmState.accounts.size} accounts"

  for (addr, acc) in evmState.accounts.toList do
    IO.println s!"  Account {natToHex32 addr}:"
    IO.println s!"    Balance: {acc.balance}"
    IO.println s!"    Nonce: {acc.nonce}"
    IO.println s!"    Code: {acc.code.size} bytes"
    IO.println s!"    Storage: {acc.storage.size} slots"

end LeanEVM.Testing.Parser
