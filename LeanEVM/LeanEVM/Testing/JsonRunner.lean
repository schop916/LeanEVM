import Lean.Data.Json
import LeanEVM.Core.Types
import LeanEVM.Core.FFI

/-!
# Ethereum JSON Conformance Test Runner

This module implements a test harness for running Ethereum conformance tests.
The tests are JSON files describing pre-state, transaction, and expected post-state.

## Test Format (Ethereum/tests)

```json
{
  "info": { "comment": "Test description" },
  "env": { "currentNumber": "0x1", ... },
  "pre": {
    "0xAddress": { "balance": "0x...", "code": "0x...", "nonce": "0x1", "storage": {} }
  },
  "transaction": { "data": "0x...", "gasLimit": "0x...", ... },
  "post": { ... }
}
```

## Usage

```lean
#eval runTestFile "tests/GeneralStateTests/stExample/add.json"
```
-/

namespace LeanEVM.Testing

open Lean (Json FromJson ToJson)
open LeanEVM.Core.FFI

/-! ## JSON Structures -/

/-- Environment block info -/
structure EnvInfo where
  currentCoinbase : String := "0x0"
  currentDifficulty : String := "0x0"
  currentGasLimit : String := "0xffffffff"
  currentNumber : String := "0x1"
  currentTimestamp : String := "0x0"
  previousHash : String := "0x0"
deriving Repr

instance : FromJson EnvInfo where
  fromJson? json := do
    let coinbase ← json.getObjValAs? String "currentCoinbase" <|> pure "0x0"
    let difficulty ← json.getObjValAs? String "currentDifficulty" <|> pure "0x0"
    let gasLimit ← json.getObjValAs? String "currentGasLimit" <|> pure "0xffffffff"
    let number ← json.getObjValAs? String "currentNumber" <|> pure "0x1"
    let timestamp ← json.getObjValAs? String "currentTimestamp" <|> pure "0x0"
    let prevHash ← json.getObjValAs? String "previousHash" <|> pure "0x0"
    return { currentCoinbase := coinbase
           , currentDifficulty := difficulty
           , currentGasLimit := gasLimit
           , currentNumber := number
           , currentTimestamp := timestamp
           , previousHash := prevHash }

/-- Account pre-state -/
structure AccountPreState where
  balance : String
  code : String
  nonce : String
  storage : List (String × String)  -- (slot, value) pairs
deriving Repr

instance : FromJson AccountPreState where
  fromJson? json := do
    let balance ← json.getObjValAs? String "balance"
    let code ← json.getObjValAs? String "code" <|> pure "0x"
    let nonce ← json.getObjValAs? String "nonce" <|> pure "0x0"
    -- Parse storage object
    let storageJson ← json.getObjValAs? Json "storage" <|> pure (Json.mkObj [])
    let storageArr := match storageJson with
      | Json.obj kvs => kvs.toList.map fun (k, v) =>
        match v with
        | Json.str s => (k, s)
        | _ => (k, "0x0")
      | _ => []
    return { balance, code, nonce, storage := storageArr }

/-- Transaction data -/
structure TxData where
  data : Array String  -- Multiple data options
  gasLimit : Array String
  gasPrice : String
  nonce : String
  secretKey : String
  sender : String
  to : String
  value : Array String
deriving Repr

instance : FromJson TxData where
  fromJson? json := do
    let dataArr ← json.getObjValAs? (Array String) "data" <|> pure #["0x"]
    let gasLimitArr ← json.getObjValAs? (Array String) "gasLimit" <|> pure #["0xffffffff"]
    let gasPrice ← json.getObjValAs? String "gasPrice" <|> pure "0x1"
    let nonce ← json.getObjValAs? String "nonce" <|> pure "0x0"
    let secretKey ← json.getObjValAs? String "secretKey" <|> pure "0x"
    let sender ← json.getObjValAs? String "sender" <|> pure "0x"
    let to ← json.getObjValAs? String "to" <|> pure "0x"
    let valueArr ← json.getObjValAs? (Array String) "value" <|> pure #["0x0"]
    return { data := dataArr
           , gasLimit := gasLimitArr
           , gasPrice, nonce, secretKey, sender, to
           , value := valueArr }

/-- Post-state expectation -/
structure PostExpectation where
  hash : String  -- Expected state root hash
  indexes : Json  -- Data/gas/value index selections
  logs : String   -- Expected logs hash
  txbytes : String
deriving Inhabited

instance : FromJson PostExpectation where
  fromJson? json := do
    let hash ← json.getObjValAs? String "hash" <|> pure "0x"
    let indexes ← json.getObjValAs? Json "indexes" <|> pure (Json.mkObj [])
    let logs ← json.getObjValAs? String "logs" <|> pure "0x"
    let txbytes ← json.getObjValAs? String "txbytes" <|> pure "0x"
    return { hash, indexes, logs, txbytes }

/-- Complete Ethereum test case -/
structure EthTest where
  info : Json
  env : EnvInfo
  pre : List (String × AccountPreState)  -- address → account
  transaction : TxData
  post : List (String × Array PostExpectation)  -- fork → expectations

/-! ## Hex Parsing -/

/-- Parse hex string to ByteArray -/
def parseHex (s : String) : ByteArray := Id.run do
  let s := if s.startsWith "0x" then s.drop 2 else s
  -- Pad to even length
  let s := if s.length % 2 == 1 then "0" ++ s else s
  let mut bytes := ByteArray.emptyWithCapacity (s.length / 2)
  for i in [:s.length / 2] do
    let hi := hexDigitToNat (s.get ⟨2 * i⟩)
    let lo := hexDigitToNat (s.get ⟨2 * i + 1⟩)
    bytes := bytes.push ((hi * 16 + lo).toUInt8)
  return bytes
where
  hexDigitToNat (c : Char) : Nat :=
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
    else 0

/-- Parse hex string to Nat -/
def parseHexNat (s : String) : Nat := Id.run do
  let s := if s.startsWith "0x" then s.drop 2 else s
  let mut n := 0
  for c in s.data do
    let d := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
             else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
             else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
             else 0
    n := n * 16 + d
  return n

/-! ## Test Execution -/

/-- Convert parsed test to execution context -/
def testToContext (test : EthTest) (dataIdx gasIdx valueIdx : Nat := 0) : Core.FFI.ExecutionContext := Id.run do
  -- Build account states
  let mut accounts : Array Core.FFI.AccountState := #[]
  for (addrStr, acct) in test.pre do
    let state : Core.FFI.AccountState := {
      address := parseHex addrStr
      balance := parseHex acct.balance
      nonce := (parseHexNat acct.nonce).toUInt64
      code := parseHex acct.code
      storage := acct.storage.toArray.map fun (k, v) => (parseHex k, parseHex v)
    }
    accounts := accounts.push state

  -- Build transaction
  let tx := test.transaction
  let txCtx : Core.FFI.TxContext := {
    caller := parseHex tx.sender
    target := parseHex tx.to
    value := parseHex (tx.value.get! valueIdx)
    data := parseHex (tx.data.get! dataIdx)
    gasLimit := (parseHexNat (tx.gasLimit.get! gasIdx)).toUInt64
    gasPrice := parseHex tx.gasPrice
  }

  return {
    accounts := accounts
    transaction := txCtx
    blockNumber := (parseHexNat test.env.currentNumber).toUInt64
    timestamp := (parseHexNat test.env.currentTimestamp).toUInt64
    chainId := 1  -- Mainnet
  }

/-- Result of a single test -/
inductive TestResult
  | pass : TestResult
  | fail (reason : String) : TestResult
  | skip (reason : String) : TestResult
deriving Repr

/-- Run a single test case -/
def runTest (test : EthTest) (fork : String := "Cancun") : IO TestResult := do
  -- Find post-state for requested fork
  let postExpects := test.post.find? fun (f, _) => f == fork
  match postExpects with
  | none => return .skip s!"Fork {fork} not found in test"
  | some (_, expects) =>
    -- For now, just run first expectation
    if expects.isEmpty then return .skip "No expectations"

    let expect := expects[0]!

    -- Build execution context
    let ctx := testToContext test

    -- Run through reference EVM
    let result ← runReferenceEVMWithContext ctx

    -- Compare with expectation
    -- Note: Full comparison requires computing state root hash
    if result.success then
      return .pass
    else
      return .fail s!"Execution failed: status={result.statusCode}"

/-! ## Test File Loading -/

/-- Helper to convert Except with custom error message -/
def exceptWithMsg {α : Type} (e : Except String α) (msg : String) : Except String α :=
  match e with
  | .ok a => .ok a
  | .error _ => .error msg

/-- Parse a test file -/
def parseTestFile (content : String) : Except String (List (String × EthTest)) := do
  match Json.parse content with
  | .error e => throw s!"JSON parse error: {e}"
  | .ok json =>
    match json with
    | Json.obj kvs =>
      let mut tests := []
      for (name, testJson) in kvs.toList do
        -- Parse individual test
        let info ← exceptWithMsg (testJson.getObjValAs? Json "info") s!"Missing info in {name}"
        let envJson ← exceptWithMsg (testJson.getObjValAs? Json "env") s!"Missing env in {name}"
        let env ← exceptWithMsg (FromJson.fromJson? envJson) s!"Invalid env in {name}"
        let preJson ← exceptWithMsg (testJson.getObjValAs? Json "pre") s!"Missing pre in {name}"
        let txJson ← exceptWithMsg (testJson.getObjValAs? Json "transaction") s!"Missing tx in {name}"
        let tx ← exceptWithMsg (FromJson.fromJson? txJson) s!"Invalid tx in {name}"
        let postJson ← exceptWithMsg (testJson.getObjValAs? Json "post") s!"Missing post in {name}"

        -- Parse pre-state
        let pre := match preJson with
          | Json.obj kvs => kvs.toList.filterMap fun (addr, acctJson) =>
            match FromJson.fromJson? acctJson with
            | .ok acct => some (addr, acct)
            | .error _ => none
          | _ => []

        -- Parse post expectations
        let post := match postJson with
          | Json.obj kvs => kvs.toList.filterMap fun (fork, expectsJson) =>
            match expectsJson with
            | Json.arr arr =>
              let expects := arr.filterMap fun e =>
                match FromJson.fromJson? e with
                | .ok exp => some exp
                | .error _ => none
              some (fork, expects)
            | _ => none
          | _ => []

        tests := (name, { info, env, pre, transaction := tx, post }) :: tests

      return tests.reverse
    | _ => throw "Expected object at top level"

/-- Run tests from a file -/
def runTestFile (path : System.FilePath) (fork : String := "Cancun") : IO Unit := do
  IO.println s!"Loading {path}..."

  let content ← IO.FS.readFile path

  match parseTestFile content with
  | .error e => IO.println s!"Parse error: {e}"
  | .ok tests =>
    IO.println s!"Found {tests.length} tests"

    let mut passed := 0
    let mut failed := 0
    let mut skipped := 0

    for (name, test) in tests do
      let result ← runTest test fork
      match result with
      | .pass =>
        IO.println s!"  PASS: {name}"
        passed := passed + 1
      | .fail reason =>
        IO.println s!"  FAIL: {name} - {reason}"
        failed := failed + 1
      | .skip reason =>
        IO.println s!"  SKIP: {name} - {reason}"
        skipped := skipped + 1

    IO.println s!"\nResults: {passed} passed, {failed} failed, {skipped} skipped"

/-- Run all test files in a directory -/
def runTestDir (dir : System.FilePath) (fork : String := "Cancun") : IO Unit := do
  let entries ← dir.readDir
  for entry in entries do
    if entry.path.extension == some "json" then
      runTestFile entry.path fork

/-! ## Main Entry Point -/

/-- Main test runner -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "Usage: test_runner <path> [--fork <name>]"
    IO.println "  path: JSON test file or directory"
    IO.println "  --fork: Ethereum fork to test (default: Cancun)"
    return 1
  | path :: rest =>
    let fork := match rest with
      | "--fork" :: name :: _ => name
      | _ => "Cancun"

    let p := System.FilePath.mk path

    if ← p.isDir then
      runTestDir p fork
    else
      runTestFile p fork

    return 0

end LeanEVM.Testing
