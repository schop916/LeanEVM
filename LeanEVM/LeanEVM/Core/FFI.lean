import LeanEVM.Core.Types

/-!
# Foreign Function Interface for Reference EVM Testing

This module provides FFI bindings to external EVM implementations (Rust/C++)
for cross-validation testing. By running the same bytecode through both
LeanEVM and a reference implementation, we can verify correctness.

## Architecture

1. **Lean Side**: Exposes functions via `@[export]` and calls external via `@[extern]`
2. **Native Side**: Rust library using `revm` for reference execution
3. **Comparison**: Test harness compares results and reports divergences

## Usage

```lean
-- Run bytecode through reference EVM
let ref_result := runReferenceEVM bytecode calldata
-- Compare with LeanEVM result
let lean_result := LeanEVM.execute vm_state bytecode
assert (ref_result.success == lean_result.isOk)
```
-/

namespace LeanEVM.Core.FFI

/-! ## Result Structures -/

/-- Result from EVM execution -/
structure EVMResult where
  /-- Whether execution succeeded -/
  success : Bool
  /-- Gas consumed during execution -/
  gasUsed : UInt64
  /-- Return data length -/
  outputLen : UInt64
  /-- Status code (0 = success, 1 = revert, 2 = error) -/
  statusCode : UInt8
  /-- Return data as byte array -/
  output : ByteArray
deriving Inhabited

/-- Account state for test setup -/
structure AccountState where
  /-- Account address -/
  address : ByteArray  -- 20 bytes
  /-- Account balance in wei -/
  balance : ByteArray  -- 32 bytes (U256)
  /-- Account nonce -/
  nonce : UInt64
  /-- Contract bytecode (empty for EOA) -/
  code : ByteArray
  /-- Storage key-value pairs -/
  storage : Array (ByteArray × ByteArray)  -- (key, value) pairs
deriving Inhabited

/-- Transaction context for execution -/
structure TxContext where
  /-- Sender address -/
  caller : ByteArray
  /-- Target address (empty for contract creation) -/
  target : ByteArray
  /-- Value in wei -/
  value : ByteArray
  /-- Calldata -/
  data : ByteArray
  /-- Gas limit -/
  gasLimit : UInt64
  /-- Gas price -/
  gasPrice : ByteArray
deriving Inhabited

/-- Full execution context -/
structure ExecutionContext where
  /-- Pre-state accounts -/
  accounts : Array AccountState
  /-- Transaction to execute -/
  transaction : TxContext
  /-- Block number -/
  blockNumber : UInt64
  /-- Block timestamp -/
  timestamp : UInt64
  /-- Chain ID -/
  chainId : UInt64
deriving Inhabited

/-! ## External Function Declarations -/

/-- Run bytecode through reference EVM (revm) -/
@[extern "lean_run_reference_evm"]
opaque runReferenceEVM (bytecode : @& ByteArray) (calldata : @& ByteArray) : IO EVMResult

/-- Run with full execution context -/
@[extern "lean_run_reference_evm_ctx"]
opaque runReferenceEVMWithContext (ctx : @& ExecutionContext) : IO EVMResult

/-- Get storage value from reference EVM -/
@[extern "lean_get_storage_ref"]
opaque getStorageRef (address : @& ByteArray) (slot : @& ByteArray) : IO ByteArray

/-- Compare two EVM results for equality -/
@[extern "lean_compare_evm_results"]
opaque compareEVMResults (a : @& EVMResult) (b : @& EVMResult) : IO Bool

/-! ## Exported Functions (for native code to call) -/

/-- Export LeanEVM execution for comparison -/
@[export lean_execute_bytecode]
def executeBytecode (bytecode : ByteArray) (calldata : ByteArray) : EVMResult :=
  -- Placeholder: integrate with actual LeanEVM execution
  { success := true
  , gasUsed := 0
  , outputLen := 0
  , statusCode := 0
  , output := ByteArray.empty }

/-! ## Consistency Testing -/

/-- Test that LeanEVM and reference EVM produce same result -/
def testConsistency (bytecode : ByteArray) (calldata : ByteArray := ByteArray.empty) : IO Bool := do
  -- Run through reference EVM
  let refResult ← runReferenceEVM bytecode calldata

  -- Run through LeanEVM
  let leanResult := executeBytecode bytecode calldata

  -- Compare results
  if refResult.success != leanResult.success then
    IO.eprintln s!"Divergence: success mismatch (ref={refResult.success}, lean={leanResult.success})"
    return false

  if refResult.gasUsed != leanResult.gasUsed then
    IO.eprintln s!"Divergence: gas mismatch (ref={refResult.gasUsed}, lean={leanResult.gasUsed})"
    return false

  if refResult.output != leanResult.output then
    IO.eprintln s!"Divergence: output mismatch"
    return false

  return true

/-- Run consistency test on multiple bytecode samples -/
def runConsistencyTests (samples : Array ByteArray) : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0

  for bytecode in samples do
    let result ← testConsistency bytecode
    if result then
      passed := passed + 1
    else
      failed := failed + 1

  return (passed, failed)

/-! ## Fuzzing Support -/

/-- Generate random bytecode for fuzzing -/
def generateRandomBytecode (len : Nat) : IO ByteArray := do
  let mut bytes := ByteArray.emptyWithCapacity len
  for _ in [:len] do
    let byte ← IO.rand 0 255
    bytes := bytes.push byte.toUInt8
  return bytes

/-- Fuzz test with random bytecode -/
def fuzzTest (iterations : Nat) : IO Unit := do
  IO.println s!"Running {iterations} fuzz iterations..."
  let mut divergences := 0

  for i in [:iterations] do
    -- Generate random bytecode (16-256 bytes)
    let len ← IO.rand 16 256
    let bytecode ← generateRandomBytecode len

    -- Test consistency
    let consistent ← testConsistency bytecode
    if !consistent then
      divergences := divergences + 1
      IO.println s!"Divergence at iteration {i}"

  IO.println s!"Fuzz complete: {divergences}/{iterations} divergences"

/-! ## Helpers -/

/-- Convert 32-byte array to Nat (big-endian) -/
def bytesToNat (bytes : ByteArray) : Nat := Id.run do
  let mut n := 0
  for b in bytes.data do
    n := n * 256 + b.toNat
  return n

/-- Convert Nat to 32-byte array (big-endian) -/
def natToBytes32 (n : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity 32
  let mut val := n
  for _ in [:32] do
    bytes := ByteArray.mk #[val.toUInt8] ++ bytes
    val := val / 256
  return bytes

/-- Convert address (20 bytes) to hex string -/
def addressToHex (addr : ByteArray) : String :=
  "0x" ++ String.join (addr.data.toList.map fun b =>
    let hex := Nat.toDigits 16 b.toNat
    if hex.length < 2 then "0" ++ String.mk hex else String.mk hex)

end LeanEVM.Core.FFI
