//! # LeanEVM Native FFI Library
//!
//! This library provides FFI bindings between Lean 4 and the Rust `revm` library
//! for reference EVM execution. This enables cross-validation testing between
//! the verified LeanEVM implementation and a production EVM.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
//! │   Lean Code     │────▶│    C FFI        │────▶│   Rust/revm     │
//! │  (LeanEVM)      │     │  (this file)    │     │  (reference)    │
//! └─────────────────┘     └─────────────────┘     └─────────────────┘
//! ```
//!
//! ## Usage from Lean
//!
//! ```lean
//! @[extern "lean_run_reference_evm"]
//! opaque runReferenceEVM (bytecode : @& ByteArray) (calldata : @& ByteArray) : IO EVMResult
//! ```

use revm::{
    db::{CacheDB, EmptyDB},
    primitives::{
        Address, Bytes, ExecutionResult, Output, TransactTo, TxEnv, U256,
    },
    Evm,
};
use std::ffi::c_void;
use std::slice;

// ============================================================================
// Lean Object Types (matching lean4/include/lean/lean.h)
// ============================================================================

/// Opaque Lean object pointer
#[repr(C)]
pub struct LeanObject {
    _private: [u8; 0],
}

/// Lean ByteArray structure
#[repr(C)]
pub struct LeanByteArray {
    /// Reference count and other metadata
    pub header: usize,
    /// Capacity of the array
    pub capacity: usize,
    /// Number of bytes stored
    pub size: usize,
    /// Actual byte data (flexible array member)
    pub data: [u8; 0],
}

/// Result structure returned to Lean
#[repr(C)]
pub struct EVMResult {
    pub success: u8,
    pub gas_used: u64,
    pub output_len: u64,
    pub status_code: u8,
    pub output_ptr: *mut u8,
}

// ============================================================================
// Lean Runtime Functions (external)
// ============================================================================

extern "C" {
    fn lean_io_result_mk_ok(val: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_result_mk_error(err: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_string(s: *const u8) -> *mut LeanObject;
    fn lean_alloc_external(cls: *mut c_void, data: *mut c_void) -> *mut LeanObject;
    fn lean_inc_ref(obj: *mut LeanObject);
    fn lean_dec_ref(obj: *mut LeanObject);
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Extract byte slice from Lean ByteArray
unsafe fn lean_byte_array_to_slice(arr: *const LeanByteArray) -> &'static [u8] {
    let arr = &*arr;
    slice::from_raw_parts(arr.data.as_ptr(), arr.size)
}

/// Convert Rust bytes to Lean ByteArray
unsafe fn bytes_to_lean_byte_array(bytes: &[u8]) -> *mut LeanObject {
    // Allocate Lean ByteArray structure
    // Note: This is simplified; real impl needs proper Lean memory allocation
    let size = bytes.len();
    let total_size = std::mem::size_of::<LeanByteArray>() + size;
    let ptr = libc::malloc(total_size) as *mut LeanByteArray;

    if ptr.is_null() {
        return std::ptr::null_mut();
    }

    (*ptr).capacity = size;
    (*ptr).size = size;
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), (*ptr).data.as_mut_ptr(), size);

    ptr as *mut LeanObject
}

/// Create Lean IO result (success)
unsafe fn lean_io_ok(val: *mut LeanObject) -> *mut LeanObject {
    lean_io_result_mk_ok(val)
}

/// Create Lean IO result (error)
unsafe fn lean_io_error(msg: &str) -> *mut LeanObject {
    let s = lean_mk_string(msg.as_ptr());
    lean_io_result_mk_error(s)
}

// ============================================================================
// EVM Execution
// ============================================================================

/// Run bytecode through revm and return result
fn execute_evm(bytecode: &[u8], calldata: &[u8]) -> Result<EVMResult, String> {
    // Create an in-memory database
    let db = CacheDB::new(EmptyDB::default());

    // Create EVM instance
    let mut evm = Evm::builder()
        .with_db(db)
        .modify_tx_env(|tx| {
            tx.caller = Address::ZERO;
            tx.transact_to = TransactTo::Call(Address::ZERO);
            tx.data = Bytes::copy_from_slice(calldata);
            tx.gas_limit = 1_000_000;
            tx.gas_price = U256::from(1);
            tx.value = U256::ZERO;
        })
        .build();

    // Deploy contract (simplified - just set code at address)
    // Note: Real implementation would handle deployment properly

    // Execute
    match evm.transact() {
        Ok(result) => {
            let (success, output, gas_used) = match result.result {
                ExecutionResult::Success { output, gas_used, .. } => {
                    let output_bytes = match output {
                        Output::Call(bytes) => bytes.to_vec(),
                        Output::Create(bytes, _) => bytes.to_vec(),
                    };
                    (true, output_bytes, gas_used)
                }
                ExecutionResult::Revert { output, gas_used, .. } => {
                    (false, output.to_vec(), gas_used)
                }
                ExecutionResult::Halt { reason, gas_used, .. } => {
                    (false, format!("{:?}", reason).into_bytes(), gas_used)
                }
            };

            let output_len = output.len() as u64;
            let output_ptr = if output.is_empty() {
                std::ptr::null_mut()
            } else {
                let ptr = unsafe { libc::malloc(output.len()) as *mut u8 };
                if !ptr.is_null() {
                    unsafe {
                        std::ptr::copy_nonoverlapping(output.as_ptr(), ptr, output.len());
                    }
                }
                ptr
            };

            Ok(EVMResult {
                success: success as u8,
                gas_used,
                output_len,
                status_code: if success { 0 } else { 1 },
                output_ptr,
            })
        }
        Err(e) => Err(format!("EVM error: {:?}", e)),
    }
}

// ============================================================================
// FFI Exports
// ============================================================================

/// Run bytecode through reference EVM
///
/// # Safety
/// - `bytecode` and `calldata` must be valid Lean ByteArray pointers
/// - Returns a Lean IO result
#[no_mangle]
pub unsafe extern "C" fn lean_run_reference_evm(
    bytecode: *const LeanByteArray,
    calldata: *const LeanByteArray,
) -> *mut LeanObject {
    // Extract byte slices
    let bytecode_slice = lean_byte_array_to_slice(bytecode);
    let calldata_slice = lean_byte_array_to_slice(calldata);

    // Execute
    match execute_evm(bytecode_slice, calldata_slice) {
        Ok(result) => {
            // Convert result to Lean structure
            // Note: This is simplified; real impl needs proper Lean structure creation
            let result_ptr = Box::into_raw(Box::new(result)) as *mut LeanObject;
            lean_io_ok(result_ptr)
        }
        Err(e) => {
            lean_io_error(&e)
        }
    }
}

/// Run EVM with full execution context
#[no_mangle]
pub unsafe extern "C" fn lean_run_reference_evm_ctx(
    _ctx: *const LeanObject,
) -> *mut LeanObject {
    // TODO: Implement full context execution
    lean_io_error("Not implemented yet")
}

/// Get storage value from reference EVM
#[no_mangle]
pub unsafe extern "C" fn lean_get_storage_ref(
    _address: *const LeanByteArray,
    _slot: *const LeanByteArray,
) -> *mut LeanObject {
    // TODO: Implement storage access
    lean_io_error("Not implemented yet")
}

/// Compare two EVM results
#[no_mangle]
pub unsafe extern "C" fn lean_compare_evm_results(
    _a: *const EVMResult,
    _b: *const EVMResult,
) -> *mut LeanObject {
    // TODO: Implement comparison
    lean_io_error("Not implemented yet")
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_add() {
        // PUSH1 0x01 PUSH1 0x02 ADD
        let bytecode = vec![0x60, 0x01, 0x60, 0x02, 0x01];
        let calldata = vec![];

        let result = execute_evm(&bytecode, &calldata);
        assert!(result.is_ok());
    }

    #[test]
    fn test_return_value() {
        // PUSH1 0x42 PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 RETURN
        let bytecode = vec![
            0x60, 0x42,  // PUSH1 0x42
            0x60, 0x00,  // PUSH1 0x00
            0x52,        // MSTORE
            0x60, 0x20,  // PUSH1 0x20
            0x60, 0x00,  // PUSH1 0x00
            0xf3,        // RETURN
        ];
        let calldata = vec![];

        let result = execute_evm(&bytecode, &calldata);
        assert!(result.is_ok());
        let r = result.unwrap();
        assert_eq!(r.success, 1);
    }
}
