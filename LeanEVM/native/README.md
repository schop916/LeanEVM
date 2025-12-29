# LeanEVM Native FFI Library

This directory contains the Rust native library for LeanEVM reference testing.
It uses [revm](https://github.com/bluealloy/revm) as the reference EVM implementation.

## Building

### Prerequisites

1. Rust (1.70+): https://rustup.rs
2. Lean 4: Already installed with elan

### Build Commands

```bash
# Build release version
cargo build --release

# Run tests
cargo test

# Generate C headers (if needed)
cargo install cbindgen
cbindgen --output lean_evm_native.h
```

### Output

The build produces:
- `target/release/liblean_evm_native.a` (static library)
- `target/release/liblean_evm_native.dylib` (macOS dynamic library)
- `target/release/liblean_evm_native.so` (Linux dynamic library)

## Integration with Lean

### 1. Add to lakefile.lean

```lean
-- In lakefile.lean
target nativeLib : System.FilePath := do
  let native ← inputFile <| "native" / "target" / "release" / "liblean_evm_native.a"
  return native
```

### 2. Link in Lean

The `@[extern]` declarations in `LeanEVM/Core/FFI.lean` automatically link
against functions exported by this library.

## FFI Functions

| Lean Function | C Function | Description |
|--------------|------------|-------------|
| `runReferenceEVM` | `lean_run_reference_evm` | Run bytecode through revm |
| `runReferenceEVMWithContext` | `lean_run_reference_evm_ctx` | Run with full context |
| `getStorageRef` | `lean_get_storage_ref` | Get storage value |
| `compareEVMResults` | `lean_compare_evm_results` | Compare results |

## Testing

```bash
# Run Rust tests
cargo test

# Run integration tests (from project root)
lake build LeanEVM
lake exe leanevmTest
```

## Adding New Functions

1. Add the Rust implementation in `src/lib.rs`
2. Mark with `#[no_mangle]` and `extern "C"`
3. Add corresponding `@[extern]` in `LeanEVM/Core/FFI.lean`
4. Rebuild both Rust and Lean

## Troubleshooting

### "undefined symbol" errors
Ensure the library is built and linked correctly:
```bash
nm target/release/liblean_evm_native.a | grep lean_
```

### Memory issues
The FFI layer handles Lean object references. Ensure:
- Use `lean_inc_ref` when storing Lean objects
- Use `lean_dec_ref` when releasing Lean objects
- Don't free memory allocated by Lean

### Debugging
Build with debug symbols:
```bash
RUSTFLAGS="-g" cargo build
```
