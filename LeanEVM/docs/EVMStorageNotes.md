# EVM Storage Layout Notes

Source: https://wavey.info/posts/2025/reverse-engineering-evm-storage/

## Relevance to LeanEVM

This article covers how Solidity organizes data in EVM storage, which is essential for:
1. Verifying storage-related opcodes (SLOAD, SSTORE)
2. Modeling realistic smart contract state
3. Understanding the security properties of storage layout

## Key Technical Details

### 1. Storage Slots (32 bytes each)

EVM storage is a key-value store where both keys and values are 256-bit words.

```
Storage: slot (uint256) → value (uint256)
```

### 2. Fixed-Size Variable Packing

Multiple small variables can share a single 32-byte slot:

```
Slot 0: | address (20 bytes) | bool (1 byte) | uint32 (4 bytes) | padding (7 bytes) |
```

**Implication for verification**: Need to model bit-level extraction for packed values.

### 3. Mapping Storage Layout

**Formula**: `storage[keccak256(key ++ baseSlot)]`

Where:
- `key`: The mapping key (padded to 32 bytes)
- `baseSlot`: The declared slot of the mapping (padded to 32 bytes)
- `++`: Concatenation (64 bytes total)

```lean
-- Potential LeanEVM model:
def mappingSlot (baseSlot : UInt256) (key : UInt256) : UInt256 :=
  keccak256 (key.toBytes ++ baseSlot.toBytes)
```

**Key property**: This is a one-way function - given a storage slot, the key is unrecoverable without preimage knowledge.

### 4. Nested Mappings

For `mapping(A => mapping(B => C))`:

```
slot1 = keccak256(keyA ++ baseSlot)
slot2 = keccak256(keyB ++ slot1)
value = storage[slot2]
```

**Verification implication**: Need to model chained hash computations.

### 5. Dynamic Arrays

- **Length**: Stored at `baseSlot`
- **Data start**: `keccak256(baseSlot)`
- **Element N**: `dataStart + N * elementSize`

```lean
def arrayElement (baseSlot : UInt256) (index : Nat) (elemSize : Nat) : UInt256 :=
  let dataStart := keccak256 baseSlot.toBytes
  dataStart + index * elemSize
```

### 6. Dynamic Strings (Solidity-specific)

**Short strings** (< 32 bytes):
- Content + length in same slot
- Lowest byte = `length * 2`

**Long strings** (≥ 32 bytes):
- Base slot stores `length * 2 + 1`
- Content at `keccak256(baseSlot)` spanning multiple slots

**Detection**: Check lowest bit of base slot value
- 0 → short string
- 1 → long string

### 7. Structs with Dynamic Fields

Arrays of structs with dynamic fields (like strings) create complex layouts:
- Fixed fields packed within struct slots
- Dynamic fields stored at computed locations

## Implications for LeanEVM

### Current Model Gaps

Our current `Storage` type is simplified:
```lean
abbrev Storage := Nat → Nat  -- slot → value
```

For realistic Solidity contract verification, we might need:

1. **Keccak256 modeling**: Abstract or concrete hash function
2. **Packed storage access**: Bit-level read/write operations
3. **Array bounds checking**: Verify index < length
4. **Mapping collision resistance**: Prove distinct keys → distinct slots

### Potential Extensions

```lean
-- Enhanced storage model
structure SolidityStorage where
  raw : UInt256 → UInt256
  -- Track known mappings for verification
  mappingPreimages : List (UInt256 × UInt256 × UInt256)  -- (slot, key, baseSlot)

-- Mapping read with preimage tracking
def readMapping (s : SolidityStorage) (base : UInt256) (key : UInt256) : UInt256 :=
  let slot := keccak256 (key ++ base)
  s.raw slot

-- Invariant: mapping slots don't collide with base slots
def mappingSlotDisjoint (base1 base2 : UInt256) (key1 key2 : UInt256) : Prop :=
  (base1 ≠ base2 ∨ key1 ≠ key2) →
  keccak256 (key1 ++ base1) ≠ keccak256 (key2 ++ base2)
```

### Verification Properties

1. **Storage isolation**: Different mappings don't interfere
2. **Array bounds**: Index access within allocated length
3. **Packing correctness**: Bit operations preserve adjacent fields
4. **Hash collision freedom**: Assumed for keccak256

## Security Considerations

1. **Storage slot collisions**: Malicious contracts might try to access unintended slots
2. **Dirty upper bits**: When reading packed values, upper bits must be masked
3. **Length manipulation**: Array length modifications must update storage atomically

## References

- Solidity Storage Layout: https://docs.soliditylang.org/en/latest/internals/layout_in_storage.html
- EIP-1967 (Proxy Storage Slots): Uses specific hash-derived slots for proxy patterns
