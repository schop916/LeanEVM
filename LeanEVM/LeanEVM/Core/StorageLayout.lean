import LeanEVM.Core.Types

/-!
# Solidity Storage Layout Model

Models how Solidity computes storage slots for complex types:
- Mappings: `keccak256(key ++ baseSlot)`
- Dynamic arrays: length at `baseSlot`, data at `keccak256(baseSlot)`
- Nested structures: chained hash computations

## References
- https://docs.soliditylang.org/en/latest/internals/layout_in_storage.html
- https://wavey.info/posts/2025/reverse-engineering-evm-storage/
-/

namespace LeanEVM.StorageLayout

open LeanEVM

/-! ## Abstract Keccak256

We model keccak256 abstractly as a function with assumed properties.
For verification, we assume collision resistance without computing actual hashes.
-/

/-- Abstract keccak256 hash function -/
opaque keccak256 : List UInt8 → Nat

/-- Convert a 256-bit natural number to 32 bytes (big-endian) -/
def toBytes32 (n : Nat) : List UInt8 :=
  List.range 32 |>.reverse |>.map fun i =>
    (n / (256 ^ i) % 256).toUInt8

/-! ### Byte Conversion Injectivity

We prove that `toBytes32` is injective for values < 2^256.

The key insight is that if two numbers have the same base-256 digits,
they must be equal. We prove this by showing that knowing all digits
uniquely determines the number.
-/

/-- Reconstruct a number from big-endian bytes using Horner's method -/
def fromBytes32 (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Length of toBytes32 result is always 32 -/
theorem toBytes32_length (n : Nat) : (toBytes32 n).length = 32 := by
  simp [toBytes32]

/-- Helper: division/multiplication identity -/
theorem div_mul_pow (n i : Nat) : n / (256 * 256^i) = n / 256^(i+1) := by
  congr 1
  simp only [Nat.pow_succ]
  omega

/-- Helper: 256^(i+1) = 256 * 256^i -/
theorem pow256_succ (i : Nat) : 256^(i+1) = 256 * 256^i := by
  simp only [Nat.pow_succ, Nat.mul_comm]

/-- Helper: a / 256 / 256^i = a / 256^(i+1) -/
theorem div_256_pow (a i : Nat) : a / 256 / 256^i = a / 256^(i+1) := by
  rw [Nat.div_div_eq_div_mul, pow256_succ]

/-- Two numbers with the same digits at all positions are equal.

    This is the core uniqueness property of positional numeral systems:
    if ∀i, (a / 256^i) % 256 = (b / 256^i) % 256, then a = b (for bounded values).
-/
theorem digits_unique (a b : Nat) (k : Nat) (ha : a < 256^k) (hb : b < 256^k)
    (h : ∀ i, i < k → a / 256^i % 256 = b / 256^i % 256) : a = b := by
  induction k generalizing a b with
  | zero =>
    simp only [Nat.pow_zero, Nat.lt_one_iff] at ha hb
    omega
  | succ k ih =>
    -- At each step: a = (a % 256) + 256 * (a / 256)
    -- The digits of (a / 256) at positions 0..k-1 equal those of a at positions 1..k
    have h0 : a % 256 = b % 256 := by
      have := h 0 (by omega)
      simp only [Nat.pow_zero, Nat.div_one] at this
      exact this
    have ha' : a / 256 < 256^k := by
      have := ha
      simp only [Nat.pow_succ] at this
      omega
    have hb' : b / 256 < 256^k := by
      have := hb
      simp only [Nat.pow_succ] at this
      omega
    have h_rest : ∀ i, i < k → (a / 256) / 256^i % 256 = (b / 256) / 256^i % 256 := by
      intro i hi
      have := h (i + 1) (by omega)
      rw [div_256_pow, div_256_pow]
      exact this
    have h_quot := ih (a / 256) (b / 256) ha' hb' h_rest
    have ha_decomp : a = a % 256 + 256 * (a / 256) := by omega
    have hb_decomp : b = b % 256 + 256 * (b / 256) := by omega
    omega

/-- The (31-i)-th element of the reversed range [31, 30, ..., 0] is i -/
theorem range32_reverse_getElem (i : Nat) (hi : i < 32) :
    (List.range 32).reverse[31 - i]'(by simp; omega) = i := by
  have h1 : (List.range 32).reverse.length = 32 := by simp
  have h2 : 31 - i < 32 := by omega
  simp only [List.getElem_reverse, List.length_range]
  have : 32 - 1 - (31 - i) = i := by omega
  simp only [this, List.getElem_range]

/-- Two toBytes32 outputs being equal implies digit equality -/
theorem toBytes32_eq_implies_digits_eq (a b : Nat)
    (h : toBytes32 a = toBytes32 b) :
    ∀ i, i < 32 → a / 256^i % 256 = b / 256^i % 256 := by
  intro i hi
  -- The list equality h gives us element-wise equality
  -- Element at position (31-i) in toBytes32 n is (n / 256^i % 256).toUInt8
  have h_len : (toBytes32 a).length = 32 := toBytes32_length a
  have h_pos : 31 - i < 32 := by omega
  -- Get the element at position (31 - i) from both lists
  have h_elem : (toBytes32 a)[31 - i]'(by simp [toBytes32]; omega) =
                (toBytes32 b)[31 - i]'(by simp [toBytes32]; omega) := by
    simp only [h]
  -- Unfold toBytes32 to see what each element is
  unfold toBytes32 at h_elem
  simp only [List.getElem_map] at h_elem
  -- The (31-i)-th element of the reversed range is i
  have h_idx := range32_reverse_getElem i hi
  simp only [h_idx] at h_elem
  -- Now h_elem says (a / 256^i % 256).toUInt8 = (b / 256^i % 256).toUInt8
  -- Since both values are < 256, the UInt8 conversion is faithful
  have h_a_mod : a / 256^i % 256 < 256 := Nat.mod_lt _ (by decide)
  have h_b_mod : b / 256^i % 256 < 256 := Nat.mod_lt _ (by decide)
  -- UInt8 equality for small values implies Nat equality
  have h_inj : ∀ x y : Nat, x < 256 → y < 256 → x.toUInt8 = y.toUInt8 → x = y := by
    intro x y hx hy heq
    have h1 : x.toUInt8.toNat = y.toUInt8.toNat := congrArg UInt8.toNat heq
    simp only [Nat.toUInt8, UInt8.toNat_ofNat] at h1
    calc x = x % 256 := (Nat.mod_eq_of_lt hx).symm
         _ = y % 256 := h1
         _ = y := Nat.mod_eq_of_lt hy
  exact h_inj _ _ h_a_mod h_b_mod h_elem

/-- toBytes32 is injective for values < 2^256 -/
theorem toBytes32_injective (a b : Nat) (ha : a < 2^256) (hb : b < 2^256)
    (h : toBytes32 a = toBytes32 b) : a = b := by
  have h_digits := toBytes32_eq_implies_digits_eq a b h
  have h256 : (2:Nat)^256 = 256^32 := by native_decide
  rw [h256] at ha hb
  exact digits_unique a b 32 ha hb h_digits

/-- Concatenate two 256-bit values as 64 bytes -/
def concat256 (a b : Nat) : List UInt8 :=
  toBytes32 a ++ toBytes32 b

/-! ## Mapping Slot Calculation -/

/-- Compute storage slot for a mapping entry.

    For `mapping(K => V)` at base slot `baseSlot`:
    - Entry for key `k` is at `keccak256(k ++ baseSlot)`

    The key is left-padded to 32 bytes, baseSlot is right-padded to 32 bytes.
-/
def mappingSlot (baseSlot : StorageSlot) (key : Nat) : StorageSlot :=
  keccak256 (concat256 key baseSlot)

/-- Compute storage slot for a nested mapping entry.

    For `mapping(K1 => mapping(K2 => V))` at base slot `baseSlot`:
    - First compute slot1 = keccak256(key1 ++ baseSlot)
    - Then compute slot2 = keccak256(key2 ++ slot1)
-/
def nestedMappingSlot (baseSlot : StorageSlot) (key1 key2 : Nat) : StorageSlot :=
  let slot1 := mappingSlot baseSlot key1
  mappingSlot slot1 key2

/-- Compute storage slot for a triple-nested mapping.

    For `mapping(K1 => mapping(K2 => mapping(K3 => V)))`:
-/
def tripleNestedMappingSlot (baseSlot : StorageSlot) (key1 key2 key3 : Nat) : StorageSlot :=
  let slot1 := mappingSlot baseSlot key1
  let slot2 := mappingSlot slot1 key2
  mappingSlot slot2 key3

/-! ## Dynamic Array Storage -/

/-- Storage layout for a dynamic array at `baseSlot`:
    - Length stored at `baseSlot`
    - Data starts at `keccak256(baseSlot)`
    - Element N at `dataStart + N * elementSize`
-/
structure DynamicArrayLayout where
  /-- Base slot where length is stored -/
  baseSlot : StorageSlot
  /-- Number of 32-byte slots per element -/
  elementSize : Nat
  deriving Repr

/-- Get the slot where array length is stored -/
def DynamicArrayLayout.lengthSlot (arr : DynamicArrayLayout) : StorageSlot :=
  arr.baseSlot

/-- Get the starting slot for array data -/
def DynamicArrayLayout.dataStart (arr : DynamicArrayLayout) : StorageSlot :=
  keccak256 (toBytes32 arr.baseSlot)

/-- Get the slot for element at index N -/
def DynamicArrayLayout.elementSlot (arr : DynamicArrayLayout) (index : Nat) : StorageSlot :=
  arr.dataStart + index * arr.elementSize

/-- Get the slot for a specific field within a struct element -/
def DynamicArrayLayout.fieldSlot (arr : DynamicArrayLayout) (index : Nat) (fieldOffset : Nat) : StorageSlot :=
  arr.elementSlot index + fieldOffset

/-! ## Solidity Storage with Layout Tracking -/

/-- Enhanced storage that tracks mapping and array layouts -/
structure SolidityStorage where
  /-- Raw storage data -/
  raw : Storage
  /-- Known mapping base slots (for verification) -/
  mappingBases : List StorageSlot
  /-- Known array layouts -/
  arrayLayouts : List DynamicArrayLayout

namespace SolidityStorage

/-- Create empty Solidity storage -/
def empty : SolidityStorage :=
  { raw := Storage.empty
  , mappingBases := []
  , arrayLayouts := [] }

/-- Read from a raw slot -/
def readRaw (s : SolidityStorage) (slot : StorageSlot) : StorageValue :=
  s.raw.read slot

/-- Write to a raw slot -/
def writeRaw (s : SolidityStorage) (slot : StorageSlot) (val : StorageValue) : SolidityStorage :=
  { s with raw := s.raw.write slot val }

/-- Declare a mapping at a base slot -/
def declareMapping (s : SolidityStorage) (baseSlot : StorageSlot) : SolidityStorage :=
  { s with mappingBases := baseSlot :: s.mappingBases }

/-- Declare a dynamic array -/
def declareArray (s : SolidityStorage) (baseSlot : StorageSlot) (elemSize : Nat) : SolidityStorage :=
  { s with arrayLayouts := ⟨baseSlot, elemSize⟩ :: s.arrayLayouts }

/-- Read from a mapping -/
def readMapping (s : SolidityStorage) (baseSlot : StorageSlot) (key : Nat) : StorageValue :=
  s.raw.read (mappingSlot baseSlot key)

/-- Write to a mapping -/
def writeMapping (s : SolidityStorage) (baseSlot : StorageSlot) (key : Nat) (val : StorageValue) : SolidityStorage :=
  { s with raw := s.raw.write (mappingSlot baseSlot key) val }

/-- Read from a nested mapping -/
def readNestedMapping (s : SolidityStorage) (baseSlot : StorageSlot) (key1 key2 : Nat) : StorageValue :=
  s.raw.read (nestedMappingSlot baseSlot key1 key2)

/-- Write to a nested mapping -/
def writeNestedMapping (s : SolidityStorage) (baseSlot : StorageSlot) (key1 key2 : Nat) (val : StorageValue) : SolidityStorage :=
  { s with raw := s.raw.write (nestedMappingSlot baseSlot key1 key2) val }

/-- Read array length -/
def readArrayLength (s : SolidityStorage) (arr : DynamicArrayLayout) : Nat :=
  s.raw.read arr.lengthSlot

/-- Write array length -/
def writeArrayLength (s : SolidityStorage) (arr : DynamicArrayLayout) (len : Nat) : SolidityStorage :=
  { s with raw := s.raw.write arr.lengthSlot len }

/-- Read array element -/
def readArrayElement (s : SolidityStorage) (arr : DynamicArrayLayout) (index : Nat) : StorageValue :=
  s.raw.read (arr.elementSlot index)

/-- Write array element -/
def writeArrayElement (s : SolidityStorage) (arr : DynamicArrayLayout) (index : Nat) (val : StorageValue) : SolidityStorage :=
  { s with raw := s.raw.write (arr.elementSlot index) val }

end SolidityStorage

/-! ## Collision Resistance Axioms

We assume keccak256 is collision-resistant. These axioms are used
for verification but are not proven (they rely on cryptographic assumptions).
-/

/-- Different inputs produce different outputs (collision resistance) -/
axiom keccak256_injective : ∀ (a b : List UInt8), a ≠ b → keccak256 a ≠ keccak256 b

/-- Mapping slots for different keys are different (for bounded keys).

    In the EVM, all storage keys and values are 256-bit, so this bound is
    always satisfied in practice.
-/
theorem mappingSlot_injective (baseSlot : StorageSlot) (k1 k2 : Nat)
    (hk1 : k1 < 2^256) (hk2 : k2 < 2^256) (h : k1 ≠ k2) :
    mappingSlot baseSlot k1 ≠ mappingSlot baseSlot k2 := by
  unfold mappingSlot
  apply keccak256_injective
  unfold concat256
  -- Different keys produce different concatenations
  intro h_eq
  have h_bytes : toBytes32 k1 = toBytes32 k2 := by
    have h_len : (toBytes32 k1).length = 32 := by simp [toBytes32]
    exact List.append_inj_left h_eq (by simp [toBytes32])
  -- Use injectivity of toBytes32
  have h_keys_eq := toBytes32_injective k1 k2 hk1 hk2 h_bytes
  exact h h_keys_eq

/-- Mapping slots for different base slots are different (for bounded slots).

    This is the dual of mappingSlot_injective - injectivity in the base slot argument.
-/
theorem mappingSlot_base_injective (b1 b2 : StorageSlot) (key : Nat)
    (hb1 : b1 < 2^256) (hb2 : b2 < 2^256) (h : b1 ≠ b2) :
    mappingSlot b1 key ≠ mappingSlot b2 key := by
  unfold mappingSlot
  apply keccak256_injective
  unfold concat256
  intro h_eq
  -- The concatenations are key ++ b1 and key ++ b2
  -- If they're equal, then b1 = b2 (since key parts are the same)
  have h_bytes : toBytes32 b1 = toBytes32 b2 := by
    have h_len : (toBytes32 key).length = 32 := by simp [toBytes32]
    exact List.append_inj_right h_eq (by simp [toBytes32])
  have h_base_eq := toBytes32_injective b1 b2 hb1 hb2 h_bytes
  exact h h_base_eq

/-- Mapping slots don't collide with base slots (for reasonable base slots) -/
axiom mappingSlot_not_base : ∀ (baseSlot : StorageSlot) (key : Nat),
    baseSlot < 2^64 → mappingSlot baseSlot key ≥ 2^64

/-! ## Storage Properties -/

section Properties

/-- Reading from a mapping after writing returns the written value -/
theorem readMapping_writeMapping (s : SolidityStorage) (baseSlot : StorageSlot)
    (key : Nat) (val : StorageValue) :
    (s.writeMapping baseSlot key val).readMapping baseSlot key = val := by
  unfold SolidityStorage.readMapping SolidityStorage.writeMapping
  simp only [Storage.read, Storage.write]
  simp

/-- Writing to different mapping keys doesn't affect other entries.

    Requires keys to be bounded (< 2^256), which is always true for EVM values.
-/
theorem writeMapping_different_key (s : SolidityStorage) (baseSlot : StorageSlot)
    (k1 k2 : Nat) (val : StorageValue)
    (hk1 : k1 < 2^256) (hk2 : k2 < 2^256) (h : k1 ≠ k2) :
    (s.writeMapping baseSlot k1 val).readMapping baseSlot k2 = s.readMapping baseSlot k2 := by
  unfold SolidityStorage.readMapping SolidityStorage.writeMapping
  simp only [Storage.read, Storage.write]
  have h_slot : mappingSlot baseSlot k2 ≠ mappingSlot baseSlot k1 := by
    intro h_eq
    exact mappingSlot_injective baseSlot k1 k2 hk1 hk2 h h_eq.symm
  split
  · -- Case: k2 == k1 = true, contradiction
    rename_i h_beq
    simp only [beq_iff_eq] at h_beq
    exact absurd h_beq h_slot
  · -- Case: k2 == k1 = false, trivial
    rfl

/-- Nested mapping writes are independent for different outer keys.

    Requires keys and intermediate slots to be bounded.
-/
theorem writeNestedMapping_different_outer (s : SolidityStorage) (baseSlot : StorageSlot)
    (k1a k1b k2 : Nat) (val : StorageValue)
    (hk1a : k1a < 2^256) (hk1b : k1b < 2^256)
    (hSlot1a : mappingSlot baseSlot k1a < 2^256) (hSlot1b : mappingSlot baseSlot k1b < 2^256)
    (h : k1a ≠ k1b) :
    (s.writeNestedMapping baseSlot k1a k2 val).readNestedMapping baseSlot k1b k2 =
    s.readNestedMapping baseSlot k1b k2 := by
  unfold SolidityStorage.readNestedMapping SolidityStorage.writeNestedMapping
  simp only [Storage.read, Storage.write]
  unfold nestedMappingSlot
  have h_slot1 : mappingSlot baseSlot k1a ≠ mappingSlot baseSlot k1b :=
    mappingSlot_injective baseSlot k1a k1b hk1a hk1b h
  -- The nested slots are different because the intermediate base slots are different
  have h_nested : mappingSlot (mappingSlot baseSlot k1b) k2 ≠ mappingSlot (mappingSlot baseSlot k1a) k2 := by
    exact mappingSlot_base_injective _ _ k2 hSlot1b hSlot1a h_slot1.symm
  split
  · -- Case: slots equal = true, contradiction
    rename_i h_beq
    simp only [beq_iff_eq] at h_beq
    exact absurd h_beq h_nested
  · -- Case: slots equal = false, trivial
    rfl

end Properties

/-! ## ERC-20 Storage Layout Example

Standard ERC-20 token layout:
- Slot 0: totalSupply
- Slot 1: balances mapping
- Slot 2: allowances mapping (nested)
-/

/-- Standard ERC-20 storage slots -/
structure ERC20Layout where
  totalSupplySlot : StorageSlot := 0
  balancesSlot : StorageSlot := 1
  allowancesSlot : StorageSlot := 2

/-- Get balance slot for an address -/
def ERC20Layout.balanceSlot (layout : ERC20Layout) (owner : Address) : StorageSlot :=
  mappingSlot layout.balancesSlot owner.value

/-- Get allowance slot for owner/spender pair -/
def ERC20Layout.allowanceSlot (layout : ERC20Layout) (owner spender : Address) : StorageSlot :=
  nestedMappingSlot layout.allowancesSlot owner.value spender.value

/-- Read total supply -/
def readTotalSupply (s : SolidityStorage) (layout : ERC20Layout) : Nat :=
  s.readRaw layout.totalSupplySlot

/-- Read balance -/
def readBalance (s : SolidityStorage) (layout : ERC20Layout) (owner : Address) : Nat :=
  s.readRaw (layout.balanceSlot owner)

/-- Read allowance -/
def readAllowance (s : SolidityStorage) (layout : ERC20Layout) (owner spender : Address) : Nat :=
  s.readRaw (layout.allowanceSlot owner spender)

/-- Write balance -/
def writeBalance (s : SolidityStorage) (layout : ERC20Layout) (owner : Address) (val : Nat) : SolidityStorage :=
  s.writeRaw (layout.balanceSlot owner) val

/-- Write allowance -/
def writeAllowance (s : SolidityStorage) (layout : ERC20Layout) (owner spender : Address) (val : Nat) : SolidityStorage :=
  s.writeRaw (layout.allowanceSlot owner spender) val

/-! ## Summary

This module provides:

1. **mappingSlot**: Compute `keccak256(key ++ baseSlot)` for mapping entries
2. **nestedMappingSlot**: Chain hash computations for nested mappings
3. **DynamicArrayLayout**: Model array storage with length and data slots
4. **SolidityStorage**: Enhanced storage with read/write for mappings and arrays
5. **ERC20Layout**: Concrete example showing how ERC-20 uses these patterns

Key properties:
- Mapping slots for different keys don't collide (collision resistance)
- Reads after writes return the written value
- Independent mapping entries don't interfere
-/

end LeanEVM.StorageLayout
