/-!
# Core EVM Types

This module defines the fundamental types used to model the Ethereum Virtual Machine.
We use a simplified model suitable for verifying high-level contract properties.

## Design Decisions

1. **UInt256 as Nat**: We model 256-bit integers as natural numbers with explicit
   overflow checks. This simplifies proofs while maintaining soundness.

2. **Address as opaque type**: Addresses are 160-bit values, but we treat them
   as an abstract type with decidable equality.

3. **Storage as functions**: Contract storage is modeled as `Slot → Value` functions,
   which is natural for Lean and supports clean reasoning.
-/

namespace LeanEVM

/-! ## Basic Types -/

/-- Ethereum address (160-bit, but we abstract over the representation) -/
structure Address where
  value : Nat
  deriving Repr, DecidableEq, Hashable

instance : Inhabited Address := ⟨⟨0⟩⟩

/-- The zero address (0x0) - often used as burn address or null -/
def Address.zero : Address := ⟨0⟩

/-- Check if address is zero -/
def Address.isZero (a : Address) : Bool := a.value == 0

/-- Wei - the smallest unit of Ether (we use Nat for simplicity) -/
abbrev Wei := Nat

/-- Storage slot (256-bit key) -/
abbrev StorageSlot := Nat

/-- Storage value (256-bit) -/
abbrev StorageValue := Nat

/-- Maximum value for uint256 -/
def MAX_UINT256 : Nat := 2^256 - 1

/-! ## Blockchain Context -/

/-- Block information available to contracts -/
structure BlockContext where
  number : Nat
  timestamp : Nat
  baseFee : Nat
  coinbase : Address
  deriving Repr

/-- Message context for the current call -/
structure MsgContext where
  sender : Address
  value : Wei
  origin : Address  -- Original transaction sender (tx.origin)
  deriving Repr

/-- Transaction context -/
structure TxContext where
  origin : Address
  gasPrice : Nat
  deriving Repr

/-! ## Storage Model -/

/-- Contract storage as a function from slots to values -/
def Storage := StorageSlot → StorageValue

instance : Inhabited Storage := ⟨fun _ => 0⟩

/-- Read from storage (SLOAD) -/
def Storage.read (s : Storage) (slot : StorageSlot) : StorageValue := s slot

/-- Write to storage (SSTORE) -/
def Storage.write (s : Storage) (slot : StorageSlot) (val : StorageValue) : Storage :=
  fun k => if k == slot then val else s k

/-- Storage with all zeros -/
def Storage.empty : Storage := fun _ => 0

/-- Two storages are equal if they agree on all slots -/
theorem Storage.ext {s1 s2 : Storage} (h : ∀ k, s1 k = s2 k) : s1 = s2 := by
  funext k
  exact h k

/-! ## Balance Model -/

/-- Global balance mapping -/
def Balances := Address → Wei

instance : Inhabited Balances := ⟨fun _ => 0⟩

/-- Read balance -/
def Balances.get (b : Balances) (addr : Address) : Wei := b addr

/-- Update balance -/
def Balances.set (b : Balances) (addr : Address) (val : Wei) : Balances :=
  fun a => if a == addr then val else b a

/-- Add to balance -/
def Balances.add (b : Balances) (addr : Address) (amount : Wei) : Balances :=
  b.set addr (b.get addr + amount)

/-- Subtract from balance (with underflow check) -/
def Balances.sub (b : Balances) (addr : Address) (amount : Wei) : Option Balances :=
  if b.get addr >= amount then
    some (b.set addr (b.get addr - amount))
  else
    none

/-! ## Arithmetic with Overflow Handling -/

/-- Safe addition that checks for overflow -/
def safeAdd (a b : Nat) : Option Nat :=
  let sum := a + b
  if sum <= MAX_UINT256 then some sum else none

/-- Safe subtraction that checks for underflow -/
def safeSub (a b : Nat) : Option Nat :=
  if a >= b then some (a - b) else none

/-- Safe multiplication that checks for overflow -/
def safeMul (a b : Nat) : Option Nat :=
  let prod := a * b
  if prod <= MAX_UINT256 then some prod else none

/-- Modular addition (wrapping) -/
def wrapAdd (a b : Nat) : Nat := (a + b) % (MAX_UINT256 + 1)

/-- Modular subtraction (wrapping) -/
def wrapSub (a b : Nat) : Nat := (a + MAX_UINT256 + 1 - b) % (MAX_UINT256 + 1)

end LeanEVM
