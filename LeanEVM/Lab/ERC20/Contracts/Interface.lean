import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# ERC-20 Interface

Standard ERC-20 interface definitions for verification.

## ERC-20 Standard Functions

- `totalSupply()` - Returns total token supply
- `balanceOf(address)` - Returns balance of an address
- `transfer(address, uint256)` - Transfer tokens
- `approve(address, uint256)` - Approve spender
- `allowance(address, address)` - Check allowance
- `transferFrom(address, address, uint256)` - Transfer with allowance
-/

namespace Lab.ERC20

/-! ## Basic Types -/

/-- Ethereum address (160 bits, represented as Nat for simplicity) -/
structure Address where
  val : Nat
deriving DecidableEq, Repr

/-- Zero address -/
def Address.zero : Address := ⟨0⟩

/-- Check if address is zero -/
def Address.isZero (a : Address) : Bool := a.val = 0

/-- Token amount (256 bits, represented as Nat) -/
abbrev Amount := Nat

/-! ## Execution Result -/

/-- Result of a contract call -/
inductive Result (α : Type)
  | ok : α → Result α
  | revert : String → Result α
deriving Repr

namespace Result

def isOk {α : Type} : Result α → Bool
  | ok _ => true
  | revert _ => false

def isRevert {α : Type} : Result α → Bool
  | ok _ => false
  | revert _ => true

def map {α β : Type} (f : α → β) : Result α → Result β
  | ok a => ok (f a)
  | revert msg => revert msg

/-- Bind for Result monad -/
def bind {α β : Type} (r : Result α) (f : α → Result β) : Result β :=
  match r with
  | ok a => f a
  | revert msg => revert msg

instance : Monad Result where
  pure := Result.ok
  bind := Result.bind

end Result

/-- Require condition or revert -/
def require (cond : Bool) (msg : String) : Result Unit :=
  if cond then Result.ok () else Result.revert msg

/-! ## Message Context -/

/-- Transaction context -/
structure MsgContext where
  sender : Address
  value : Amount := 0

/-! ## ERC-20 State Interface -/

/-- Abstract ERC-20 state -/
class ERC20State (S : Type) where
  /-- Get total supply -/
  totalSupply : S → Amount
  /-- Get balance of address -/
  balanceOf : S → Address → Amount
  /-- Get allowance -/
  allowance : S → Address → Address → Amount
  /-- Set balance (internal) -/
  setBalance : S → Address → Amount → S
  /-- Set allowance (internal) -/
  setAllowance : S → Address → Address → Amount → S

/-! ## ERC-20 Operations Interface -/

/-- Abstract ERC-20 operations -/
class ERC20Ops (S : Type) [ERC20State S] where
  /-- Transfer tokens -/
  transfer : S → MsgContext → Address → Amount → Result S
  /-- Approve spender -/
  approve : S → MsgContext → Address → Amount → Result S
  /-- Transfer from (using allowance) -/
  transferFrom : S → MsgContext → Address → Address → Amount → Result S

end Lab.ERC20
