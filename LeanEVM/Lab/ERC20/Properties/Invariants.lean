import Lab.ERC20.Contracts.Interface

/-!
# ERC-20 Invariants

Global invariants that should hold throughout a contract's lifetime.

## Key Invariants

1. **Supply Conservation** - Total supply equals sum of all balances
2. **Non-Negative Balances** - All balances are ≥ 0 (automatic with Nat)
3. **Allowance Bounds** - Allowances don't exceed owner's balance (optional)
-/

namespace Lab.ERC20.Properties

open Lab.ERC20

/-! ## Invariant Definitions -/

/-- The fundamental invariant: sum of balances equals total supply -/
def SupplyInvariant {S : Type} [ERC20State S]
    (state : S) (addresses : List Address) : Prop :=
  (addresses.map (ERC20State.balanceOf state)).sum = ERC20State.totalSupply state

/-- No single balance exceeds total supply -/
def BalanceBoundedBySupply {S : Type} [ERC20State S] (state : S) : Prop :=
  ∀ addr, ERC20State.balanceOf state addr ≤ ERC20State.totalSupply state

/-- Allowance doesn't exceed owner's balance (stronger invariant) -/
def AllowanceBoundedByBalance {S : Type} [ERC20State S] (state : S) : Prop :=
  ∀ owner spender,
    ERC20State.allowance state owner spender ≤ ERC20State.balanceOf state owner

/-! ## Invariant Preservation -/

/-- Type for proving an invariant is preserved by an operation -/
structure InvariantPreservation {S : Type} [ERC20State S]
    (inv : S → Prop) (op : S → MsgContext → Address → Amount → Result S) where
  /-- The preservation proof -/
  preserved : ∀ s msg addr amt s',
    inv s → op s msg addr amt = Result.ok s' → inv s'

/-! ## Local Balance Conservation -/

/-- Transfer conserves the sum of sender and receiver balances -/
def LocalBalanceConservation {S : Type} [ERC20State S] [ERC20Ops S]
    (state state' : S) (sender receiver : Address) : Prop :=
  ERC20State.balanceOf state sender + ERC20State.balanceOf state receiver =
  ERC20State.balanceOf state' sender + ERC20State.balanceOf state' receiver

/-! ## Monotonicity Properties -/

/-- Total supply never increases (for non-mintable tokens) -/
def SupplyNonIncreasing {S : Type} [ERC20State S]
    (state state' : S) : Prop :=
  ERC20State.totalSupply state' ≤ ERC20State.totalSupply state

/-- Total supply never decreases (for non-burnable tokens) -/
def SupplyNonDecreasing {S : Type} [ERC20State S]
    (state state' : S) : Prop :=
  ERC20State.totalSupply state' ≥ ERC20State.totalSupply state

/-- Total supply is constant (for fixed-supply tokens) -/
def SupplyConstant {S : Type} [ERC20State S]
    (state state' : S) : Prop :=
  ERC20State.totalSupply state' = ERC20State.totalSupply state

end Lab.ERC20.Properties
