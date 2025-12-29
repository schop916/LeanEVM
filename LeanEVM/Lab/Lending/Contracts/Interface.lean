import Lab.ERC20.Contracts.Interface

/-!
# Lending Protocol Interface

An Aave-style lending protocol where users can:
1. Deposit assets as collateral
2. Borrow against their collateral
3. Repay loans with interest
4. Liquidate undercollateralized positions

## Key Concepts

- **Collateral Factor**: Maximum borrow capacity as percentage of collateral
- **Health Factor**: Ratio of collateral value to borrow value (< 1 = liquidatable)
- **Interest Rate**: Accumulates on borrowed amounts over time
- **Liquidation**: Third parties can repay loans and seize collateral

## References

- Aave V2: https://docs.aave.com/developers/v/2.0/
- Compound: https://compound.finance/docs
-/

namespace Lab.Lending

open Lab.ERC20 (Address Amount Result MsgContext)

/-! ## Lending-Specific Types -/

/-- Asset identifier (simplified - would be token address in reality) -/
abbrev AssetId := Nat

/-- Interest rate in basis points (1 bp = 0.01%) -/
abbrev InterestRate := Nat

/-- Collateral factor in basis points (e.g., 7500 = 75%) -/
abbrev CollateralFactor := Nat

/-- Timestamp for interest calculations -/
abbrev Timestamp := Nat

/-- Price in a common denomination -/
abbrev Price := Nat

/-! ## Constants -/

/-- Basis points denominator (100% = 10000 bp) -/
def BASIS_POINTS : Nat := 10000

/-- Minimum health factor (100% = liquidation threshold) -/
def MIN_HEALTH_FACTOR : Nat := 10000

/-- Liquidation bonus in basis points (e.g., 500 = 5% bonus) -/
def LIQUIDATION_BONUS : Nat := 500

/-! ## User Position -/

/-- A user's position in the lending protocol -/
structure UserPosition where
  /-- Deposited collateral per asset -/
  collateral : AssetId → Amount
  /-- Borrowed amount per asset (principal) -/
  borrowed : AssetId → Amount
  /-- Accumulated interest per asset -/
  accruedInterest : AssetId → Amount
  /-- Last update timestamp -/
  lastUpdate : Timestamp

/-! ## Asset Configuration -/

/-- Configuration for a supported asset -/
structure AssetConfig where
  /-- Whether the asset can be used as collateral -/
  isCollateral : Bool
  /-- Whether the asset can be borrowed -/
  isBorrowable : Bool
  /-- Collateral factor (LTV) in basis points -/
  collateralFactor : CollateralFactor
  /-- Liquidation threshold in basis points -/
  liquidationThreshold : CollateralFactor
  /-- Current borrow interest rate (per block) in basis points -/
  borrowRate : InterestRate
  /-- Current price in common denomination -/
  price : Price
  deriving Repr

/-! ## State Abstraction -/

/-- Abstract state for a lending protocol -/
class LendingState (S : Type) where
  /-- Get user position -/
  getPosition : S → Address → UserPosition
  /-- Get asset configuration -/
  getAssetConfig : S → AssetId → AssetConfig
  /-- Total deposited for an asset -/
  totalDeposits : S → AssetId → Amount
  /-- Total borrowed for an asset -/
  totalBorrows : S → AssetId → Amount
  /-- Protocol owner/admin -/
  owner : S → Address
  /-- Update user position -/
  setPosition : S → Address → UserPosition → S

/-! ## Operations -/

/-- Lending protocol operations -/
class LendingOps (S : Type) [LendingState S] where
  /-- Deposit collateral -/
  deposit : S → MsgContext → AssetId → Amount → Timestamp → Result S
  /-- Withdraw collateral (if health factor permits) -/
  withdraw : S → MsgContext → AssetId → Amount → Timestamp → Result S
  /-- Borrow against collateral -/
  borrow : S → MsgContext → AssetId → Amount → Timestamp → Result S
  /-- Repay borrowed amount -/
  repay : S → MsgContext → AssetId → Amount → Timestamp → Result S
  /-- Liquidate undercollateralized position -/
  liquidate : S → MsgContext → Address → AssetId → AssetId → Amount → Timestamp → Result S

/-! ## Health Factor Calculation -/

/-- Calculate total collateral value in common denomination -/
def totalCollateralValue {S : Type} [LendingState S] (state : S) (user : Address) (assets : List AssetId) : Amount :=
  let pos := LendingState.getPosition state user
  assets.foldl (fun acc asset =>
    let config := LendingState.getAssetConfig state asset
    let value := pos.collateral asset * config.price * config.collateralFactor / BASIS_POINTS
    acc + value) 0

/-- Calculate total borrow value in common denomination -/
def totalBorrowValue {S : Type} [LendingState S] (state : S) (user : Address) (assets : List AssetId) : Amount :=
  let pos := LendingState.getPosition state user
  assets.foldl (fun acc asset =>
    let config := LendingState.getAssetConfig state asset
    let principal := pos.borrowed asset
    let interest := pos.accruedInterest asset
    let value := (principal + interest) * config.price
    acc + value) 0

/-- Calculate health factor (scaled by BASIS_POINTS) -/
def healthFactor {S : Type} [LendingState S] (state : S) (user : Address) (assets : List AssetId) : Nat :=
  let collateral := totalCollateralValue state user assets
  let borrow := totalBorrowValue state user assets
  if borrow = 0 then
    BASIS_POINTS * 100  -- Max health factor when no borrows
  else
    collateral * BASIS_POINTS / borrow

/-- Check if position is liquidatable -/
def isLiquidatable {S : Type} [LendingState S] (state : S) (user : Address) (assets : List AssetId) : Bool :=
  healthFactor state user assets < MIN_HEALTH_FACTOR

end Lab.Lending
