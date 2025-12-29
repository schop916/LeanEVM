import Lab.Lending.Contracts.LendingPool

/-!
# Lending Protocol Invariants

Key invariants for lending protocol safety:

1. **Solvency**: Protocol can always meet withdrawal requests
2. **Collateralization**: All borrows are sufficiently collateralized
3. **Interest Monotonicity**: Accrued interest never decreases
4. **Liquidation Safety**: Only unhealthy positions can be liquidated
-/

namespace Lab.Lending

open Lab.ERC20 (Address Amount Result MsgContext)

/-! ## Solvency Invariants -/

/-- Total deposits ≥ total borrows for each asset -/
def AssetSolvency (s : LendingPoolState) (assetId : AssetId) : Prop :=
  s.totalDeps assetId ≥ s.totalBors assetId

/-- Protocol is solvent for all assets -/
def ProtocolSolvency (s : LendingPoolState) : Prop :=
  ∀ assetId ∈ s.supportedAssets, AssetSolvency s assetId

/-! ## Collateralization Invariants -/

/-- All positions have health factor ≥ 1 (or no borrows) -/
def AllPositionsHealthy (s : LendingPoolState) (users : List Address) : Prop :=
  ∀ user ∈ users, healthFactor s user s.supportedAssets ≥ MIN_HEALTH_FACTOR

/-- User's collateral value exceeds borrow value -/
def PositionCollateralized (s : LendingPoolState) (user : Address) : Prop :=
  totalCollateralValue s user s.supportedAssets ≥ totalBorrowValue s user s.supportedAssets

/-! ## Interest Invariants -/

/-- Interest only accrues, never decreases -/
def InterestMonotonicity (s s' : LendingPoolState) (user : Address) : Prop :=
  ∀ assetId, (s'.positions user).accruedInterest assetId ≥ (s.positions user).accruedInterest assetId

/-- Interest is proportional to borrow amount and time -/
def InterestProportional (s : LendingPoolState) (user : Address) (assetId : AssetId) (startTime endTime : Timestamp) : Prop :=
  let pos := s.positions user
  let config := s.assetConfigs assetId
  let elapsed := endTime - startTime
  let expected := calculateInterest (pos.borrowed assetId) config.borrowRate elapsed
  pos.accruedInterest assetId ≤ expected + (s.positions user).accruedInterest assetId

/-! ## Liquidation Invariants -/

/-- Liquidation only possible when health factor < 1 -/
def LiquidationRequiresUnhealthy (s : LendingPoolState) (borrower : Address) : Prop :=
  ∀ msg debtAsset collateralAsset amount t,
    (∃ s', liquidate s msg borrower debtAsset collateralAsset amount t = Result.ok s') →
    isLiquidatable s borrower s.supportedAssets = true

/-- Liquidation improves or maintains protocol solvency -/
def LiquidationPreservesSolvency (s s' : LendingPoolState) : Prop :=
  ∀ assetId, AssetSolvency s assetId → AssetSolvency s' assetId

/-! ## Balance Conservation -/

/-- Total deposits = sum of user deposits -/
def DepositConservation (s : LendingPoolState) (assetId : AssetId) (users : List Address) : Prop :=
  (users.map fun u => (s.positions u).collateral assetId).sum = s.totalDeps assetId

/-- Total borrows = sum of user borrows -/
def BorrowConservation (s : LendingPoolState) (assetId : AssetId) (users : List Address) : Prop :=
  (users.map fun u => (s.positions u).borrowed assetId).sum = s.totalBors assetId

/-! ## Safety Properties -/

/-- Withdrawals maintain health factor -/
def SafeWithdrawal (s : LendingPoolState) (user : Address) : Prop :=
  ∀ assetId amount t s',
    withdraw s ⟨user, 0⟩ assetId amount t = Result.ok s' →
    healthFactor s' user s.supportedAssets ≥ MIN_HEALTH_FACTOR

/-- Borrows maintain health factor -/
def SafeBorrow (s : LendingPoolState) (user : Address) : Prop :=
  ∀ assetId amount t s',
    borrow s ⟨user, 0⟩ assetId amount t = Result.ok s' →
    healthFactor s' user s.supportedAssets ≥ MIN_HEALTH_FACTOR

/-! ## Compound Invariant -/

/-- Main lending pool invariant -/
structure LendingInvariant (s : LendingPoolState) (users : List Address) : Prop where
  /-- Protocol is solvent -/
  solvent : ProtocolSolvency s
  /-- All positions are healthy -/
  healthy : AllPositionsHealthy s users
  /-- Deposit accounting is correct -/
  depositConservation : ∀ assetId ∈ s.supportedAssets, DepositConservation s assetId users
  /-- Borrow accounting is correct -/
  borrowConservation : ∀ assetId ∈ s.supportedAssets, BorrowConservation s assetId users

/-! ## Two-State Properties -/

/-- Operations preserve solvency -/
def PreservesProtocolSolvency (op : LendingPoolState → Result LendingPoolState) : Prop :=
  ∀ s s', ProtocolSolvency s → op s = Result.ok s' → ProtocolSolvency s'

/-- Deposits only increase solvency -/
def DepositIncreasesSolvency (s s' : LendingPoolState) (assetId : AssetId) : Prop :=
  s'.totalDeps assetId ≥ s.totalDeps assetId ∧
  s'.totalBors assetId = s.totalBors assetId

end Lab.Lending
