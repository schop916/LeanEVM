import Lab.Lending.Contracts.Interface

/-!
# Lending Pool Implementation

A simplified Aave-style lending pool with:

- Multi-asset support with configurable parameters
- Collateral and borrowing with health factor checks
- Interest accrual on borrowed amounts
- Liquidation of undercollateralized positions

## Key Invariants

1. **Solvency**: Total deposits ≥ total borrows per asset
2. **Health Factor**: Borrows only allowed if health factor > 1
3. **Interest Monotonicity**: Accrued interest only increases
4. **Liquidation Threshold**: Only positions with HF < 1 can be liquidated
-/

namespace Lab.Lending

open Lab.ERC20 (Address Amount Result MsgContext require)

/-! ## State Definition -/

/-- Lending pool state -/
structure LendingPoolState where
  /-- User positions -/
  positions : Address → UserPosition
  /-- Asset configurations -/
  assetConfigs : AssetId → AssetConfig
  /-- Total deposits per asset -/
  totalDeps : AssetId → Amount
  /-- Total borrows per asset -/
  totalBors : AssetId → Amount
  /-- Protocol owner -/
  admin : Address
  /-- Supported asset IDs -/
  supportedAssets : List AssetId

/-! ## Default Values -/

/-- Empty user position -/
def UserPosition.empty : UserPosition :=
  { collateral := fun _ => 0
  , borrowed := fun _ => 0
  , accruedInterest := fun _ => 0
  , lastUpdate := 0 }

/-- Default asset config (not enabled) -/
def AssetConfig.default : AssetConfig :=
  { isCollateral := false
  , isBorrowable := false
  , collateralFactor := 0
  , liquidationThreshold := 0
  , borrowRate := 0
  , price := 0 }

/-! ## Initialization -/

/-- Create a new lending pool -/
def LendingPoolState.init (admin : Address) : LendingPoolState :=
  { positions := fun _ => UserPosition.empty
  , assetConfigs := fun _ => AssetConfig.default
  , totalDeps := fun _ => 0
  , totalBors := fun _ => 0
  , admin := admin
  , supportedAssets := [] }

/-- Add a supported asset -/
def LendingPoolState.addAsset (s : LendingPoolState) (assetId : AssetId) (config : AssetConfig) : LendingPoolState :=
  { s with
    assetConfigs := fun id => if id = assetId then config else s.assetConfigs id
    supportedAssets := if assetId ∈ s.supportedAssets then s.supportedAssets else assetId :: s.supportedAssets }

/-! ## LendingState Instance -/

instance : LendingState LendingPoolState where
  getPosition s addr := s.positions addr
  getAssetConfig s id := s.assetConfigs id
  totalDeposits s id := s.totalDeps id
  totalBorrows s id := s.totalBors id
  owner s := s.admin
  setPosition s addr pos := { s with positions := fun a => if a = addr then pos else s.positions a }

/-! ## Interest Accrual -/

/-- Calculate accrued interest since last update -/
def calculateInterest (principal : Amount) (rate : InterestRate) (elapsed : Timestamp) : Amount :=
  principal * rate * elapsed / BASIS_POINTS

/-- Update user's accrued interest -/
def accrueInterest (s : LendingPoolState) (user : Address) (currentTime : Timestamp) : LendingPoolState :=
  let pos := s.positions user
  let elapsed := currentTime - pos.lastUpdate
  if elapsed = 0 then s
  else
    let newPos := { pos with
      accruedInterest := fun asset =>
        let config := s.assetConfigs asset
        let principal := pos.borrowed asset
        let newInterest := calculateInterest principal config.borrowRate elapsed
        pos.accruedInterest asset + newInterest
      lastUpdate := currentTime }
    { s with positions := fun a => if a = user then newPos else s.positions a }

/-! ## Core Operations -/

/-- Deposit collateral -/
def deposit (s : LendingPoolState) (msg : MsgContext) (assetId : AssetId) (amount : Amount) (currentTime : Timestamp) :
    Result LendingPoolState := do
  require (amount > 0) "Lending: deposit amount must be positive"
  let config := s.assetConfigs assetId
  require (config.isCollateral) "Lending: asset cannot be used as collateral"
  -- Accrue interest first
  let s := accrueInterest s msg.sender currentTime
  let pos := s.positions msg.sender
  let newCollateral := pos.collateral assetId + amount
  let newPos := { pos with
    collateral := fun id => if id = assetId then newCollateral else pos.collateral id
    lastUpdate := currentTime }
  pure { s with
    positions := fun a => if a = msg.sender then newPos else s.positions a
    totalDeps := fun id => if id = assetId then s.totalDeps id + amount else s.totalDeps id }

/-- Withdraw collateral (with health factor check) -/
def withdraw (s : LendingPoolState) (msg : MsgContext) (assetId : AssetId) (amount : Amount) (currentTime : Timestamp) :
    Result LendingPoolState := do
  require (amount > 0) "Lending: withdraw amount must be positive"
  let s := accrueInterest s msg.sender currentTime
  let pos := s.positions msg.sender
  require (pos.collateral assetId ≥ amount) "Lending: insufficient collateral"
  -- Calculate new position
  let newCollateral := pos.collateral assetId - amount
  let newPos := { pos with
    collateral := fun id => if id = assetId then newCollateral else pos.collateral id
    lastUpdate := currentTime }
  let newState := { s with
    positions := fun a => if a = msg.sender then newPos else s.positions a
    totalDeps := fun id => if id = assetId then s.totalDeps id - amount else s.totalDeps id }
  -- Check health factor after withdrawal
  let hf := healthFactor newState msg.sender s.supportedAssets
  require (hf ≥ MIN_HEALTH_FACTOR) "Lending: withdrawal would make position unhealthy"
  pure newState

/-- Borrow against collateral -/
def borrow (s : LendingPoolState) (msg : MsgContext) (assetId : AssetId) (amount : Amount) (currentTime : Timestamp) :
    Result LendingPoolState := do
  require (amount > 0) "Lending: borrow amount must be positive"
  let config := s.assetConfigs assetId
  require (config.isBorrowable) "Lending: asset is not borrowable"
  require (s.totalDeps assetId ≥ s.totalBors assetId + amount) "Lending: insufficient liquidity"
  -- Accrue interest first
  let s := accrueInterest s msg.sender currentTime
  let pos := s.positions msg.sender
  let newBorrowed := pos.borrowed assetId + amount
  let newPos := { pos with
    borrowed := fun id => if id = assetId then newBorrowed else pos.borrowed id
    lastUpdate := currentTime }
  let newState := { s with
    positions := fun a => if a = msg.sender then newPos else s.positions a
    totalBors := fun id => if id = assetId then s.totalBors id + amount else s.totalBors id }
  -- Check health factor after borrowing
  let hf := healthFactor newState msg.sender s.supportedAssets
  require (hf ≥ MIN_HEALTH_FACTOR) "Lending: borrow would make position unhealthy"
  pure newState

/-- Repay borrowed amount -/
def repay (s : LendingPoolState) (msg : MsgContext) (assetId : AssetId) (amount : Amount) (currentTime : Timestamp) :
    Result LendingPoolState := do
  require (amount > 0) "Lending: repay amount must be positive"
  let s := accrueInterest s msg.sender currentTime
  let pos := s.positions msg.sender
  let totalOwed := pos.borrowed assetId + pos.accruedInterest assetId
  require (totalOwed > 0) "Lending: nothing to repay"
  -- Calculate how much goes to interest vs principal
  let actualRepay := min amount totalOwed
  let interestPayment := min actualRepay (pos.accruedInterest assetId)
  let principalPayment := actualRepay - interestPayment
  let newPos := { pos with
    borrowed := fun id => if id = assetId then pos.borrowed id - principalPayment else pos.borrowed id
    accruedInterest := fun id => if id = assetId then pos.accruedInterest id - interestPayment else pos.accruedInterest id
    lastUpdate := currentTime }
  pure { s with
    positions := fun a => if a = msg.sender then newPos else s.positions a
    totalBors := fun id => if id = assetId then s.totalBors id - principalPayment else s.totalBors id }

/-- Liquidate an undercollateralized position -/
def liquidate (s : LendingPoolState) (msg : MsgContext) (borrower : Address)
    (debtAsset collateralAsset : AssetId) (debtAmount : Amount) (currentTime : Timestamp) :
    Result LendingPoolState := do
  require (borrower ≠ msg.sender) "Lending: cannot liquidate own position"
  require (debtAmount > 0) "Lending: liquidation amount must be positive"
  -- Accrue interest for the borrower
  let s := accrueInterest s borrower currentTime
  -- Check if position is liquidatable
  require (isLiquidatable s borrower s.supportedAssets) "Lending: position is healthy"
  let pos := s.positions borrower
  let totalDebt := pos.borrowed debtAsset + pos.accruedInterest debtAsset
  let actualDebt := min debtAmount totalDebt
  -- Calculate collateral to seize (with bonus)
  let debtConfig := s.assetConfigs debtAsset
  let collateralConfig := s.assetConfigs collateralAsset
  let debtValue := actualDebt * debtConfig.price
  let collateralToSeize := debtValue * (BASIS_POINTS + LIQUIDATION_BONUS) / (collateralConfig.price * BASIS_POINTS)
  require (pos.collateral collateralAsset ≥ collateralToSeize) "Lending: insufficient collateral to seize"
  -- Update borrower's position
  let interestPayment := min actualDebt (pos.accruedInterest debtAsset)
  let principalPayment := actualDebt - interestPayment
  let newBorrowerPos := { pos with
    borrowed := fun id => if id = debtAsset then pos.borrowed id - principalPayment else pos.borrowed id
    accruedInterest := fun id => if id = debtAsset then pos.accruedInterest id - interestPayment else pos.accruedInterest id
    collateral := fun id => if id = collateralAsset then pos.collateral id - collateralToSeize else pos.collateral id
    lastUpdate := currentTime }
  -- Update liquidator's position (receives collateral)
  let liquidatorPos := s.positions msg.sender
  let newLiquidatorPos := { liquidatorPos with
    collateral := fun id => if id = collateralAsset then liquidatorPos.collateral id + collateralToSeize else liquidatorPos.collateral id
    lastUpdate := currentTime }
  pure { s with
    positions := fun a =>
      if a = borrower then newBorrowerPos
      else if a = msg.sender then newLiquidatorPos
      else s.positions a
    totalBors := fun id => if id = debtAsset then s.totalBors id - principalPayment else s.totalBors id }

/-! ## View Functions -/

/-- Get user's health factor -/
def getUserHealthFactor (s : LendingPoolState) (user : Address) : Nat :=
  healthFactor s user s.supportedAssets

/-- Get user's total collateral value -/
def getUserCollateralValue (s : LendingPoolState) (user : Address) : Amount :=
  totalCollateralValue s user s.supportedAssets

/-- Get user's total borrow value -/
def getUserBorrowValue (s : LendingPoolState) (user : Address) : Amount :=
  totalBorrowValue s user s.supportedAssets

/-! ## Helper Lemmas -/

/-- accrueInterest preserves totalDeps -/
theorem accrueInterest_preserves_totalDeps (s : LendingPoolState) (user : Address) (t : Timestamp) :
    (accrueInterest s user t).totalDeps = s.totalDeps := by
  unfold accrueInterest
  simp only
  split <;> rfl

/-- accrueInterest preserves totalBors -/
theorem accrueInterest_preserves_totalBors (s : LendingPoolState) (user : Address) (t : Timestamp) :
    (accrueInterest s user t).totalBors = s.totalBors := by
  unfold accrueInterest
  simp only
  split <;> rfl

/-- accrueInterest preserves assetConfigs -/
theorem accrueInterest_preserves_assetConfigs (s : LendingPoolState) (user : Address) (t : Timestamp) :
    (accrueInterest s user t).assetConfigs = s.assetConfigs := by
  unfold accrueInterest
  simp only
  split <;> rfl

/-- accrueInterest preserves collateral for the user -/
theorem accrueInterest_preserves_collateral (s : LendingPoolState) (user : Address) (t : Timestamp) (assetId : AssetId) :
    ((accrueInterest s user t).positions user).collateral assetId = (s.positions user).collateral assetId := by
  unfold accrueInterest
  simp only
  split
  · rfl
  · simp only [ite_true]

/-- accrueInterest preserves supportedAssets -/
theorem accrueInterest_preserves_supportedAssets (s : LendingPoolState) (user : Address) (t : Timestamp) :
    (accrueInterest s user t).supportedAssets = s.supportedAssets := by
  unfold accrueInterest
  simp only
  split <;> rfl

/-! ## Basic Properties -/

/-- Deposit increases total deposits -/
theorem deposit_increases_total (s s' : LendingPoolState) (msg : MsgContext)
    (assetId : AssetId) (amount : Amount) (t : Timestamp)
    (_h_pos : amount > 0)
    (h : deposit s msg assetId amount t = Result.ok s') :
    s'.totalDeps assetId = s.totalDeps assetId + amount := by
  unfold deposit require at h
  simp only [Bind.bind, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Pure.pure, Result.ok.injEq] at h
  cases h
  simp only [accrueInterest_preserves_totalDeps, ite_true]

/-- Deposit increases user's collateral -/
theorem deposit_increases_collateral (s s' : LendingPoolState) (msg : MsgContext)
    (assetId : AssetId) (amount : Amount) (t : Timestamp)
    (h : deposit s msg assetId amount t = Result.ok s') :
    (s'.positions msg.sender).collateral assetId ≥ (s.positions msg.sender).collateral assetId := by
  unfold deposit require at h
  simp only [Bind.bind, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Pure.pure, Result.ok.injEq] at h
  cases h
  simp only [ite_true, ge_iff_le]
  rw [accrueInterest_preserves_collateral]
  exact Nat.le_add_right _ _

/-- Zero deposit reverts -/
theorem deposit_zero_reverts (s : LendingPoolState) (msg : MsgContext) (assetId : AssetId) (t : Timestamp) :
    ∃ m, deposit s msg assetId 0 t = Result.revert m := by
  refine ⟨"Lending: deposit amount must be positive", ?_⟩
  unfold deposit require
  simp [Bind.bind, Result.bind]

/-- Borrow without sufficient liquidity reverts -/
theorem borrow_insufficient_liquidity_reverts (s : LendingPoolState) (msg : MsgContext)
    (assetId : AssetId) (amount : Amount) (t : Timestamp)
    (h_pos : amount > 0)
    (h_borrowable : (s.assetConfigs assetId).isBorrowable = true)
    (h_liquidity : s.totalDeps assetId < s.totalBors assetId + amount) :
    ∃ m, borrow s msg assetId amount t = Result.revert m := by
  refine ⟨"Lending: insufficient liquidity", ?_⟩
  unfold borrow require
  simp only [Bind.bind, Result.bind, decide_eq_true_eq]
  simp only [h_pos, ↓reduceIte, h_borrowable]
  simp only [Nat.not_le.mpr h_liquidity, ↓reduceIte]

/-- Liquidation of healthy position reverts

    The proof follows the logic that:
    1. The first two requires pass (borrower ≠ msg.sender, amount > 0)
    2. After accrueInterest, isLiquidatable check fails per h_healthy
    3. The accrued state preserves supportedAssets (accrueInterest_preserves_supportedAssets)

    TODO: Complete proof requires careful tracking through do-notation let bindings. -/
theorem liquidate_healthy_reverts (s : LendingPoolState) (msg : MsgContext)
    (borrower : Address) (debtAsset collateralAsset : AssetId) (amount : Amount) (t : Timestamp)
    (_h_not_self : borrower ≠ msg.sender)
    (_h_pos : amount > 0)
    (_h_healthy : isLiquidatable (accrueInterest s borrower t) borrower s.supportedAssets = false) :
    ∃ m, liquidate s msg borrower debtAsset collateralAsset amount t = Result.revert m := by
  sorry -- Proof requires careful handling of do-notation let bindings

end Lab.Lending
