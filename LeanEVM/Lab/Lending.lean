import Lab.Lending.Contracts.Interface
import Lab.Lending.Contracts.LendingPool
import Lab.Lending.Properties.Invariants
import Lab.Lending.Model.TransitionSystem

/-!
# Lending Protocol Verification Laboratory

Formal verification environment for Aave-style lending protocols.

## Quick Start

```lean
import Lab.Lending

open Lab.Lending

-- Create a lending pool
def myPool := LendingPoolState.init ⟨1⟩  -- admin address

-- Add a supported asset
def ethConfig : AssetConfig := {
  isCollateral := true
  isBorrowable := true
  collateralFactor := 7500  -- 75% LTV
  liquidationThreshold := 8000  -- 80%
  borrowRate := 50  -- 0.5% per block
  price := 1000
}

-- Verify properties
#check deposit_increases_total
#check liquidate_healthy_reverts
```

## Structure

- **Contracts/Interface.lean** - Abstract lending interface
- **Contracts/LendingPool.lean** - Concrete pool implementation
- **Properties/Invariants.lean** - Lending invariants

## Key Concepts

1. **Collateral Factor**: Maximum borrow as % of collateral (e.g., 75%)
2. **Health Factor**: Collateral value / Borrow value (< 1 = liquidatable)
3. **Liquidation**: Third parties repay debt and seize collateral + bonus
4. **Interest Accrual**: Borrowed amounts accumulate interest over time

## Verified Properties

- Deposits increase collateral and total deposits
- Borrows require sufficient collateral
- Liquidation requires unhealthy position
- Health factor maintained after allowed operations
-/
