import Lab.Vault.Contracts.Interface
import Lab.Vault.Contracts.StakingVault
import Lab.Vault.Properties.Invariants
import Lab.Vault.Model.TransitionSystem

/-!
# Vault/Staking Verification Laboratory

Formal verification environment for staking vault contracts.

## Quick Start

```lean
import Lab.Vault

open Lab.Vault

-- Create a vault with 100 rewards per block
def myVault := StakingVaultState.init 100 0

-- Verify properties
#check deposit_increases_shares
#check withdraw_decreases_shares
```

## Structure

- **Contracts/Interface.lean** - Abstract vault interface and typeclasses
- **Contracts/StakingVault.lean** - Concrete staking implementation
- **Properties/Invariants.lean** - Vault invariants and safety properties

## Key Properties

1. **Share-based accounting**: Users receive shares proportional to deposits
2. **Reward distribution**: Rewards accumulate based on share ownership
3. **Solvency**: Vault always has enough assets to cover withdrawals
-/
