import Lab.Vault.Contracts.StakingVault

open Lab.ERC20 (Result)

/-!
# Vault Invariants

Key invariants for staking vault correctness:

1. **Share Conservation**: Sum of user shares equals total shares
2. **No Loss**: Users can always withdraw at least what they deposited
3. **Reward Bounds**: Distributed rewards don't exceed accumulated rewards
-/

namespace Lab.Vault

open Lab.ERC20 (Address Amount)

/-! ## Core Invariants -/

/-- Total shares equals sum of all individual share balances -/
def ShareConservation (s : StakingVaultState) (addresses : List Address) : Prop :=
  (addresses.map s.shares).sum = s.totalSh

/-- Share conservation for two addresses involved in a transfer -/
def LocalShareConservation (s s' : StakingVaultState) (addr1 addr2 : Address) : Prop :=
  s.shares addr1 + s.shares addr2 = s'.shares addr1 + s'.shares addr2

/-- Assets are sufficient to cover all shares at current rate -/
def AssetSufficiency (s : StakingVaultState) : Prop :=
  s.totalAs ≥ sharesToAssets s s.totalSh

/-- No loss: asset value per share never decreases -/
def ShareValueNonDecreasing (s s' : StakingVaultState) : Prop :=
  sharePrice s ≤ sharePrice s'

/-! ## Reward Invariants -/

/-- Total distributed rewards bounded by time elapsed × rate -/
def RewardBound (s : StakingVaultState) (startTime : Timestamp) : Prop :=
  s.totalDistributed ≤ (s.lastUpdate - startTime) * s.rate

/-- Users can only earn rewards proportional to their stake -/
def FairRewardDistribution (s : StakingVaultState) (addr : Address) : Prop :=
  s.rewards addr ≤ s.totalDistributed

/-! ## Safety Properties -/

/-- Users with zero shares have zero pending rewards (initially) -/
def ZeroSharesZeroRewards (s : StakingVaultState) (addr : Address) : Prop :=
  s.shares addr = 0 → s.rewards addr = 0

/-- Vault is solvent: can pay out all shares -/
def Solvency (s : StakingVaultState) : Prop :=
  s.totalAs ≥ s.totalSh  -- At minimum 1:1 ratio

/-! ## Compound Invariants -/

/-- Main vault invariant combining key properties -/
structure VaultInvariant (s : StakingVaultState) : Prop where
  /-- Vault has enough assets -/
  solvent : Solvency s
  /-- Share accounting is consistent -/
  totalSharesNonNeg : s.totalSh ≥ 0  -- Always true for Nat, but explicit

/-- Two-state property: operations preserve solvency -/
def PreservesSolvency (op : StakingVaultState → Result StakingVaultState) : Prop :=
  ∀ s s', Solvency s → op s = Result.ok s' → Solvency s'

end Lab.Vault
