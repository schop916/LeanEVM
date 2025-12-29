import Lab.ERC20.Contracts.Interface

/-!
# Vault/Staking Contract Interface

Defines the abstract interface for staking vaults where users:
1. Deposit tokens to earn rewards
2. Withdraw tokens (with optional lock period)
3. Claim accumulated rewards

## Design

The vault follows a share-based model similar to ERC-4626:
- Users receive shares proportional to their deposit
- Shares appreciate as rewards accumulate
- Withdrawal returns tokens proportional to shares
-/

namespace Lab.Vault

open Lab.ERC20 (Address Amount Result MsgContext)

/-! ## Vault-Specific Types -/

/-- Timestamp (block number or unix timestamp) -/
abbrev Timestamp := Nat

/-- Share tokens representing stake ownership -/
abbrev Shares := Nat

/-- Reward rate per block/second -/
abbrev RewardRate := Nat

/-! ## Vault State Abstraction -/

/-- Abstract state for a staking vault -/
class VaultState (S : Type) where
  /-- Total tokens deposited in the vault -/
  totalAssets : S → Amount
  /-- Total shares issued -/
  totalShares : S → Shares
  /-- Shares held by an address -/
  sharesOf : S → Address → Shares
  /-- Pending rewards for an address -/
  pendingRewards : S → Address → Amount
  /-- Last reward update timestamp -/
  lastRewardTime : S → Timestamp
  /-- Reward rate per unit time -/
  rewardRate : S → RewardRate
  /-- Total rewards distributed -/
  totalRewardsDistributed : S → Amount
  /-- Set shares for an address -/
  setShares : S → Address → Shares → S
  /-- Set pending rewards for an address -/
  setPendingRewards : S → Address → Amount → S

/-! ## Vault Operations -/

/-- Operations for a staking vault -/
class VaultOps (S : Type) [VaultState S] where
  /-- Deposit tokens and receive shares -/
  deposit : S → MsgContext → Amount → Result S
  /-- Withdraw tokens by burning shares -/
  withdraw : S → MsgContext → Shares → Result S
  /-- Claim accumulated rewards -/
  claimRewards : S → MsgContext → Result S
  /-- Update reward accounting (called before state changes) -/
  updateRewards : S → Timestamp → S

/-! ## Helper Functions -/

/-- Convert assets to shares at current rate -/
def assetsToShares {S : Type} [VaultState S] (state : S) (assets : Amount) : Shares :=
  let total := VaultState.totalAssets state
  let shares := VaultState.totalShares state
  if total = 0 ∨ shares = 0 then
    assets  -- 1:1 for empty vault
  else
    assets * shares / total

/-- Convert shares to assets at current rate -/
def sharesToAssets {S : Type} [VaultState S] (state : S) (shares : Shares) : Amount :=
  let total := VaultState.totalAssets state
  let totalSh := VaultState.totalShares state
  if totalSh = 0 then
    0
  else
    shares * total / totalSh

/-! ## Share Price Properties -/

/-- Share price is the ratio of total assets to total shares -/
def sharePrice {S : Type} [VaultState S] (state : S) : Nat :=
  let total := VaultState.totalAssets state
  let shares := VaultState.totalShares state
  if shares = 0 then 1 else total / shares

/-- Shares are worth at least the deposited amount (no loss invariant) -/
def NoLossInvariant {S : Type} [VaultState S] (state : S) : Prop :=
  VaultState.totalAssets state ≥ VaultState.totalShares state

end Lab.Vault
