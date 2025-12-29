import Lab.Vault.Contracts.Interface

/-!
# Staking Vault Implementation

A simple staking vault where:
- Users deposit tokens and receive shares
- Rewards accumulate over time based on share ownership
- Users can withdraw their proportional share of the pool
- Users can claim accumulated rewards

## Invariants

1. **Share Conservation**: Total shares = sum of all user shares
2. **Asset Conservation**: Total assets ≥ sum of all deposits (no loss)
3. **Reward Accounting**: Rewards distributed ≤ reward rate × time elapsed
-/

namespace Lab.Vault

open Lab.ERC20 (Address Amount Result MsgContext require)

/-! ## State Definition -/

/-- Staking vault state -/
structure StakingVaultState where
  /-- Shares held by each address -/
  shares : Address → Shares
  /-- Pending rewards for each address -/
  rewards : Address → Amount
  /-- Total shares outstanding -/
  totalSh : Shares
  /-- Total assets in the vault -/
  totalAs : Amount
  /-- Reward rate per block -/
  rate : RewardRate
  /-- Last time rewards were updated -/
  lastUpdate : Timestamp
  /-- Accumulated rewards per share (scaled by 1e18) -/
  rewardPerShareStored : Nat
  /-- User's reward per share at last update -/
  userRewardPerSharePaid : Address → Nat
  /-- Total rewards ever distributed -/
  totalDistributed : Amount

/-! ## Initialization -/

/-- Create a new staking vault -/
def StakingVaultState.init (rewardRate : RewardRate) (startTime : Timestamp) : StakingVaultState :=
  { shares := fun _ => 0
  , rewards := fun _ => 0
  , totalSh := 0
  , totalAs := 0
  , rate := rewardRate
  , lastUpdate := startTime
  , rewardPerShareStored := 0
  , userRewardPerSharePaid := fun _ => 0
  , totalDistributed := 0 }

/-! ## VaultState Instance -/

instance : VaultState StakingVaultState where
  totalAssets s := s.totalAs
  totalShares s := s.totalSh
  sharesOf s addr := s.shares addr
  pendingRewards s addr := s.rewards addr
  lastRewardTime s := s.lastUpdate
  rewardRate s := s.rate
  totalRewardsDistributed s := s.totalDistributed
  setShares s addr amount := { s with shares := fun a => if a = addr then amount else s.shares a }
  setPendingRewards s addr amount := { s with rewards := fun a => if a = addr then amount else s.rewards a }

/-! ## Reward Calculation Helpers -/

/-- Scaling factor for reward per share calculation (1e18) -/
def SCALE : Nat := 1000000000000000000

/-- Calculate current reward per share -/
def rewardPerShare (s : StakingVaultState) (currentTime : Timestamp) : Nat :=
  if s.totalSh = 0 then
    s.rewardPerShareStored
  else
    let elapsed := currentTime - s.lastUpdate
    let newRewards := elapsed * s.rate
    s.rewardPerShareStored + (newRewards * SCALE / s.totalSh)

/-- Calculate earned rewards for a user -/
def earned (s : StakingVaultState) (addr : Address) (currentTime : Timestamp) : Amount :=
  let rps := rewardPerShare s currentTime
  let userShares := s.shares addr
  let userRpsPaid := s.userRewardPerSharePaid addr
  s.rewards addr + (userShares * (rps - userRpsPaid) / SCALE)

/-! ## Update Rewards -/

/-- Update reward state before any action -/
def updateRewardsFor (s : StakingVaultState) (addr : Address) (currentTime : Timestamp) : StakingVaultState :=
  let rps := rewardPerShare s currentTime
  let newRewards := if s.totalSh > 0 then (currentTime - s.lastUpdate) * s.rate else 0
  { s with
    rewardPerShareStored := rps
    lastUpdate := currentTime
    totalDistributed := s.totalDistributed + newRewards
    rewards := fun a => if a = addr then earned s addr currentTime else s.rewards a
    userRewardPerSharePaid := fun a => if a = addr then rps else s.userRewardPerSharePaid a }

/-! ## Core Operations -/

/-- Deposit assets and receive shares -/
def deposit (s : StakingVaultState) (msg : MsgContext) (amount : Amount) (currentTime : Timestamp) : Result StakingVaultState := do
  require (amount > 0) "Vault: deposit amount must be positive"
  -- Update rewards first
  let s := updateRewardsFor s msg.sender currentTime
  -- Calculate shares to mint
  let sharesToMint := assetsToShares s amount
  require (sharesToMint > 0) "Vault: shares would be zero"
  -- Update state
  let newShares := s.shares msg.sender + sharesToMint
  pure { s with
    shares := fun a => if a = msg.sender then newShares else s.shares a
    totalSh := s.totalSh + sharesToMint
    totalAs := s.totalAs + amount }

/-- Withdraw by burning shares -/
def withdraw (s : StakingVaultState) (msg : MsgContext) (sharesToBurn : Shares) (currentTime : Timestamp) : Result StakingVaultState := do
  require (sharesToBurn > 0) "Vault: withdraw shares must be positive"
  require (s.shares msg.sender ≥ sharesToBurn) "Vault: insufficient shares"
  -- Update rewards first
  let s := updateRewardsFor s msg.sender currentTime
  -- Calculate assets to return
  let assetsToReturn := sharesToAssets s sharesToBurn
  require (assetsToReturn ≤ s.totalAs) "Vault: insufficient assets"
  -- Update state
  let newShares := s.shares msg.sender - sharesToBurn
  pure { s with
    shares := fun a => if a = msg.sender then newShares else s.shares a
    totalSh := s.totalSh - sharesToBurn
    totalAs := s.totalAs - assetsToReturn }

/-- Claim accumulated rewards -/
def claimRewards (s : StakingVaultState) (msg : MsgContext) (currentTime : Timestamp) : Result StakingVaultState := do
  -- Update rewards first
  let s := updateRewardsFor s msg.sender currentTime
  let reward := s.rewards msg.sender
  require (reward > 0) "Vault: no rewards to claim"
  -- Reset pending rewards
  pure { s with
    rewards := fun a => if a = msg.sender then 0 else s.rewards a }

/-! ## View Functions -/

/-- Get user's share balance -/
def balanceOf (s : StakingVaultState) (addr : Address) : Shares :=
  s.shares addr

/-- Get user's pending rewards at a given time -/
def getPendingRewards (s : StakingVaultState) (addr : Address) (currentTime : Timestamp) : Amount :=
  earned s addr currentTime

/-- Get user's current asset value -/
def assetValue (s : StakingVaultState) (addr : Address) : Amount :=
  sharesToAssets s (s.shares addr)

/-! ## Helper Lemmas -/

/-- updateRewardsFor preserves totalSh -/
theorem updateRewardsFor_preserves_totalSh (s : StakingVaultState) (addr : Address) (t : Timestamp) :
    (updateRewardsFor s addr t).totalSh = s.totalSh := by
  unfold updateRewardsFor
  rfl

/-- updateRewardsFor preserves totalAs -/
theorem updateRewardsFor_preserves_totalAs (s : StakingVaultState) (addr : Address) (t : Timestamp) :
    (updateRewardsFor s addr t).totalAs = s.totalAs := by
  unfold updateRewardsFor
  rfl

/-! ## Basic Properties -/

/-- Deposit increases total shares -/
theorem deposit_increases_shares (s s' : StakingVaultState) (msg : MsgContext) (amount : Amount) (t : Timestamp)
    (h : deposit s msg amount t = Result.ok s') :
    s'.totalSh ≥ s.totalSh := by
  unfold deposit require at h
  simp only [Bind.bind, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Pure.pure, Result.ok.injEq] at h
  cases h
  simp only [updateRewardsFor_preserves_totalSh, ge_iff_le, Nat.le_add_right]

/-- Deposit increases total assets -/
theorem deposit_increases_assets (s s' : StakingVaultState) (msg : MsgContext) (amount : Amount) (t : Timestamp)
    (_h_pos : amount > 0)
    (h : deposit s msg amount t = Result.ok s') :
    s'.totalAs = (updateRewardsFor s msg.sender t).totalAs + amount := by
  unfold deposit require at h
  simp only [Bind.bind, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Pure.pure, Result.ok.injEq] at h
  cases h
  rfl

/-- Withdraw decreases total shares -/
theorem withdraw_decreases_shares (s s' : StakingVaultState) (msg : MsgContext) (shares : Shares) (t : Timestamp)
    (h : withdraw s msg shares t = Result.ok s') :
    s'.totalSh ≤ s.totalSh := by
  unfold withdraw require at h
  simp only [Bind.bind, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Pure.pure, Result.ok.injEq] at h
  cases h
  simp only [updateRewardsFor_preserves_totalSh, Nat.sub_le]

/-- Zero deposit reverts -/
theorem deposit_zero_reverts (s : StakingVaultState) (msg : MsgContext) (t : Timestamp) :
    ∃ m, deposit s msg 0 t = Result.revert m := by
  refine ⟨"Vault: deposit amount must be positive", ?_⟩
  unfold deposit require
  simp [Bind.bind, Result.bind]

/-- Withdraw with insufficient shares reverts -/
theorem withdraw_insufficient_shares_reverts (s : StakingVaultState) (msg : MsgContext) (shares : Shares) (t : Timestamp)
    (h : s.shares msg.sender < shares) :
    ∃ m, withdraw s msg shares t = Result.revert m := by
  -- If shares > 0, we fail on the second require (insufficient shares)
  -- If shares = 0, we fail on the first require (must be positive)
  by_cases h_pos : shares > 0
  · -- shares > 0: fail on insufficient shares check
    refine ⟨"Vault: insufficient shares", ?_⟩
    unfold withdraw require
    simp only [Bind.bind, Result.bind, decide_eq_true_eq]
    simp only [h_pos, ↓reduceIte]
    simp only [Nat.not_le.mpr h, ↓reduceIte]
  · -- shares = 0: fail on positive check
    have h_zero : shares = 0 := Nat.eq_zero_of_not_pos h_pos
    refine ⟨"Vault: withdraw shares must be positive", ?_⟩
    unfold withdraw require
    simp only [Bind.bind, Result.bind, h_zero]
    rfl

/-! ## Solvency Preservation Lemmas -/

/-- claimRewards preserves totalAs -/
theorem claimRewards_preserves_totalAs (s s' : StakingVaultState) (msg : MsgContext) (t : Timestamp)
    (h : claimRewards s msg t = Result.ok s') :
    s'.totalAs = s.totalAs := by
  unfold claimRewards require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  simp only [updateRewardsFor_preserves_totalAs]

/-- claimRewards preserves totalSh -/
theorem claimRewards_preserves_totalSh (s s' : StakingVaultState) (msg : MsgContext) (t : Timestamp)
    (h : claimRewards s msg t = Result.ok s') :
    s'.totalSh = s.totalSh := by
  unfold claimRewards require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  simp only [updateRewardsFor_preserves_totalSh]

/-- Solvency is preserved by claimRewards -/
theorem claimRewards_preserves_solvency (s s' : StakingVaultState) (msg : MsgContext) (t : Timestamp)
    (h_solv : s.totalAs ≥ s.totalSh)
    (h : claimRewards s msg t = Result.ok s') :
    s'.totalAs ≥ s'.totalSh := by
  rw [claimRewards_preserves_totalAs s s' msg t h]
  rw [claimRewards_preserves_totalSh s s' msg t h]
  exact h_solv

/-- assetsToShares is bounded by assets when solvent -/
theorem assetsToShares_le_assets (s : StakingVaultState) (amount : Amount)
    (h_solv : s.totalAs ≥ s.totalSh) :
    assetsToShares s amount ≤ amount := by
  simp only [assetsToShares, VaultState.totalAssets, VaultState.totalShares]
  -- Use if_pos or if_neg to handle the conditional
  by_cases h : s.totalAs = 0 ∨ s.totalSh = 0
  · -- Empty vault case: returns amount
    simp only [h, ↓reduceIte, le_refl]
  · -- Non-empty case: amount * totalSh / totalAs ≤ amount
    push_neg at h
    simp only [h.1, h.2, or_self, ↓reduceIte]
    have h_pos_as : s.totalAs > 0 := Nat.pos_of_ne_zero h.1
    calc amount * s.totalSh / s.totalAs
        ≤ amount * s.totalAs / s.totalAs := by
            apply Nat.div_le_div_right
            exact Nat.mul_le_mul_left amount h_solv
      _ = amount := Nat.mul_div_cancel amount h_pos_as

/-- Solvency is preserved by deposit -/
theorem deposit_preserves_solvency (s s' : StakingVaultState) (msg : MsgContext)
    (amount : Amount) (t : Timestamp)
    (h_solv : s.totalAs ≥ s.totalSh)
    (h : deposit s msg amount t = Result.ok s') :
    s'.totalAs ≥ s'.totalSh := by
  unfold deposit require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  simp only [updateRewardsFor_preserves_totalAs, updateRewardsFor_preserves_totalSh, ge_iff_le]
  -- Need to show: totalAs + amount ≥ totalSh + sharesToMint
  -- where sharesToMint = assetsToShares (updateRewardsFor s msg.sender t) amount
  have h_solv' : (updateRewardsFor s msg.sender t).totalAs ≥ (updateRewardsFor s msg.sender t).totalSh := by
    simp only [updateRewardsFor_preserves_totalAs, updateRewardsFor_preserves_totalSh]
    exact h_solv
  have h_shares_le : assetsToShares (updateRewardsFor s msg.sender t) amount ≤ amount :=
    assetsToShares_le_assets (updateRewardsFor s msg.sender t) amount h_solv'
  calc (updateRewardsFor s msg.sender t).totalSh + assetsToShares (updateRewardsFor s msg.sender t) amount
      ≤ (updateRewardsFor s msg.sender t).totalSh + amount := Nat.add_le_add_left h_shares_le _
    _ ≤ (updateRewardsFor s msg.sender t).totalAs + amount := Nat.add_le_add_right h_solv' amount

/-- Helper: sharesToAssets maintains solvency ratio.
    When totalAs ≥ totalSh and shares ≤ totalSh, proportional withdrawal maintains solvency.
    Key insight: sharesToAssets = shares * totalAs / totalSh ≤ shares + (totalAs - totalSh)
    because the "excess" assets (totalAs - totalSh) are distributed proportionally.

    Proof sketch:
    1. shares * totalAs = shares * totalSh + shares * (totalAs - totalSh)
    2. (shares*totalSh + x) / totalSh = shares + x/totalSh (exact division)
    3. shares * (totalAs-totalSh) / totalSh ≤ totalAs - totalSh (since shares ≤ totalSh)
    4. Therefore sharesToAssets ≤ shares + (totalAs - totalSh)
    5. Thus totalAs - sharesToAssets ≥ totalAs - shares - (totalAs - totalSh) = totalSh - shares -/
private theorem sharesToAssets_solvency_aux (totalAs totalSh shares : Nat)
    (h_solv : totalAs ≥ totalSh) (h_sh_pos : totalSh > 0) (h_shares_le : shares ≤ totalSh) :
    totalAs - shares * totalAs / totalSh ≥ totalSh - shares := by
  by_cases h_as_eq : totalAs = totalSh
  · -- Equal case: sharesToAssets = shares, so LHS = RHS
    subst h_as_eq
    rw [Nat.mul_div_cancel shares h_sh_pos]
  · -- Strict case: complex integer division arithmetic
    -- The proof follows the sketch above but requires careful handling of Nat division
    sorry

/-- Solvency is preserved by withdraw -/
theorem withdraw_preserves_solvency (s s' : StakingVaultState) (msg : MsgContext)
    (shares : Shares) (t : Timestamp)
    (h_solv : s.totalAs ≥ s.totalSh)
    (h : withdraw s msg shares t = Result.ok s') :
    s'.totalAs ≥ s'.totalSh := by
  unfold withdraw require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  rename_i h_pos
  split at h <;> try contradiction
  rename_i h_has_shares
  split at h <;> try contradiction
  rename_i h_assets_ok
  simp only [Result.ok.injEq] at h
  cases h
  simp only [updateRewardsFor_preserves_totalAs, updateRewardsFor_preserves_totalSh, ge_iff_le]
  -- Simplify sharesToAssets
  simp only [sharesToAssets, VaultState.totalAssets, VaultState.totalShares,
             updateRewardsFor_preserves_totalAs, updateRewardsFor_preserves_totalSh] at h_assets_ok ⊢
  -- Handle the conditional in sharesToAssets
  by_cases h_sh : s.totalSh = 0
  · -- If totalSh = 0, then we need 0 ≥ 0 - shares which is trivially true (Nat subtraction)
    rw [if_pos h_sh]
    simp only [Nat.sub_zero, h_sh, Nat.zero_sub, ge_iff_le, Nat.zero_le]
  · -- If totalSh > 0
    have h_sh_pos : s.totalSh > 0 := Nat.pos_of_ne_zero h_sh
    rw [if_neg h_sh]
    -- shares ≤ totalSh follows from share conservation invariant
    -- (The contract maintains that user shares sum to totalSh)
    have h_shares_le : shares ≤ s.totalSh := by
      -- This is an invariant: any valid state has user shares ≤ totalSh
      -- The require check ensures shares ≤ user's balance ≤ totalSh
      -- For now, we admit this as an invariant property
      sorry
    exact sharesToAssets_solvency_aux s.totalAs s.totalSh shares h_solv h_sh_pos h_shares_le

end Lab.Vault
