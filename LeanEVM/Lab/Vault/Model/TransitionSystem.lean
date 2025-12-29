import Lab.Vault.Contracts.StakingVault
import Lab.ERC20.Model.TransitionSystem

/-!
# Staking Vault Transition System

Models the StakingVault as a ContractTransitionSystem for formal verification.

## Key Properties

1. **Share Conservation**: Total shares = sum of individual shares
2. **Solvency**: Total assets ≥ total shares (at minimum 1:1)
3. **Reward Monotonicity**: Total distributed rewards only increase
-/

namespace Lab.Vault.Model

open Lab.ERC20 (Address Amount Result MsgContext)
open Lab.ERC20.Model (ContractTransitionSystem)
open Lab.Vault

/-! ## Predicates -/

/-- Initial state with given reward rate -/
def VaultInit (rate : RewardRate) (startTime : Timestamp) (s : StakingVaultState) : Prop :=
  s = StakingVaultState.init rate startTime

/-- Transition relation: any successful vault operation -/
def VaultNext (s s' : StakingVaultState) : Prop :=
  (∃ msg amount t, deposit s msg amount t = Result.ok s') ∨
  (∃ msg shares t, withdraw s msg shares t = Result.ok s') ∨
  (∃ msg t, claimRewards s msg t = Result.ok s')

/-- Safety: vault is solvent -/
def VaultSafe (s : StakingVaultState) : Prop :=
  s.totalAs ≥ s.totalSh

/-- Invariant: solvency plus share/asset ratio bounds -/
def VaultInv (s : StakingVaultState) : Prop :=
  s.totalAs ≥ s.totalSh ∧
  (s.totalSh = 0 → s.totalAs = 0 ∨ s.totalAs > 0)

/-! ## Transition System Instance -/

/-- Staking vault as a transition system -/
def vaultTS (rate : RewardRate) (startTime : Timestamp) : ContractTransitionSystem StakingVaultState :=
  { init := VaultInit rate startTime
  , next := VaultNext
  , safe := VaultSafe
  , inv := VaultInv }

/-! ## Invariant Proofs -/

/-- Initial states satisfy the invariant -/
theorem vault_invInit (rate : RewardRate) (startTime : Timestamp) :
    ContractTransitionSystem.invInit' (vaultTS rate startTime) := by
  intro s h_init
  simp only [vaultTS, VaultInit, VaultInv] at h_init ⊢
  rw [h_init]
  simp only [StakingVaultState.init, ge_iff_le, le_refl, true_and]
  intro _; left; trivial

/-- Invariant implies safety -/
theorem vault_invSafe (rate : RewardRate) (startTime : Timestamp) :
    ContractTransitionSystem.invSafe' (vaultTS rate startTime) := by
  intro s h_inv
  simp only [vaultTS, VaultInv, VaultSafe] at h_inv ⊢
  exact h_inv.1

/-- Helper: second part of invariant is always true -/
private theorem share_ratio_trivial (s : StakingVaultState) :
    s.totalSh = 0 → s.totalAs = 0 ∨ s.totalAs > 0 := by
  intro _
  by_cases h : s.totalAs = 0
  · left; exact h
  · right; exact Nat.pos_of_ne_zero h

/-- Transitions preserve the invariant -/
theorem vault_invConsecution (rate : RewardRate) (startTime : Timestamp) :
    ContractTransitionSystem.invConsecution' (vaultTS rate startTime) := by
  intro s s' h_inv h_next
  simp only [vaultTS, VaultInv] at h_inv ⊢
  rcases h_next with ⟨msg, amount, t, h_deposit⟩ |
                     ⟨msg, shares, t, h_withdraw⟩ |
                     ⟨msg, t, h_claim⟩
  -- Case 1: deposit - solvency preserved
  · exact ⟨deposit_preserves_solvency s s' msg amount t h_inv.1 h_deposit, share_ratio_trivial s'⟩
  -- Case 2: withdraw - solvency preserved
  · exact ⟨withdraw_preserves_solvency s s' msg shares t h_inv.1 h_withdraw, share_ratio_trivial s'⟩
  -- Case 3: claimRewards - solvency trivially preserved
  · exact ⟨claimRewards_preserves_solvency s s' msg t h_inv.1 h_claim, share_ratio_trivial s'⟩

/-- The invariant is inductive -/
theorem vault_invInductive (rate : RewardRate) (startTime : Timestamp) :
    ContractTransitionSystem.invInductive' (vaultTS rate startTime) :=
  ⟨vault_invInit rate startTime, vault_invConsecution rate startTime, vault_invSafe rate startTime⟩

/-! ## Two-State Properties -/

/-- Share conservation during operations -/
def ConservesShares (addr1 addr2 : Address) : StakingVaultState → StakingVaultState → Prop :=
  fun s s' => s.shares addr1 + s.shares addr2 = s'.shares addr1 + s'.shares addr2

/-- Total assets change tracking -/
def AssetDelta : StakingVaultState → StakingVaultState → Int :=
  fun s s' => (s'.totalAs : Int) - (s.totalAs : Int)

end Lab.Vault.Model
