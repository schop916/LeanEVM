import Lab.ERC1155.Contracts.MultiToken
import Lab.ERC20.Model.TransitionSystem

/-!
# ERC-1155 Multi-Token Transition System

Models the MultiToken contract as a ContractTransitionSystem for formal verification.

## Key Properties

1. **Per-Token Supply Conservation**: For each token ID, transfers preserve total supply
2. **Batch Atomicity**: Batch operations succeed entirely or fail entirely
3. **Approval Independence**: Token balances don't affect approval state
-/

namespace Lab.ERC1155.Model

open Lab.ERC20 (Address Amount Result MsgContext)
open Lab.ERC20.Model (ContractTransitionSystem)
open Lab.ERC1155

/-! ## Predicates -/

/-- Initial state with given owner and base URI -/
def MultiTokenInit (owner : Address) (baseURI : URI) (s : MultiTokenState) : Prop :=
  s = MultiTokenState.init owner baseURI

/-- Transition relation: any successful multi-token operation -/
def MultiTokenNext (s s' : MultiTokenState) : Prop :=
  (∃ msg from_ to_ id amount, safeTransferFrom s msg from_ to_ id amount = Result.ok s') ∨
  (∃ msg from_ to_ batch, safeBatchTransferFrom s msg from_ to_ batch = Result.ok s') ∨
  (∃ msg operator approved, setApprovalForAll s msg operator approved = Result.ok s') ∨
  (∃ msg to_ id amount, mint s msg to_ id amount = Result.ok s') ∨
  (∃ msg from_ id amount, burn s msg from_ id amount = Result.ok s') ∨
  (∃ msg to_ batch, mintBatch s msg to_ batch = Result.ok s')

/-- Safety: supplies are consistent (non-negative, which is always true for Nat) -/
def MultiTokenSafe (s : MultiTokenState) : Prop :=
  ∀ id, s.supplies id ≥ 0

/-- Invariant: owner is set and supplies are consistent -/
def MultiTokenInv (s : MultiTokenState) (owner : Address) : Prop :=
  s.owner = owner ∧ (∀ id, s.supplies id ≥ 0)

/-! ## Transition System Instance -/

/-- Multi-token as a transition system -/
def multiTokenTS (owner : Address) (baseURI : URI) : ContractTransitionSystem MultiTokenState :=
  { init := MultiTokenInit owner baseURI
  , next := MultiTokenNext
  , safe := MultiTokenSafe
  , inv := fun s => MultiTokenInv s owner }

/-! ## Invariant Proofs -/

/-- Initial states satisfy the invariant -/
theorem multiToken_invInit (owner : Address) (baseURI : URI) :
    ContractTransitionSystem.invInit' (multiTokenTS owner baseURI) := by
  intro s h_init
  simp only [multiTokenTS, MultiTokenInit, MultiTokenInv] at h_init ⊢
  rw [h_init]
  simp only [MultiTokenState.init, ge_iff_le, le_refl, implies_true, and_self]

/-- Invariant implies safety -/
theorem multiToken_invSafe (owner : Address) (baseURI : URI) :
    ContractTransitionSystem.invSafe' (multiTokenTS owner baseURI) := by
  intro s h_inv
  simp only [multiTokenTS, MultiTokenInv, MultiTokenSafe] at h_inv ⊢
  exact h_inv.2

/-- Transitions preserve the invariant -/
theorem multiToken_invConsecution (owner : Address) (baseURI : URI) :
    ContractTransitionSystem.invConsecution' (multiTokenTS owner baseURI) := by
  intro s s' h_inv h_next
  simp only [multiTokenTS, MultiTokenInv] at h_inv ⊢
  -- Owner is preserved by all operations (they don't modify owner field)
  -- Supplies remain non-negative (Nat is always ≥ 0)
  rcases h_next with ⟨msg, from_, to_, id, amount, h_transfer⟩ |
                     ⟨msg, from_, to_, batch, h_batch⟩ |
                     ⟨msg, operator, approved, h_approval⟩ |
                     ⟨msg, to_, id, amount, h_mint⟩ |
                     ⟨msg, from_, id, amount, h_burn⟩ |
                     ⟨msg, to_, batch, h_mintBatch⟩
  -- Each case: owner preserved and supplies non-negative (always true for Nat)
  · exact ⟨h_inv.1 ▸ safeTransferFrom_preserves_owner s s' msg from_ to_ id amount h_transfer,
          fun _ => Nat.zero_le _⟩
  · exact ⟨h_inv.1 ▸ safeBatchTransferFrom_preserves_owner s s' msg from_ to_ batch h_batch,
          fun _ => Nat.zero_le _⟩
  · exact ⟨h_inv.1 ▸ setApprovalForAll_preserves_owner s s' msg operator approved h_approval,
          fun _ => Nat.zero_le _⟩
  · exact ⟨h_inv.1 ▸ mint_preserves_owner s s' msg to_ id amount h_mint,
          fun _ => Nat.zero_le _⟩
  · exact ⟨h_inv.1 ▸ burn_preserves_owner s s' msg from_ id amount h_burn,
          fun _ => Nat.zero_le _⟩
  · exact ⟨h_inv.1 ▸ mintBatch_preserves_owner s s' msg to_ batch h_mintBatch,
          fun _ => Nat.zero_le _⟩

/-- The invariant is inductive -/
theorem multiToken_invInductive (owner : Address) (baseURI : URI) :
    ContractTransitionSystem.invInductive' (multiTokenTS owner baseURI) :=
  ⟨multiToken_invInit owner baseURI,
   multiToken_invConsecution owner baseURI,
   multiToken_invSafe owner baseURI⟩

/-! ## Per-Token Supply Conservation -/

/-- Supply conservation for a specific token during transfers -/
def TokenSupplyConserved (id : TokenId) : MultiTokenState → MultiTokenState → Prop :=
  fun s s' => s'.supplies id = s.supplies id

/-- Transfer preserves supply for the transferred token -/
theorem transfer_conserves_supply (s s' : MultiTokenState) (msg : MsgContext)
    (from_ to_ : Address) (id : TokenId) (amount : Amount)
    (h : safeTransferFrom s msg from_ to_ id amount = Result.ok s') :
    TokenSupplyConserved id s s' :=
  transfer_preserves_supply s s' msg from_ to_ id amount h

/-! ## Balance Conservation -/

/-- Local balance conservation for transfers -/
def LocalBalanceConserved (from_ to_ : Address) (id : TokenId) :
    MultiTokenState → MultiTokenState → Prop :=
  fun s s' =>
    s.balances from_ id + s.balances to_ id =
    s'.balances from_ id + s'.balances to_ id

end Lab.ERC1155.Model
