import Lab.ERC1155.Contracts.Interface

/-!
# ERC-1155 Multi-Token Implementation

A basic implementation of the ERC-1155 multi-token standard.

## Features

- Multiple token types managed in a single contract
- Batch transfers for gas efficiency
- Operator approval for all tokens
- Minting and burning with access control

## Invariants

1. **Balance Conservation**: For each token ID, sum of balances is constant
   (unless minting/burning occurs)
2. **Atomic Batches**: Batch operations succeed entirely or fail entirely
3. **Approval Independence**: Token balances don't affect approvals
-/

namespace Lab.ERC1155

open Lab.ERC20 (Address Amount Result MsgContext require)

/-! ## State Definition -/

/-- ERC-1155 multi-token state -/
structure MultiTokenState where
  /-- Balances: address → tokenId → amount -/
  balances : Address → TokenId → Amount
  /-- Operator approvals: owner → operator → approved -/
  operatorApprovals : Address → Address → Bool
  /-- Token URI template -/
  baseURI : URI
  /-- Contract owner (for minting) -/
  owner : Address
  /-- Total supply per token ID -/
  supplies : TokenId → Amount

/-! ## Initialization -/

/-- Create a new multi-token contract -/
def MultiTokenState.init (owner : Address) (baseURI : URI) : MultiTokenState :=
  { balances := fun _ _ => 0
  , operatorApprovals := fun _ _ => false
  , baseURI := baseURI
  , owner := owner
  , supplies := fun _ => 0 }

/-! ## ERC1155State Instance -/

instance : ERC1155State MultiTokenState where
  balanceOf s addr id := s.balances addr id
  isApprovedForAll s owner operator := s.operatorApprovals owner operator
  uri s _ := s.baseURI  -- Simplified: same base URI for all tokens
  setBalance s addr id amount :=
    { s with balances := fun a i => if a = addr ∧ i = id then amount else s.balances a i }
  setApprovalForAll s owner operator approved :=
    { s with operatorApprovals := fun o op => if o = owner ∧ op = operator then approved else s.operatorApprovals o op }

/-! ## Internal Helpers -/

/-- Update balance for a single transfer -/
def updateBalance (s : MultiTokenState) (from_ to_ : Address) (id : TokenId) (amount : Amount) : MultiTokenState :=
  let fromBal := s.balances from_ id
  let toBal := s.balances to_ id
  { s with balances := fun a i =>
      if a = from_ ∧ i = id then fromBal - amount
      else if a = to_ ∧ i = id then toBal + amount
      else s.balances a i }

/-- Apply a batch of balance updates -/
def applyBatchTransfer (s : MultiTokenState) (from_ to_ : Address) (pairs : List (TokenId × Amount)) : MultiTokenState :=
  pairs.foldl (fun state (id, amount) => updateBalance state from_ to_ id amount) s

/-! ## Core Operations -/

/-- Transfer a single token type -/
def safeTransferFrom (s : MultiTokenState) (msg : MsgContext) (from_ to_ : Address) (id : TokenId) (amount : Amount) :
    Result MultiTokenState := do
  require (!to_.isZero) "ERC1155: transfer to zero address"
  require (isApprovedOrOwner s msg.sender from_) "ERC1155: caller is not owner nor approved"
  require (s.balances from_ id ≥ amount) "ERC1155: insufficient balance"
  pure (updateBalance s from_ to_ id amount)

/-- Check if all balances are sufficient for a batch transfer -/
def checkBatchBalances (s : MultiTokenState) (from_ : Address) (pairs : List (TokenId × Amount)) : Bool :=
  pairs.all fun (id, amount) => s.balances from_ id ≥ amount

/-- Transfer multiple token types atomically -/
def safeBatchTransferFrom (s : MultiTokenState) (msg : MsgContext) (from_ to_ : Address) (batch : TransferBatch) :
    Result MultiTokenState := do
  require (!to_.isZero) "ERC1155: transfer to zero address"
  require (batch.isValid) "ERC1155: ids and amounts length mismatch"
  require (isApprovedOrOwner s msg.sender from_) "ERC1155: caller is not owner nor approved"
  let pairs := batch.toPairs
  require (checkBatchBalances s from_ pairs) "ERC1155: insufficient balance for batch"
  pure (applyBatchTransfer s from_ to_ pairs)

/-- Set operator approval for all tokens -/
def setApprovalForAll (s : MultiTokenState) (msg : MsgContext) (operator : Address) (approved : Bool) :
    Result MultiTokenState := do
  require (operator ≠ msg.sender) "ERC1155: setting approval for self"
  pure { s with operatorApprovals := fun o op =>
    if o = msg.sender ∧ op = operator then approved else s.operatorApprovals o op }

/-- Mint new tokens (owner only) -/
def mint (s : MultiTokenState) (msg : MsgContext) (to_ : Address) (id : TokenId) (amount : Amount) :
    Result MultiTokenState := do
  require (msg.sender = s.owner) "ERC1155: caller is not owner"
  require (!to_.isZero) "ERC1155: mint to zero address"
  let currentBal := s.balances to_ id
  let currentSupply := s.supplies id
  pure { s with
    balances := fun a i => if a = to_ ∧ i = id then currentBal + amount else s.balances a i
    supplies := fun i => if i = id then currentSupply + amount else s.supplies i }

/-- Burn tokens -/
def burn (s : MultiTokenState) (msg : MsgContext) (from_ : Address) (id : TokenId) (amount : Amount) :
    Result MultiTokenState := do
  require (isApprovedOrOwner s msg.sender from_) "ERC1155: caller is not owner nor approved"
  require (s.balances from_ id ≥ amount) "ERC1155: burn amount exceeds balance"
  let currentBal := s.balances from_ id
  let currentSupply := s.supplies id
  pure { s with
    balances := fun a i => if a = from_ ∧ i = id then currentBal - amount else s.balances a i
    supplies := fun i => if i = id then currentSupply - amount else s.supplies i }

/-- Batch mint -/
def mintBatch (s : MultiTokenState) (msg : MsgContext) (to_ : Address) (batch : TransferBatch) :
    Result MultiTokenState := do
  require (msg.sender = s.owner) "ERC1155: caller is not owner"
  require (!to_.isZero) "ERC1155: mint to zero address"
  require (batch.isValid) "ERC1155: ids and amounts length mismatch"
  let pairs := batch.toPairs
  pure (pairs.foldl (fun state (id, amount) =>
    let currentBal := state.balances to_ id
    let currentSupply := state.supplies id
    { state with
      balances := fun a i => if a = to_ ∧ i = id then currentBal + amount else state.balances a i
      supplies := fun i => if i = id then currentSupply + amount else state.supplies i }) s)

/-! ## ERC1155Ops Instance -/

instance : ERC1155Ops MultiTokenState where
  safeTransferFrom := safeTransferFrom
  safeBatchTransferFrom := safeBatchTransferFrom
  setApprovalForAll := setApprovalForAll
  mint := mint
  burn := burn

/-! ## Basic Properties -/

/-- Single transfer preserves total supply -/
theorem transfer_preserves_supply (s s' : MultiTokenState) (msg : MsgContext)
    (from_ to_ : Address) (id : TokenId) (amount : Amount)
    (h : safeTransferFrom s msg from_ to_ id amount = Result.ok s') :
    s'.supplies id = s.supplies id := by
  unfold safeTransferFrom require isApprovedOrOwner at h
  simp only [Bind.bind, Pure.pure, Result.bind, Bool.or_eq_true, decide_eq_true_eq] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  simp only [updateBalance]

/-- Transfer to zero address reverts -/
theorem transfer_to_zero_reverts (s : MultiTokenState) (msg : MsgContext)
    (from_ : Address) (id : TokenId) (amount : Amount) :
    ∃ m, safeTransferFrom s msg from_ Address.zero id amount = Result.revert m := by
  refine ⟨"ERC1155: transfer to zero address", ?_⟩
  unfold safeTransferFrom require Address.isZero Address.zero
  simp [Bind.bind, Result.bind]

/-- Helper: not approved or owner implies isApprovedOrOwner is false -/
theorem not_approved_or_owner_false {s : MultiTokenState} {operator owner : Address}
    (h_not_owner : operator ≠ owner)
    (h_not_approved : s.operatorApprovals owner operator = false) :
    isApprovedOrOwner s operator owner = false := by
  unfold isApprovedOrOwner
  simp only [ERC1155State.isApprovedForAll]
  simp only [decide_eq_false_iff_not, not_or]
  exact ⟨h_not_owner, Bool.eq_false_iff.mp h_not_approved⟩

/-- Unauthorized transfer reverts -/
theorem transfer_unauthorized_reverts (s : MultiTokenState) (msg : MsgContext)
    (from_ to_ : Address) (id : TokenId) (amount : Amount)
    (h_not_owner : msg.sender ≠ from_)
    (h_not_approved : s.operatorApprovals from_ msg.sender = false)
    (h_to_nonzero : to_.isZero = false) :
    ∃ m, safeTransferFrom s msg from_ to_ id amount = Result.revert m := by
  have h_not_approved_or_owner := not_approved_or_owner_false h_not_owner h_not_approved
  refine ⟨"ERC1155: caller is not owner nor approved", ?_⟩
  unfold safeTransferFrom require
  simp_all [Bind.bind, Result.bind]

/-- Mint increases supply -/
theorem mint_increases_supply (s s' : MultiTokenState) (msg : MsgContext)
    (to_ : Address) (id : TokenId) (amount : Amount)
    (h : mint s msg to_ id amount = Result.ok s') :
    s'.supplies id = s.supplies id + amount := by
  unfold mint require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  simp only [ite_true]

/-- Burn decreases supply -/
theorem burn_decreases_supply (s s' : MultiTokenState) (msg : MsgContext)
    (from_ : Address) (id : TokenId) (amount : Amount)
    (h : burn s msg from_ id amount = Result.ok s') :
    s'.supplies id = s.supplies id - amount := by
  unfold burn require isApprovedOrOwner at h
  simp only [Bind.bind, Pure.pure, Result.bind, Bool.or_eq_true, decide_eq_true_eq] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  simp only [ite_true]

/-- Setting approval doesn't change balances -/
theorem approval_preserves_balances (s s' : MultiTokenState) (msg : MsgContext)
    (operator : Address) (approved : Bool)
    (h : setApprovalForAll s msg operator approved = Result.ok s') :
    ∀ addr id, s'.balances addr id = s.balances addr id := by
  unfold setApprovalForAll require at h
  simp only [Bind.bind, Pure.pure, Result.bind, ne_eq] at h
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  intro addr id
  rfl

/-! ## Owner Preservation Lemmas -/

/-- updateBalance preserves owner -/
theorem updateBalance_preserves_owner (s : MultiTokenState) (from_ to_ : Address)
    (id : TokenId) (amount : Amount) :
    (updateBalance s from_ to_ id amount).owner = s.owner := by
  unfold updateBalance
  rfl

/-- applyBatchTransfer preserves owner -/
theorem applyBatchTransfer_preserves_owner (s : MultiTokenState) (from_ to_ : Address)
    (pairs : List (TokenId × Amount)) :
    (applyBatchTransfer s from_ to_ pairs).owner = s.owner := by
  unfold applyBatchTransfer
  induction pairs generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact updateBalance_preserves_owner _ _ _ _ _

/-- safeTransferFrom preserves owner -/
theorem safeTransferFrom_preserves_owner (s s' : MultiTokenState) (msg : MsgContext)
    (from_ to_ : Address) (id : TokenId) (amount : Amount)
    (h : safeTransferFrom s msg from_ to_ id amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold safeTransferFrom require isApprovedOrOwner at h
  simp only [Bind.bind, Pure.pure, Result.bind, Bool.or_eq_true, decide_eq_true_eq] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  exact updateBalance_preserves_owner _ _ _ _ _

/-- safeBatchTransferFrom preserves owner -/
theorem safeBatchTransferFrom_preserves_owner (s s' : MultiTokenState) (msg : MsgContext)
    (from_ to_ : Address) (batch : TransferBatch)
    (h : safeBatchTransferFrom s msg from_ to_ batch = Result.ok s') :
    s'.owner = s.owner := by
  unfold safeBatchTransferFrom require isApprovedOrOwner at h
  simp only [Bind.bind, Pure.pure, Result.bind, Bool.or_eq_true, decide_eq_true_eq] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  exact applyBatchTransfer_preserves_owner _ _ _ _

/-- setApprovalForAll preserves owner -/
theorem setApprovalForAll_preserves_owner (s s' : MultiTokenState) (msg : MsgContext)
    (operator : Address) (approved : Bool)
    (h : setApprovalForAll s msg operator approved = Result.ok s') :
    s'.owner = s.owner := by
  unfold setApprovalForAll require at h
  simp only [Bind.bind, Pure.pure, Result.bind, ne_eq] at h
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  rfl

/-- mint preserves owner -/
theorem mint_preserves_owner (s s' : MultiTokenState) (msg : MsgContext)
    (to_ : Address) (id : TokenId) (amount : Amount)
    (h : mint s msg to_ id amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold mint require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  rfl

/-- burn preserves owner -/
theorem burn_preserves_owner (s s' : MultiTokenState) (msg : MsgContext)
    (from_ : Address) (id : TokenId) (amount : Amount)
    (h : burn s msg from_ id amount = Result.ok s') :
    s'.owner = s.owner := by
  unfold burn require isApprovedOrOwner at h
  simp only [Bind.bind, Pure.pure, Result.bind, Bool.or_eq_true, decide_eq_true_eq] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  rfl

/-- Helper: single mintBatch step preserves owner -/
private theorem mintBatch_step_preserves_owner (s : MultiTokenState) (to_ : Address)
    (id : TokenId) (amount : Amount) :
    { s with
      balances := fun a i => if a = to_ ∧ i = id then s.balances to_ id + amount else s.balances a i
      supplies := fun i => if i = id then s.supplies id + amount else s.supplies i }.owner = s.owner := rfl

/-- Helper: mintBatch foldl preserves owner -/
private theorem mintBatch_foldl_preserves_owner (s : MultiTokenState) (to_ : Address)
    (pairs : List (TokenId × Amount)) :
    (pairs.foldl (fun state (p : TokenId × Amount) =>
      { state with
        balances := fun a i => if a = to_ ∧ i = p.1 then state.balances to_ p.1 + p.2 else state.balances a i
        supplies := fun i => if i = p.1 then state.supplies p.1 + p.2 else state.supplies i }) s).owner = s.owner := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    let s' := { s with
      balances := fun a i => if a = to_ ∧ i = p.1 then s.balances to_ p.1 + p.2 else s.balances a i
      supplies := fun i => if i = p.1 then s.supplies p.1 + p.2 else s.supplies i }
    have h_step : s'.owner = s.owner := rfl
    calc (ps.foldl _ s').owner = s'.owner := ih s'
      _ = s.owner := h_step

/-- mintBatch preserves owner -/
theorem mintBatch_preserves_owner (s s' : MultiTokenState) (msg : MsgContext)
    (to_ : Address) (batch : TransferBatch)
    (h : mintBatch s msg to_ batch = Result.ok s') :
    s'.owner = s.owner := by
  unfold mintBatch require at h
  simp only [Bind.bind, Pure.pure, Result.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Result.ok.injEq] at h
  cases h
  exact mintBatch_foldl_preserves_owner s to_ batch.toPairs

end Lab.ERC1155
