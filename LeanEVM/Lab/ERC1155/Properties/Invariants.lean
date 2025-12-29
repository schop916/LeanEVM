import Lab.ERC1155.Contracts.MultiToken

open Lab.ERC20 (Result MsgContext)

/-!
# ERC-1155 Invariants

Key invariants for multi-token contract correctness:

1. **Per-Token Supply Conservation**: For each token ID, sum of balances equals supply
2. **Batch Atomicity**: Batch operations are all-or-nothing
3. **Approval Independence**: Balances and approvals are independent
-/

namespace Lab.ERC1155

open Lab.ERC20 (Address Amount)

/-! ## Supply Invariants -/

/-- Supply invariant for a specific token ID -/
def TokenSupplyInvariant (s : MultiTokenState) (id : TokenId) (addresses : List Address) : Prop :=
  (addresses.map (fun addr => s.balances addr id)).sum = s.supplies id

/-- Supply invariant holds for all token IDs -/
def AllSupplyInvariant (s : MultiTokenState) (ids : List TokenId) (addresses : List Address) : Prop :=
  ∀ id ∈ ids, TokenSupplyInvariant s id addresses

/-! ## Transfer Conservation -/

/-- Local balance conservation for a single token transfer -/
def LocalTokenConservation (s s' : MultiTokenState) (from_ to_ : Address) (id : TokenId) : Prop :=
  s.balances from_ id + s.balances to_ id = s'.balances from_ id + s'.balances to_ id

/-- Batch transfer preserves total balance for each token ID -/
def BatchConservation (s s' : MultiTokenState) (from_ to_ : Address) (ids : List TokenId) : Prop :=
  ∀ id ∈ ids, LocalTokenConservation s s' from_ to_ id

/-! ## Approval Invariants -/

/-- Approvals are reflexive: you're always approved for yourself -/
def SelfApproved (s : MultiTokenState) : Prop :=
  ∀ addr, isApprovedOrOwner s addr addr = true

/-- Approval state is independent of balances -/
def ApprovalBalanceIndependence (s : MultiTokenState) : Prop :=
  ∀ (owner operator : Address) (id : TokenId) (amount : Amount),
    let s' := { s with balances := fun a i =>
      if a = owner ∧ i = id then amount else s.balances a i }
    s'.operatorApprovals = s.operatorApprovals

/-! ## Multi-Token Specific Invariants -/

/-- Different token IDs have independent balances -/
def TokenIndependence (s s' : MultiTokenState) (modifiedId : TokenId) (addresses : List Address) : Prop :=
  ∀ id, id ≠ modifiedId → ∀ addr ∈ addresses, s.balances addr id = s'.balances addr id

/-- Mint doesn't affect other tokens -/
def MintIsolation (s s' : MultiTokenState) (mintedId : TokenId) : Prop :=
  ∀ id, id ≠ mintedId → s'.supplies id = s.supplies id

/-! ## Safety Properties -/

/-- No token can be transferred without approval -/
def TransferRequiresApproval (s : MultiTokenState) (from_ : Address) (msg : MsgContext) : Prop :=
  msg.sender ≠ from_ → s.operatorApprovals from_ msg.sender = false →
  ∀ to_ id amount, ∃ m, safeTransferFrom s msg from_ to_ id amount = Result.revert m

/-- Minting requires ownership -/
def MintRequiresOwnership (s : MultiTokenState) : Prop :=
  ∀ msg to_ id amount,
    msg.sender ≠ s.owner →
    ∃ m, mint s msg to_ id amount = Result.revert m

/-! ## Compound Invariant -/

/-- Main multi-token invariant -/
structure MultiTokenInvariant (s : MultiTokenState) (knownTokens : List TokenId) (knownAddresses : List Address) : Prop where
  /-- Supply accounting is correct for all known tokens -/
  supplyCorrect : AllSupplyInvariant s knownTokens knownAddresses
  /-- Self-approval holds -/
  selfApproved : SelfApproved s

end Lab.ERC1155
