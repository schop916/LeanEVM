import Lab.ERC20.Contracts.Interface

/-!
# ERC-1155 Multi-Token Interface

ERC-1155 is a standard for managing multiple token types in a single contract:
- Fungible tokens (like ERC-20)
- Non-fungible tokens (like ERC-721)
- Semi-fungible tokens (limited supply fungibles)

## Key Differences from ERC-20

1. **Token IDs**: Each token type has a unique ID
2. **Batch Operations**: Transfer multiple token types atomically
3. **Operator Approvals**: Approve addresses for all tokens (not per-token allowances)

## References

- EIP-1155: https://eips.ethereum.org/EIPS/eip-1155
-/

namespace Lab.ERC1155

open Lab.ERC20 (Address Amount Result MsgContext)

/-! ## ERC-1155 Specific Types -/

/-- Token ID identifying a specific token type -/
abbrev TokenId := Nat

/-- URI for token metadata -/
abbrev URI := String

/-! ## State Abstraction -/

/-- Abstract state for an ERC-1155 contract -/
class ERC1155State (S : Type) where
  /-- Balance of a specific token for an address -/
  balanceOf : S → Address → TokenId → Amount
  /-- Check if an operator is approved for all tokens of an owner -/
  isApprovedForAll : S → Address → Address → Bool
  /-- Get URI for a token type -/
  uri : S → TokenId → URI
  /-- Set balance for a specific token -/
  setBalance : S → Address → TokenId → Amount → S
  /-- Set operator approval -/
  setApprovalForAll : S → Address → Address → Bool → S

/-! ## Batch Types -/

/-- A batch transfer: list of (tokenId, amount) pairs -/
structure TransferBatch where
  ids : List TokenId
  amounts : List Amount
  deriving Repr

/-- Validate batch has matching lengths -/
def TransferBatch.isValid (batch : TransferBatch) : Bool :=
  batch.ids.length = batch.amounts.length

/-- Zip batch into (id, amount) pairs -/
def TransferBatch.toPairs (batch : TransferBatch) : List (TokenId × Amount) :=
  batch.ids.zip batch.amounts

/-! ## Operations -/

/-- ERC-1155 operations -/
class ERC1155Ops (S : Type) [ERC1155State S] where
  /-- Transfer a single token type -/
  safeTransferFrom : S → MsgContext → Address → Address → TokenId → Amount → Result S
  /-- Transfer multiple token types atomically -/
  safeBatchTransferFrom : S → MsgContext → Address → Address → TransferBatch → Result S
  /-- Set or revoke operator approval for all tokens -/
  setApprovalForAll : S → MsgContext → Address → Bool → Result S
  /-- Mint tokens (if minting is supported) -/
  mint : S → MsgContext → Address → TokenId → Amount → Result S
  /-- Burn tokens -/
  burn : S → MsgContext → Address → TokenId → Amount → Result S

/-! ## Helper Functions -/

/-- Check if caller is owner or approved operator -/
def isApprovedOrOwner {S : Type} [ERC1155State S] (state : S) (operator owner : Address) : Bool :=
  operator = owner ∨ ERC1155State.isApprovedForAll state owner operator

/-- Sum balances across multiple token IDs -/
def totalBalanceOf {S : Type} [ERC1155State S] (state : S) (addr : Address) (ids : List TokenId) : Amount :=
  (ids.map (ERC1155State.balanceOf state addr)).sum

/-! ## Balance Batch Query -/

/-- Get balances for multiple address/token pairs -/
def balanceOfBatch {S : Type} [ERC1155State S] (state : S) (accounts : List Address) (ids : List TokenId) : List Amount :=
  (accounts.zip ids).map fun (addr, id) => ERC1155State.balanceOf state addr id

end Lab.ERC1155
