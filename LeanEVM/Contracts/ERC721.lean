import LeanEVM.Core.Types
import LeanEVM.Core.Execution

/-!
# ERC-721 Non-Fungible Token Contract Model

This module models the ERC-721 NFT standard in Lean 4.
Each token has a unique ID and exactly one owner.
-/

namespace LeanEVM.Contracts

open LeanEVM

/-! ## Token ID -/

/-- Token ID (unique identifier for each NFT) -/
abbrev TokenId := Nat

/-! ## NFT State -/

/-- ERC-721 NFT State -/
structure NFTState where
  /-- Token owners: tokenId → owner (none if token doesn't exist) -/
  owners : TokenId → Option Address
  /-- Token approvals: tokenId → approved address (none if no approval) -/
  tokenApprovals : TokenId → Option Address
  /-- Operator approvals: owner → operator → approved -/
  operatorApprovals : Address → Address → Bool
  /-- Balance count: owner → number of tokens owned -/
  balances : Address → Nat

namespace NFTState

/-- Create empty NFT state -/
def empty : NFTState :=
  { owners := fun _ => none
  , tokenApprovals := fun _ => none
  , operatorApprovals := fun _ _ => false
  , balances := fun _ => 0 }

/-- Check if token exists -/
def exists_ (state : NFTState) (tokenId : TokenId) : Bool :=
  state.owners tokenId |>.isSome

/-- Get owner of a token -/
def ownerOf (state : NFTState) (tokenId : TokenId) : Option Address :=
  state.owners tokenId

/-- Get balance (number of tokens) of an address -/
def balanceOf (state : NFTState) (owner : Address) : Nat :=
  state.balances owner

/-- Get approved address for a token -/
def getApproved (state : NFTState) (tokenId : TokenId) : Option Address :=
  state.tokenApprovals tokenId

/-- Check if operator is approved for all tokens of owner -/
def isApprovedForAll (state : NFTState) (owner operator : Address) : Bool :=
  state.operatorApprovals owner operator

/-- Check if spender is approved or owner -/
def isApprovedOrOwner (state : NFTState) (spender : Address) (tokenId : TokenId) : Bool :=
  match state.ownerOf tokenId with
  | none => false
  | some owner =>
    spender == owner ||
    state.getApproved tokenId == some spender ||
    state.isApprovedForAll owner spender

/-- Set owner of a token (internal) -/
def setOwner (state : NFTState) (tokenId : TokenId) (owner : Option Address) : NFTState :=
  { state with owners := fun t => if t == tokenId then owner else state.owners t }

/-- Set token approval (internal) -/
def setTokenApproval (state : NFTState) (tokenId : TokenId) (approved : Option Address) : NFTState :=
  { state with tokenApprovals := fun t => if t == tokenId then approved else state.tokenApprovals t }

/-- Set operator approval (internal) -/
def setOperatorApproval (state : NFTState) (owner operator : Address) (approved : Bool) : NFTState :=
  { state with operatorApprovals := fun o op =>
      if o == owner && op == operator then approved
      else state.operatorApprovals o op }

/-- Update balance (internal) -/
def setBalance (state : NFTState) (addr : Address) (bal : Nat) : NFTState :=
  { state with balances := fun a => if a == addr then bal else state.balances a }

/-- Increment balance (internal) -/
def incBalance (state : NFTState) (addr : Address) : NFTState :=
  state.setBalance addr (state.balanceOf addr + 1)

/-- Decrement balance (internal) -/
def decBalance (state : NFTState) (addr : Address) : NFTState :=
  state.setBalance addr (state.balanceOf addr - 1)

end NFTState

/-! ## NFT Operations -/

/-- Mint a new token to an address -/
def mint (state : NFTState) (to_ : Address) (tokenId : TokenId) :
    ExecResult NFTState := do
  -- Check: cannot mint to zero address
  require (!to_.isZero) "ERC721: mint to zero address"
  -- Check: token must not already exist
  require (!state.exists_ tokenId) "ERC721: token already minted"
  -- Effect: set owner and increment balance
  let state' := state.setOwner tokenId (some to_)
  let state'' := state'.incBalance to_
  pure state''

/-- Burn a token -/
def burn (state : NFTState) (msg : MsgContext) (tokenId : TokenId) :
    ExecResult NFTState := do
  -- Check: token must exist
  require (state.exists_ tokenId) "ERC721: invalid token ID"
  -- Check: caller must be owner or approved
  require (state.isApprovedOrOwner msg.sender tokenId) "ERC721: caller is not owner nor approved"
  -- Get current owner
  match state.ownerOf tokenId with
  | none => ExecResult.revert "ERC721: invalid token ID"
  | some owner =>
    -- Effect: clear approval, remove owner, decrement balance
    let state' := state.setTokenApproval tokenId none
    let state'' := state'.setOwner tokenId none
    let state''' := state''.decBalance owner
    pure state'''

/-- Approve an address to transfer a specific token -/
def approve (state : NFTState) (msg : MsgContext) (to_ : Address) (tokenId : TokenId) :
    ExecResult NFTState := do
  -- Check: token must exist
  match state.ownerOf tokenId with
  | none => ExecResult.revert "ERC721: invalid token ID"
  | some owner =>
    -- Check: caller must be owner or approved operator
    require (msg.sender == owner || state.isApprovedForAll owner msg.sender)
      "ERC721: approve caller is not owner nor approved for all"
    -- Check: cannot approve to current owner
    require (to_ != owner) "ERC721: approval to current owner"
    -- Effect: set approval
    pure (state.setTokenApproval tokenId (some to_))

/-- Set approval for all tokens to an operator -/
def setApprovalForAll (state : NFTState) (msg : MsgContext) (operator : Address) (approved : Bool) :
    ExecResult NFTState := do
  -- Check: cannot approve self
  require (operator != msg.sender) "ERC721: approve to caller"
  -- Effect: set operator approval
  pure (state.setOperatorApproval msg.sender operator approved)

/-- Transfer token from one address to another -/
def transferFrom (state : NFTState) (msg : MsgContext)
    (from_ to_ : Address) (tokenId : TokenId) : ExecResult NFTState := do
  -- Check: cannot transfer to zero address
  require (!to_.isZero) "ERC721: transfer to zero address"
  -- Check: token must exist and from_ must be owner
  match state.ownerOf tokenId with
  | none => ExecResult.revert "ERC721: invalid token ID"
  | some owner =>
    require (owner == from_) "ERC721: transfer from incorrect owner"
    -- Check: caller must be owner or approved
    require (state.isApprovedOrOwner msg.sender tokenId)
      "ERC721: caller is not owner nor approved"
    -- Effect: clear approval
    let state' := state.setTokenApproval tokenId none
    -- Effect: update owner
    let state'' := state'.setOwner tokenId (some to_)
    -- Effect: update balances
    let state''' := state''.decBalance from_
    let state'''' := state'''.incBalance to_
    pure state''''

/-- Safe transfer (in real ERC721, this calls onERC721Received) -/
def safeTransferFrom (state : NFTState) (msg : MsgContext)
    (from_ to_ : Address) (tokenId : TokenId) : ExecResult NFTState := do
  -- For this model, safeTransferFrom is the same as transferFrom
  -- In a full model, we'd check if `to_` is a contract and call onERC721Received
  transferFrom state msg from_ to_ tokenId

/-! ## Verified Properties -/

section Properties

/-! ### Property 1: Mint to Zero Reverts -/

/-- Minting to zero address reverts -/
theorem mint_to_zero_reverts
    (state : NFTState) (to_ : Address) (tokenId : TokenId)
    (h_zero : to_.isZero = true) :
    ∃ m, mint state to_ tokenId = ExecResult.revert m := by
  refine ⟨"ERC721: mint to zero address", ?_⟩
  unfold mint require
  simp only [bind, pure, ExecResult.bind, h_zero, Bool.not_true]
  rfl

/-! ### Property 2: Cannot Mint Existing Token -/

/-- Minting an existing token reverts -/
theorem mint_existing_reverts
    (state : NFTState) (to_ : Address) (tokenId : TokenId)
    (h_not_zero : to_.isZero = false)
    (h_exists : state.exists_ tokenId = true) :
    ∃ m, mint state to_ tokenId = ExecResult.revert m := by
  refine ⟨"ERC721: token already minted", ?_⟩
  unfold mint require
  simp only [bind, pure, ExecResult.bind, h_not_zero, Bool.not_false, h_exists, Bool.not_true]
  rfl

/-! ### Property 3: Transfer to Zero Reverts -/

/-- Transfer to zero address reverts -/
theorem transferFrom_to_zero_reverts
    (state : NFTState) (msg : MsgContext) (from_ to_ : Address) (tokenId : TokenId)
    (h_zero : to_.isZero = true) :
    ∃ m, transferFrom state msg from_ to_ tokenId = ExecResult.revert m := by
  refine ⟨"ERC721: transfer to zero address", ?_⟩
  unfold transferFrom require
  simp only [bind, pure, ExecResult.bind, h_zero, Bool.not_true]
  rfl

/-! ### Property 4: Transfer Invalid Token Reverts -/

/-- Transfer of non-existent token reverts -/
theorem transferFrom_invalid_token_reverts
    (state : NFTState) (msg : MsgContext) (from_ to_ : Address) (tokenId : TokenId)
    (h_not_zero : to_.isZero = false)
    (h_not_exists : state.ownerOf tokenId = none) :
    ∃ m, transferFrom state msg from_ to_ tokenId = ExecResult.revert m := by
  refine ⟨"ERC721: invalid token ID", ?_⟩
  unfold transferFrom require
  simp only [bind, pure, ExecResult.bind, h_not_zero, Bool.not_false, h_not_exists]
  rfl

/-! ### Property 5: Successful Transfer Updates Owner -/

/-- After successful transfer, new owner is `to_` -/
theorem transferFrom_updates_owner
    (state state' : NFTState) (msg : MsgContext) (from_ to_ : Address) (tokenId : TokenId)
    (h_success : transferFrom state msg from_ to_ tokenId = ExecResult.success state') :
    state'.ownerOf tokenId = some to_ := by
  unfold transferFrom require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success
  · simp_all
  · rename_i owner h_owner
    split at h_success <;> try simp_all
    split at h_success <;> try simp_all
    cases h_success
    simp only [NFTState.ownerOf, NFTState.incBalance, NFTState.setBalance,
               NFTState.decBalance, NFTState.setOwner]
    simp only [beq_self_eq_true, ite_true]

/-! ### Property 6: Cannot Approve Self as Operator -/

/-- setApprovalForAll to self reverts -/
theorem setApprovalForAll_self_reverts
    (state : NFTState) (msg : MsgContext) (approved : Bool) :
    ∃ m, setApprovalForAll state msg msg.sender approved = ExecResult.revert m := by
  refine ⟨"ERC721: approve to caller", ?_⟩
  unfold setApprovalForAll require
  simp only [bind, pure, ExecResult.bind, ne_eq, bne_self_eq_false]
  rfl

/-! ### Property 7: Mint Increases Balance -/

/-- Successful mint increases recipient balance by 1 -/
theorem mint_increases_balance
    (state state' : NFTState) (to_ : Address) (tokenId : TokenId)
    (h_success : mint state to_ tokenId = ExecResult.success state') :
    state'.balanceOf to_ = state.balanceOf to_ + 1 := by
  unfold mint require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  cases h_success
  simp only [NFTState.balanceOf, NFTState.incBalance, NFTState.setBalance,
             NFTState.setOwner, beq_self_eq_true, ite_true]

end Properties

/-! ## Invariants -/

/-- Each token has at most one owner -/
def uniqueOwnership (state : NFTState) : Prop :=
  ∀ tokenId, match state.ownerOf tokenId with
    | none => True
    | some _ => True  -- Ownership is unique by construction (function type)

/-- Balance equals count of owned tokens (for a finite set) -/
def balanceConsistent (state : NFTState) (owner : Address) (tokens : List TokenId) : Prop :=
  state.balanceOf owner = (tokens.filter fun t => state.ownerOf t == some owner).length

end LeanEVM.Contracts
