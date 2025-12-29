import Lab.ERC20.Contracts.Interface

/-!
# Basic ERC-20 Token

A simple ERC-20 token implementation for verification practice.

## Features

- Fixed total supply (set at deployment)
- Standard transfer, approve, transferFrom
- No minting or burning after deployment

## Verification Goals

1. Total supply is constant
2. Transfer conserves balances
3. Zero address checks
4. Allowance correctly updated
-/

namespace Lab.ERC20

/-! ## Token State -/

/-- Basic ERC-20 token state -/
structure BasicTokenState where
  /-- Token balances -/
  balances : Address → Amount
  /-- Allowances: owner → spender → amount -/
  allowances : Address → Address → Amount
  /-- Total supply (constant after init) -/
  supply : Amount

namespace BasicTokenState

/-- Create initial state with all tokens to deployer -/
def init (deployer : Address) (totalSupply : Amount) : BasicTokenState :=
  { balances := fun addr => if addr = deployer then totalSupply else 0
  , allowances := fun _ _ => 0
  , supply := totalSupply }

end BasicTokenState

/-! ## ERC20State Instance -/

instance : ERC20State BasicTokenState where
  totalSupply := fun s => s.supply
  balanceOf := fun s addr => s.balances addr
  allowance := fun s owner spender => s.allowances owner spender
  setBalance := fun s addr bal =>
    { s with balances := fun a => if a = addr then bal else s.balances a }
  setAllowance := fun s owner spender amt =>
    { s with allowances := fun o sp =>
        if o = owner ∧ sp = spender then amt else s.allowances o sp }

/-! ## Token Operations -/

namespace BasicToken

open ERC20State

/-- Transfer tokens from sender to recipient -/
def transfer (state : BasicTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount) :
    Result BasicTokenState := do
  -- Check: cannot transfer to zero address
  require (!recipient.isZero) "ERC20: transfer to zero address"
  -- Check: sender has sufficient balance
  let senderBal := balanceOf state msg.sender
  require (senderBal ≥ amount) "ERC20: insufficient balance"
  -- Effect: update balances
  let state' := setBalance state msg.sender (senderBal - amount)
  let receiverBal := balanceOf state' recipient
  let state'' := setBalance state' recipient (receiverBal + amount)
  pure state''

/-- Approve spender to spend tokens -/
def approve (state : BasicTokenState) (msg : MsgContext) (spender : Address) (amount : Amount) :
    Result BasicTokenState := do
  -- Check: cannot approve zero address
  require (!spender.isZero) "ERC20: approve to zero address"
  -- Effect: set allowance
  pure (setAllowance state msg.sender spender amount)

/-- Transfer tokens using allowance -/
def transferFrom (state : BasicTokenState) (msg : MsgContext)
    (fromAddr recipient : Address) (amount : Amount) : Result BasicTokenState := do
  -- Check: cannot transfer to zero address
  require (!recipient.isZero) "ERC20: transfer to zero address"
  -- Check: sufficient allowance
  let currentAllowance := allowance state fromAddr msg.sender
  require (currentAllowance ≥ amount) "ERC20: insufficient allowance"
  -- Check: sufficient balance
  let fromBal := balanceOf state fromAddr
  require (fromBal ≥ amount) "ERC20: insufficient balance"
  -- Effect: decrease allowance
  let state' := setAllowance state fromAddr msg.sender (currentAllowance - amount)
  -- Effect: update balances
  let state'' := setBalance state' fromAddr (fromBal - amount)
  let toBal := balanceOf state'' recipient
  let state''' := setBalance state'' recipient (toBal + amount)
  pure state'''

end BasicToken

/-! ## ERC20Ops Instance -/

instance : ERC20Ops BasicTokenState where
  transfer := BasicToken.transfer
  approve := BasicToken.approve
  transferFrom := BasicToken.transferFrom

/-! ## Verified Properties -/

section Proofs

open BasicToken ERC20State

/-! ### Property 1: Transfer Preserves Total Supply -/

/-- Transfer doesn't change the supply field -/
theorem transfer_preserves_supply
    (state state' : BasicTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : transfer state msg recipient amount = Result.ok state') :
    state'.supply = state.supply := by
  unfold transfer require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  cases h_success
  rfl

/-! ### Property 2: Transfer to Zero Reverts -/

/-- Cannot transfer to zero address -/
theorem transfer_to_zero_reverts
    (state : BasicTokenState) (msg : MsgContext) (amount : Amount) :
    ∃ m, transfer state msg Address.zero amount = Result.revert m := by
  refine ⟨"ERC20: transfer to zero address", ?_⟩
  unfold transfer require Address.isZero Address.zero
  simp [Bind.bind, Result.bind]

/-! ### Property 3: Insufficient Balance Reverts -/

/-- Transfer reverts if sender has insufficient balance -/
theorem transfer_insufficient_reverts
    (state : BasicTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_to_nonzero : recipient.isZero = false)
    (h_insufficient : balanceOf state msg.sender < amount) :
    ∃ m, transfer state msg recipient amount = Result.revert m := by
  refine ⟨"ERC20: insufficient balance", ?_⟩
  unfold transfer require
  simp only [Bind.bind, Pure.pure, Result.bind, h_to_nonzero, Bool.not_false, ite_true]
  have h : ¬(balanceOf state msg.sender ≥ amount) := Nat.not_le.mpr h_insufficient
  simp only [ge_iff_le, decide_eq_true_eq, h, ite_false]

/-! ### Property 4: Approve Sets Allowance -/

/-- Approve sets the exact allowance -/
theorem approve_sets_allowance
    (state state' : BasicTokenState) (msg : MsgContext) (spender : Address) (amount : Amount)
    (h_success : approve state msg spender amount = Result.ok state') :
    allowance state' msg.sender spender = amount := by
  unfold approve require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [allowance, setAllowance, and_self, ite_true]

/-! ### Property 5: TransferFrom Decreases Allowance -/

/-- TransferFrom decreases allowance by amount -/
theorem transferFrom_decreases_allowance
    (state state' : BasicTokenState) (msg : MsgContext)
    (fromAddr recipient : Address) (amount : Amount)
    (h_success : transferFrom state msg fromAddr recipient amount = Result.ok state') :
    allowance state' fromAddr msg.sender = allowance state fromAddr msg.sender - amount := by
  unfold transferFrom require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [allowance, setBalance, setAllowance, and_self, ite_true]

end Proofs

end Lab.ERC20
