import Lab.ERC20.Contracts.Interface

/-!
# Mintable ERC-20 Token

An ERC-20 token with minting and burning capabilities.

## Features

- Owner-controlled minting
- Anyone can burn their own tokens
- Access control for privileged operations

## Verification Goals

1. Only owner can mint
2. Minting increases supply correctly
3. Burning decreases supply correctly
4. Sum of balances equals total supply
-/

namespace Lab.ERC20

/-! ## Mintable Token State -/

/-- Mintable ERC-20 token state -/
structure MintableTokenState where
  /-- Token balances -/
  balances : Address → Amount
  /-- Allowances: owner → spender → amount -/
  allowances : Address → Address → Amount
  /-- Total supply (can change via mint/burn) -/
  supply : Amount
  /-- Contract owner (can mint) -/
  owner : Address

namespace MintableTokenState

/-- Create initial state -/
def init (owner : Address) (initialSupply : Amount) : MintableTokenState :=
  { balances := fun addr => if addr = owner then initialSupply else 0
  , allowances := fun _ _ => 0
  , supply := initialSupply
  , owner := owner }

end MintableTokenState

/-! ## ERC20State Instance -/

instance : ERC20State MintableTokenState where
  totalSupply := fun s => s.supply
  balanceOf := fun s addr => s.balances addr
  allowance := fun s owner spender => s.allowances owner spender
  setBalance := fun s addr bal =>
    { s with balances := fun a => if a = addr then bal else s.balances a }
  setAllowance := fun s owner spender amt =>
    { s with allowances := fun o sp =>
        if o = owner ∧ sp = spender then amt else s.allowances o sp }

/-! ## Extended Operations -/

namespace MintableToken

open ERC20State

/-- Transfer tokens -/
def transfer (state : MintableTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount) :
    Result MintableTokenState := do
  require (!recipient.isZero) "ERC20: transfer to zero address"
  let senderBal := balanceOf state msg.sender
  require (senderBal ≥ amount) "ERC20: insufficient balance"
  let state' := setBalance state msg.sender (senderBal - amount)
  let receiverBal := balanceOf state' recipient
  let state'' := setBalance state' recipient (receiverBal + amount)
  pure state''

/-- Approve spender -/
def approve (state : MintableTokenState) (msg : MsgContext) (spender : Address) (amount : Amount) :
    Result MintableTokenState := do
  require (!spender.isZero) "ERC20: approve to zero address"
  pure (setAllowance state msg.sender spender amount)

/-- Transfer from with allowance -/
def transferFrom (state : MintableTokenState) (msg : MsgContext)
    (fromAddr recipient : Address) (amount : Amount) : Result MintableTokenState := do
  require (!recipient.isZero) "ERC20: transfer to zero address"
  let currentAllowance := allowance state fromAddr msg.sender
  require (currentAllowance ≥ amount) "ERC20: insufficient allowance"
  let fromBal := balanceOf state fromAddr
  require (fromBal ≥ amount) "ERC20: insufficient balance"
  let state' := setAllowance state fromAddr msg.sender (currentAllowance - amount)
  let state'' := setBalance state' fromAddr (fromBal - amount)
  let toBal := balanceOf state'' recipient
  let state''' := setBalance state'' recipient (toBal + amount)
  pure state'''

/-- Mint new tokens (owner only) -/
def mint (state : MintableTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount) :
    Result MintableTokenState := do
  -- Access control: only owner
  require (msg.sender = state.owner) "Ownable: caller is not the owner"
  -- Check: cannot mint to zero address
  require (!recipient.isZero) "ERC20: mint to zero address"
  -- Effect: increase balance and supply
  let currentBal := balanceOf state recipient
  let state' := setBalance state recipient (currentBal + amount)
  pure { state' with supply := state'.supply + amount }

/-- Burn tokens (caller burns their own) -/
def burn (state : MintableTokenState) (msg : MsgContext) (amount : Amount) :
    Result MintableTokenState := do
  -- Check: sufficient balance
  let senderBal := balanceOf state msg.sender
  require (senderBal ≥ amount) "ERC20: burn amount exceeds balance"
  -- Effect: decrease balance and supply
  let state' := setBalance state msg.sender (senderBal - amount)
  pure { state' with supply := state'.supply - amount }

end MintableToken

/-! ## ERC20Ops Instance -/

instance : ERC20Ops MintableTokenState where
  transfer := MintableToken.transfer
  approve := MintableToken.approve
  transferFrom := MintableToken.transferFrom

/-! ## Verified Properties -/

section Proofs

open MintableToken ERC20State

/-! ### Property 1: Only Owner Can Mint -/

/-- Non-owner cannot mint -/
theorem mint_requires_owner
    (state : MintableTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_not_owner : msg.sender ≠ state.owner) :
    ∃ m, mint state msg recipient amount = Result.revert m := by
  refine ⟨"Ownable: caller is not the owner", ?_⟩
  unfold mint require
  simp only [Bind.bind, Pure.pure, Result.bind]
  have h : ¬(msg.sender = state.owner) := h_not_owner
  simp only [decide_eq_true_eq, h, not_true_eq_false, ite_false]

/-! ### Property 2: Mint Increases Supply -/

/-- Successful mint increases supply by amount -/
theorem mint_increases_supply
    (state state' : MintableTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : mint state msg recipient amount = Result.ok state') :
    state'.supply = state.supply + amount := by
  unfold mint require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  cases h_success
  rfl

/-! ### Property 3: Mint Increases Recipient Balance -/

/-- Successful mint increases recipient balance -/
theorem mint_increases_balance
    (state state' : MintableTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : mint state msg recipient amount = Result.ok state') :
    balanceOf state' recipient = balanceOf state recipient + amount := by
  unfold mint require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [balanceOf, setBalance, ite_true]

/-! ### Property 4: Burn Decreases Supply -/

/-- Successful burn decreases supply by amount -/
theorem burn_decreases_supply
    (state state' : MintableTokenState) (msg : MsgContext) (amount : Amount)
    (h_success : burn state msg amount = Result.ok state') :
    state'.supply = state.supply - amount := by
  unfold burn require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  cases h_success
  rfl

/-! ### Property 5: Burn Decreases Sender Balance -/

/-- Successful burn decreases sender balance -/
theorem burn_decreases_balance
    (state state' : MintableTokenState) (msg : MsgContext) (amount : Amount)
    (h_success : burn state msg amount = Result.ok state') :
    balanceOf state' msg.sender = balanceOf state msg.sender - amount := by
  unfold burn require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [balanceOf, setBalance, ite_true]

/-! ### Property 6: Insufficient Balance Cannot Burn -/

/-- Cannot burn more than balance -/
theorem burn_insufficient_reverts
    (state : MintableTokenState) (msg : MsgContext) (amount : Amount)
    (h_insufficient : balanceOf state msg.sender < amount) :
    ∃ m, burn state msg amount = Result.revert m := by
  refine ⟨"ERC20: burn amount exceeds balance", ?_⟩
  unfold burn require
  simp only [Bind.bind, Pure.pure, Result.bind]
  have h : ¬(balanceOf state msg.sender ≥ amount) := Nat.not_le.mpr h_insufficient
  simp only [ge_iff_le, decide_eq_true_eq, h, not_true_eq_false, ite_false]

end Proofs

end Lab.ERC20
