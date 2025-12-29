import Lab.ERC20.Contracts.BasicToken
import Lab.ERC20.Contracts.MintableToken
import Lab.ERC20.Properties.Safety
import Lab.ERC20.Properties.Invariants

/-!
# Verified ERC-20 Token Example

Complete example demonstrating how to verify ERC-20 properties.

## Verification Checklist

1. ✓ Safety: Cannot transfer to zero address
2. ✓ Safety: Insufficient balance reverts
3. ✓ Invariant: Supply is constant (BasicToken)
4. ✓ Correctness: Transfer updates balances correctly
5. ✓ Access Control: Only owner can mint (MintableToken)

## How to Use This Lab

1. Study the property definitions in Properties/
2. Examine the implementations in Contracts/
3. Follow the proof patterns below
4. Try adding your own properties
-/

namespace Lab.ERC20.Examples

open Lab.ERC20
open Lab.ERC20.Properties

/-! ## BasicToken Safety Verification -/

section BasicTokenSafety

/-- BasicToken satisfies NoTransferToZero -/
theorem basicToken_noTransferToZero :
    NoTransferToZero BasicTokenState := by
  intro state msg amount
  exact transfer_to_zero_reverts state msg amount

/-- BasicToken satisfies TransferRespectsBalance -/
theorem basicToken_transferRespectsBalance :
    TransferRespectsBalance BasicTokenState := by
  intro state msg recipient amount h_insufficient h_to_nonzero
  exact transfer_insufficient_reverts state msg recipient amount h_to_nonzero h_insufficient

end BasicTokenSafety

/-! ## MintableToken Access Control -/

section MintableTokenAccess

/-- MintableToken enforces owner-only minting -/
theorem mintableToken_ownerOnlyMint
    (state : MintableTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_not_owner : msg.sender ≠ state.owner) :
    ∃ m, MintableToken.mint state msg recipient amount = Result.revert m :=
  mint_requires_owner state msg recipient amount h_not_owner

end MintableTokenAccess

/-! ## Correctness Properties -/

section Correctness

open ERC20State

/-- After successful transfer, receiver balance increases -/
theorem transfer_receiver_increases
    (state state' : BasicTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : BasicToken.transfer state msg recipient amount = Result.ok state')
    (h_different : msg.sender ≠ recipient) :
    balanceOf state' recipient = balanceOf state recipient + amount := by
  unfold BasicToken.transfer require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [balanceOf, setBalance]
  have h : ¬(recipient = msg.sender) := fun h => h_different h.symm
  simp only [h, ite_false, ite_true]

/-- After successful transfer, sender balance decreases -/
theorem transfer_sender_decreases
    (state state' : BasicTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : BasicToken.transfer state msg recipient amount = Result.ok state')
    (h_different : msg.sender ≠ recipient) :
    balanceOf state' msg.sender = balanceOf state msg.sender - amount := by
  unfold BasicToken.transfer require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  simp only [balanceOf, setBalance]
  have h : ¬(msg.sender = recipient) := h_different
  simp only [ite_true, h, ite_false]

end Correctness

/-! ## Invariant Verification -/

section InvariantVerification

/-- BasicToken preserves supply through transfer -/
theorem basicToken_supplyConstant_transfer
    (state state' : BasicTokenState) (msg : MsgContext) (recipient : Address) (amount : Amount)
    (h_success : BasicToken.transfer state msg recipient amount = Result.ok state') :
    SupplyConstant state state' := by
  unfold SupplyConstant
  exact transfer_preserves_supply state state' msg recipient amount h_success

/-- BasicToken preserves supply through approve -/
theorem basicToken_supplyConstant_approve
    (state state' : BasicTokenState) (msg : MsgContext) (spender : Address) (amount : Amount)
    (h_success : BasicToken.approve state msg spender amount = Result.ok state') :
    SupplyConstant state state' := by
  unfold SupplyConstant
  unfold BasicToken.approve require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  rfl

/-- BasicToken preserves supply through transferFrom -/
theorem basicToken_supplyConstant_transferFrom
    (state state' : BasicTokenState) (msg : MsgContext) (fromAddr recipient : Address) (amount : Amount)
    (h_success : BasicToken.transferFrom state msg fromAddr recipient amount = Result.ok state') :
    SupplyConstant state state' := by
  unfold SupplyConstant
  unfold BasicToken.transferFrom require at h_success
  simp only [Bind.bind, Pure.pure, Result.bind] at h_success
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  split at h_success <;> try contradiction
  simp only [Result.ok.injEq] at h_success
  subst h_success
  rfl

end InvariantVerification

/-! ## Example: Creating a Token -/

section Example

/-- Create a token with initial supply to deployer -/
def createToken (deployer : Address) : BasicTokenState :=
  BasicTokenState.init deployer 1000000

/-- Deployer starts with all tokens -/
theorem deployer_has_all_tokens (deployer : Address) :
    ERC20State.balanceOf (createToken deployer) deployer = 1000000 := by
  unfold createToken BasicTokenState.init ERC20State.balanceOf
  exact if_pos rfl

/-- Others start with zero -/
theorem others_start_zero (deployer other : Address) (h : other ≠ deployer) :
    ERC20State.balanceOf (createToken deployer) other = 0 := by
  unfold createToken BasicTokenState.init ERC20State.balanceOf
  have hne : ¬(other = deployer) := h
  exact if_neg hne

end Example

/-! ## Exercise: Add Your Own Properties -/

/-
Try adding these properties:

1. Self-transfer doesn't change balance
2. Double approve overwrites the first
3. TransferFrom with zero amount succeeds
4. Approve then transfer pattern works correctly

Hint: Follow the pattern in the proofs above:
1. unfold the operation definition
2. simp to simplify the bind/result handling
3. split on conditionals
4. use cases to extract the resulting state
-/

end Lab.ERC20.Examples
