import Lab.ERC20.Contracts.Interface

/-!
# ERC-20 Safety Properties

Common safety properties that all ERC-20 tokens should satisfy.

## Property Categories

1. **No Zero Address** - Cannot send to/approve zero address
2. **Balance Checks** - Operations respect balance limits
3. **Allowance Checks** - TransferFrom respects allowances
4. **Reentrancy Safety** - State changes before external calls
-/

namespace Lab.ERC20.Properties

open Lab.ERC20

/-! ## Safety Property Definitions -/

/-- Property: Transfer never sends to zero address -/
def NoTransferToZero (S : Type) [ERC20State S] [ERC20Ops S] : Prop :=
  ∀ (state : S) (msg : MsgContext) (amount : Amount),
    ∃ m, ERC20Ops.transfer state msg Address.zero amount = Result.revert m

/-- Property: Approve never approves zero address -/
def NoApproveToZero (S : Type) [ERC20State S] [ERC20Ops S] : Prop :=
  ∀ (state : S) (msg : MsgContext) (amount : Amount),
    ∃ m, ERC20Ops.approve state msg Address.zero amount = Result.revert m

/-- Property: Transfer respects balance -/
def TransferRespectsBalance (S : Type) [ERC20State S] [ERC20Ops S] : Prop :=
  ∀ (state : S) (msg : MsgContext) (recipient : Address) (amount : Amount),
    ERC20State.balanceOf state msg.sender < amount →
    recipient.isZero = false →
    ∃ m, ERC20Ops.transfer state msg recipient amount = Result.revert m

/-- Property: TransferFrom respects allowance -/
def TransferFromRespectsAllowance (S : Type) [ERC20State S] [ERC20Ops S] : Prop :=
  ∀ (state : S) (msg : MsgContext) (fromAddr recipient : Address) (amount : Amount),
    ERC20State.allowance state fromAddr msg.sender < amount →
    recipient.isZero = false →
    ∃ m, ERC20Ops.transferFrom state msg fromAddr recipient amount = Result.revert m

/-! ## Composite Safety -/

/-- All basic safety properties combined -/
def BasicSafety (S : Type) [ERC20State S] [ERC20Ops S] : Prop :=
  NoTransferToZero S ∧
  NoApproveToZero S ∧
  TransferRespectsBalance S

/-! ## Property Checkers -/

/-- Check if a state transition preserves an invariant -/
def PreservesInvariant {S : Type} (inv : S → Prop) (op : S → Result S) : Prop :=
  ∀ s s', inv s → op s = Result.ok s' → inv s'

/-- Check if an operation is idempotent -/
def IsIdempotent {S : Type} [DecidableEq S] (op : S → Result S) : Prop :=
  ∀ s s', op s = Result.ok s' → op s' = Result.ok s'

end Lab.ERC20.Properties
