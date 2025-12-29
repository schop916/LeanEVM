import Generated.SimpleToken.State

/-!
# SimpleToken Operations

Auto-generated operations for SimpleToken contract.
-/

namespace Generated.SimpleToken

open Lab.ERC20 (Address Amount Result MsgContext require)

/-! ## Operations -/

/-- transfer -/
def transfer (s : SimpleTokenState) (msg : MsgContext)
    (to_ : Address) (amount : Nat) : Result SimpleTokenState := do
  require (((s.balances msg.sender) ≥ amount)) "insufficient balance"
  let s := { s with balances := fun k => if k = msg.sender then s.balances k - amount else s.balances k }
  let s := { s with balances := fun k => if k = to_ then s.balances k + amount else s.balances k }
  pure s


/-- mint -/
def mint (s : SimpleTokenState) (msg : MsgContext)
    (to_ : Address) (amount : Nat) : Result SimpleTokenState := do
  let s := { s with balances := fun k => if k = to_ then s.balances k + amount else s.balances k }
  let s := { s with totalSupply := s.totalSupply + amount }
  pure s

end Generated.SimpleToken