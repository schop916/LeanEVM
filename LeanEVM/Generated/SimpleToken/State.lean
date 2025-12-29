import Lab.ERC20.Contracts.Interface

/-!
# SimpleToken State

Auto-generated state structure for SimpleToken contract.
-/

namespace Generated.SimpleToken

open Lab.ERC20 (Address Amount Result MsgContext require)

/-! ## State Structure -/

/-- State for SimpleToken contract -/
structure SimpleTokenState where
  balances : (Address → Nat) -- public
  totalSupply : Nat -- public


/-- Create empty SimpleToken state -/
def SimpleTokenState.empty : SimpleTokenState :=
  {
  balances := (fun _ => 0)
  totalSupply := 0
  }

/-! ## Accessors -/

/-- Get balances for key -/
def SimpleTokenState.getBalances (s : SimpleTokenState) (key : Address) : Nat :=
  s.balances key

/-- Set balances for key -/
def SimpleTokenState.setBalances (s : SimpleTokenState) (key : Address) (val : Nat) : SimpleTokenState :=
  { s with balances := fun k => if k == key then val else s.balances k }


/-- Get totalSupply -/
def SimpleTokenState.getTotalSupply (s : SimpleTokenState) : Nat :=
  s.totalSupply

/-- Set totalSupply -/
def SimpleTokenState.setTotalSupply (s : SimpleTokenState) (val : Nat) : SimpleTokenState :=
  { s with totalSupply := val }

end Generated.SimpleToken