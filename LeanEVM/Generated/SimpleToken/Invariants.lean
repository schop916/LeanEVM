import Generated.SimpleToken.State

/-!
# SimpleToken Custom Invariants

Add custom invariants and properties here.
Auto-detected pattern: Translator.Generator.ContractPattern.erc20
-/

namespace Generated.SimpleToken.Invariants

open Lab.ERC20 (Address Amount)
open Generated.SimpleToken

def MAX_UINT256 : Nat := 2^256 - 1

/-- ERC20 Invariant: All balances bounded by total supply -/
def balancesBounded (s : SimpleTokenState) : Prop :=
  ∀ addr, s.balances addr ≤ s.totalSupply

/-- ERC20 Invariant: Total supply bounded -/
def supplyBounded (s : SimpleTokenState) : Prop :=
  s.totalSupply ≤ MAX_UINT256

/-! ## Custom Invariants -/

-- Add your custom invariants below

-- Example: def myInvariant (s : SimpleTokenState) : Prop := ...

end Generated.SimpleToken.Invariants