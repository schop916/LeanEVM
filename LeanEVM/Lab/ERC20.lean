import Lab.ERC20.Contracts.Interface
import Lab.ERC20.Contracts.BasicToken
import Lab.ERC20.Contracts.MintableToken
import Lab.ERC20.Properties.Safety
import Lab.ERC20.Properties.Invariants
import Lab.ERC20.Proofs.Attributes
import Lab.ERC20.Proofs.Tactics
import Lab.ERC20.Model.TransitionSystem
import Lab.ERC20.Model.LawfulOp
import Lab.ERC20.Examples.VerifiedToken
import Lab.ERC20.Examples.TransitionSystemExample
import Lab.ERC20.Examples.MintableTransitionSystem

/-!
# ERC-20 Verification Laboratory

A hands-on environment for formally verifying ERC-20 token contracts.

## Quick Start

```lean
import Lab.ERC20

-- Load an example contract
open Lab.ERC20.Examples

-- Verify a property
#check BasicToken.transfer_preserves_supply
```

## Structure

- **Contracts/** - ERC-20 contract models to verify
- **Properties/** - Common ERC-20 properties and invariants
- **Proofs/** - Verification tactics and proof strategies
- **Examples/** - Complete verified examples

## Workflow

1. Define your token contract state and operations
2. Specify properties you want to verify
3. Write proofs (or use automation)
4. Check that proofs compile (= verified!)
-/
