/-!
# LeanEVM: Formal Verification of EVM Smart Contracts

A Lean 4 framework for modeling and verifying Ethereum smart contracts.

## Overview

LeanEVM provides:
- Core EVM types (addresses, storage, balances)
- Execution model with reentrancy support
- Contract modeling DSL
- Property specification and verification

## Example

```lean
import LeanEVM

open LeanEVM.Contracts

-- Create a token with 1000 supply
def myToken := TokenState.init ⟨1⟩ 1000

-- Verify transfer conservation
#check transfer_conserves_local_balance
```

## Modules

- `LeanEVM.Core.Types`: Basic EVM types
- `LeanEVM.Core.Execution`: Execution model
- `LeanEVM.Contracts.ERC20`: ERC-20 token model
- `LeanEVM.Contracts.ERC721`: ERC-721 NFT model
- `LeanEVM.Properties.SafetyProperties`: Property framework
-/

-- Core modules
import LeanEVM.Core.Types
import LeanEVM.Core.Execution

-- Contract models
import LeanEVM.Contracts.ERC20
import LeanEVM.Contracts.ERC721

-- Property framework
import LeanEVM.Properties.SafetyProperties
