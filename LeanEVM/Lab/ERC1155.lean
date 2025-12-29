import Lab.ERC1155.Contracts.Interface
import Lab.ERC1155.Contracts.MultiToken
import Lab.ERC1155.Properties.Invariants
import Lab.ERC1155.Model.TransitionSystem

/-!
# ERC-1155 Multi-Token Verification Laboratory

Formal verification environment for ERC-1155 multi-token contracts.

## Quick Start

```lean
import Lab.ERC1155

open Lab.ERC1155

-- Create a multi-token contract
def myTokens := MultiTokenState.init ⟨1⟩ "https://example.com/tokens/"

-- Verify properties
#check transfer_preserves_supply
#check mint_increases_supply
```

## Structure

- **Contracts/Interface.lean** - Abstract ERC-1155 interface
- **Contracts/MultiToken.lean** - Concrete implementation
- **Properties/Invariants.lean** - Multi-token invariants

## Key Features

1. **Multiple Token Types**: Manage fungible and non-fungible tokens together
2. **Batch Operations**: Atomic transfers of multiple token types
3. **Operator Approvals**: Approve operators for all tokens at once

## Verified Properties

- Transfer preserves supply (no tokens created/destroyed)
- Unauthorized transfers revert
- Mint/burn correctly update supply
- Approvals don't affect balances
-/
