# LeanEVM

A proof-of-concept framework for formal verification of Ethereum smart contracts using Lean 4.

## Overview

LeanEVM demonstrates how to apply theorem proving techniques to verify smart contract properties. Inspired by the [Veil framework](https://github.com/verse-lab/veil), it embeds the entire verification workflow within Lean 4.

### Philosophy

- **All goals are Lean goals** - No separate specification language
- **All proofs are Lean proofs** - Full power of interactive theorem proving
- **Seamless automation fallback** - When SMT fails, prove manually

## Features

### Core Types (`LeanEVM.Core.Types`)
- `Address` - Ethereum addresses
- `Storage` - Contract storage as functions
- `Balances` - ETH balance tracking
- Safe arithmetic with overflow checking

### Execution Model (`LeanEVM.Core.Execution`)
- `ExecResult` monad for success/revert/outOfGas
- Reentrancy guard pattern
- Two-state reasoning for transitions

### ERC-20 Model (`LeanEVM.Contracts.ERC20`)
- Full ERC-20 interface
- Verified properties:
  - Transfer conservation
  - Balance correctness
  - Zero-address safety
  - Insufficient balance reverts
  - Allowance correctness

### ERC-721 NFT Model (`LeanEVM.Contracts.ERC721`)
- Full ERC-721 interface (mint, burn, transfer, approve)
- Verified properties:
  - Mint to zero address reverts
  - Cannot mint existing token
  - Transfer to zero address reverts
  - Transfer updates owner correctly
  - Mint increases balance
  - Cannot approve self as operator

### AMM Model (`LeanEVM.Contracts.AMM`)
- Uniswap v2 style constant-product AMM
- Features:
  - Token pair liquidity pools
  - LP token minting/burning
  - Swap with 0.3% fee
  - Minimum liquidity protection
- Verified properties:
  - Cannot initialize twice
  - Cannot swap on empty pool
  - Zero input swap reverts
  - Insufficient LP tokens reverts
  - Initialized pool has positive reserves
  - Minimum liquidity locked to zero address

### Safety Properties (`LeanEVM.Properties.SafetyProperties`)
- Access control patterns
- Reentrancy safety proofs
- Vault deposit/withdraw symmetry
- Bounded value reasoning

## Getting Started

### Prerequisites
- Lean 4 (v4.14.0)
- Lake build system

### Building

```bash
cd LeanEVM
lake update
lake build
```

### Example: Verify Transfer Conservation

```lean
import LeanEVM

open LeanEVM.Contracts

-- The theorem states: sender balance + receiver balance is unchanged
#check transfer_conserves_local_balance

-- Use it in a proof
example (state state' : TokenState) (msg : MsgContext) (to_ : Address) (amount : Nat)
    (h_neq : msg.sender ≠ to_)
    (h_success : transfer state msg to_ amount = ExecResult.success state') :
    state.balanceOf msg.sender + state.balanceOf to_ =
    state'.balanceOf msg.sender + state'.balanceOf to_ :=
  transfer_conserves_local_balance state state' msg to_ amount h_neq h_success
```

## Verified Properties

### ERC-20 Token

| Property | Theorem | Status |
|----------|---------|--------|
| Transfer conserves local balance | `transfer_conserves_local_balance` | ✓ Proved |
| Transfer preserves total supply | `transfer_preserves_totalSupply` | ✓ Proved |
| Sender balance decreases by amount | `transfer_decreases_sender` | ✓ Proved |
| Receiver balance increases by amount | `transfer_increases_receiver` | ✓ Proved |
| Transfer to zero reverts | `transfer_to_zero_reverts` | ✓ Proved |
| Insufficient balance reverts | `transfer_insufficient_balance_reverts` | ✓ Proved |
| Approve sets exact allowance | `approve_sets_allowance` | ✓ Proved |
| TransferFrom decreases allowance | `transferFrom_decreases_allowance` | ✓ Proved |

### Reentrancy Safety

| Property | Theorem | Status |
|----------|---------|--------|
| Guarded functions reject reentrant calls | `guarded_is_reentrancy_safe` | ✓ Proved |
| Role-restricted functions revert for non-members | `onlyRole_reverts_non_member` | ✓ Proved |

### ERC-721 NFT

| Property | Theorem | Status |
|----------|---------|--------|
| Mint to zero address reverts | `mint_to_zero_reverts` | ✓ Proved |
| Cannot mint existing token | `mint_existing_reverts` | ✓ Proved |
| Transfer to zero reverts | `transferFrom_to_zero_reverts` | ✓ Proved |
| Transfer invalid token reverts | `transferFrom_invalid_token_reverts` | ✓ Proved |
| Transfer updates owner | `transferFrom_updates_owner` | ✓ Proved |
| Cannot approve self as operator | `setApprovalForAll_self_reverts` | ✓ Proved |
| Mint increases balance | `mint_increases_balance` | ✓ Proved |

### AMM (Automated Market Maker)

| Property | Theorem | Status |
|----------|---------|--------|
| Cannot initialize twice | `initialize_twice_reverts` | ✓ Proved |
| Cannot swap on empty pool | `swap_empty_reverts` | ✓ Proved |
| Zero input swap reverts | `swap_zero_reverts` | ✓ Proved |
| Insufficient LP tokens reverts | `remove_insufficient_reverts` | ✓ Proved |
| Initialized pool has reserves | `initialized_has_reserves` | ✓ Proved |
| Empty pool not initialized | `empty_not_initialized` | ✓ Proved |
| getAmountOut fails on zero reserve | `getAmountOut_none_zero_reserve` | ✓ Proved |
| Minimum liquidity locked | `init_locks_minimum_liquidity` | ✓ Proved |

### Vault Pattern

| Property | Theorem | Status |
|----------|---------|--------|
| Deposit updates total correctly | `deposit_preserves_invariant_local` | ✓ Proved |
| Withdraw updates total correctly | `withdraw_preserves_invariant_local` | ✓ Proved |

## Architecture

```
LeanEVM/
├── LeanEVM.lean              # Main library entry point
├── LeanEVM/
│   ├── Core/
│   │   ├── Types.lean        # EVM primitive types
│   │   └── Execution.lean    # Execution model
│   ├── Contracts/
│   │   ├── ERC20.lean        # ERC-20 token model
│   │   ├── ERC721.lean       # ERC-721 NFT model
│   │   └── AMM.lean          # Automated Market Maker model
│   └── Properties/
│       └── SafetyProperties.lean  # Property framework
├── lakefile.lean             # Build configuration
└── README.md
```

## Roadmap

### Phase 1: Foundation (Current)
- [x] Basic EVM types
- [x] Execution monad
- [x] ERC-20 model with proofs
- [x] ERC-721 NFT model with proofs
- [x] AMM (Uniswap v2 style) model with proofs
- [x] Reentrancy guard pattern

### Phase 2: Extended Contracts
- [ ] Vault/Staking contracts
- [ ] ERC-1155 multi-token model
- [ ] Lending protocol (Aave-style)

### Phase 3: Automation
- [ ] SMT integration for arithmetic
- [ ] Custom decision procedures
- [ ] Counterexample generation

### Phase 4: Real-World
- [ ] Solidity-to-Lean translator
- [ ] Verification of deployed contracts
- [ ] Integration with security contest workflow

## Comparison with Other Tools

| Feature | LeanEVM | Certora | Halmos | Kontrol |
|---------|---------|---------|--------|---------|
| Interactive proofs | ✓ | ✗ | ✗ | Limited |
| Higher-order logic | ✓ | ✗ | ✗ | ✗ |
| Open source | ✓ | ✗ | ✓ | ✓ |
| SMT automation | Planned | ✓ | ✓ | ✓ |
| Learning curve | High | Medium | Low | Medium |

## Contributing

This is a proof-of-concept. Contributions welcome for:
- Additional contract models
- More property theorems
- Automation tactics
- Documentation

## References

- [Veil: A Framework for Automated and Interactive Verification](https://github.com/verse-lab/veil)
- [A Survey of Attacks on Ethereum Smart Contracts](https://eprint.iacr.org/2016/1007)
- [OWASP Smart Contract Top 10](https://owasp.org/www-project-smart-contract-top-10/)
- [KEVM: Complete Formal Semantics of the EVM](https://github.com/runtimeverification/evm-semantics)

## License

MIT
