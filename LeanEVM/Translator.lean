/-!
# Solidity-to-Lean Translator

Translates Solidity smart contracts into verified Lean models.

## Components

- `Parser`: Tokenization and parsing of Solidity source
- `Analyzer`: Storage layout and function analysis
- `Generator`: Lean code generation
- `CLI`: Command-line interface

## Supported Solidity Features (v0.1)

**Types**: uint256, address, bool, mapping
**Functions**: public, external, view
**Control**: require, if/else, return
**Modifiers**: onlyOwner (inlined)

## Usage

```
leanaudit translate MyContract.sol
```
-/

import Translator.Parser.AST
import Translator.Parser.Lexer
import Translator.Parser.Parser
import Translator.Generator.StateGen
import Translator.Generator.OpGen
import Translator.Generator.TransitionGen
