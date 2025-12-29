import Translator.Parser.AST
import Translator.Parser.Lexer
import Translator.Parser.Parser
import Translator.Generator.StateGen
import Translator.Generator.OpGen
import Translator.Generator.TransitionGen

/-!
# Translator Test

Test the Solidity-to-Lean translation pipeline.
-/

open Translator.Parser
open Translator.Generator

/-- Simple token contract source -/
def simpleTokenSource : String := "
contract SimpleToken {
    mapping(address => uint256) public balances;
    uint256 public totalSupply;

    function transfer(address to, uint256 amount) public {
        require(balances[msg.sender] >= amount, \"insufficient balance\");
        balances[msg.sender] -= amount;
        balances[to] += amount;
    }

    function mint(address to, uint256 amount) public {
        balances[to] += amount;
        totalSupply += amount;
    }
}
"

/-- Test tokenization -/
def testLexer : IO Unit := do
  IO.println "=== Lexer Test ==="
  let tokens := tokenize simpleTokenSource
  IO.println s!"Tokenized {tokens.length} tokens"
  -- Print first 20 tokens
  for tok in tokens.take 20 do
    IO.println s!"  {tok.kind}"

/-- Test parsing -/
def testParser : IO Unit := do
  IO.println "\n=== Parser Test ==="
  match Translator.Parser.parse simpleTokenSource with
  | .error err =>
    IO.println s!"Parse error: {err.message} at line {err.pos.line}"
  | .ok sourceFile =>
    IO.println s!"Parsed {sourceFile.contracts.length} contracts"
    for c in sourceFile.contracts do
      IO.println s!"  Contract: {c.name.name}"
      IO.println s!"    State vars: {c.stateVars.length}"
      for sv in c.stateVars do
        IO.println s!"      - {sv.name.name} : {sv.type}"
      IO.println s!"    Functions: {c.functions.length}"
      for f in c.functions do
        IO.println s!"      - {f.name.name}({f.params.length} params)"

/-- Test code generation -/
def testGenerator : IO Unit := do
  IO.println "\n=== Generator Test ==="
  match Translator.Parser.parse simpleTokenSource with
  | .error err =>
    IO.println s!"Parse error: {err.message}"
  | .ok sourceFile =>
    let files := generateAll sourceFile
    IO.println s!"Generated {files.length} files:"
    for (name, content) in files do
      IO.println s!"\n--- {name} ---"
      -- Print first 50 lines
      let lines := content.splitOn "\n"
      for line in lines.take 50 do
        IO.println line

/-- Write generated files to disk -/
def writeGeneratedFiles : IO Unit := do
  IO.println "\n=== Writing Generated Files ==="
  match Translator.Parser.parse simpleTokenSource with
  | .error err =>
    IO.println s!"Parse error: {err.message}"
  | .ok sourceFile =>
    let files := generateAll sourceFile
    for (name, content) in files do
      let path := System.FilePath.mk "." / name
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path content
      IO.println s!"  Created: {path}"

/-- Run all tests -/
def main : IO Unit := do
  testLexer
  testParser
  testGenerator
  writeGeneratedFiles

#eval main
