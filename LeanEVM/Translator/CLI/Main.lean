import Translator.Parser.AST
import Translator.Parser.Lexer
import Translator.Parser.Parser
import Translator.Generator.StateGen
import Translator.Generator.OpGen
import Translator.Generator.TransitionGen

/-!
# Solidity-to-Lean Translator CLI

Command-line interface for translating Solidity contracts to Lean.

## Usage

```
lake exe sol2lean <input.sol> [--output <dir>]
```
-/

namespace Translator.CLI

open Translator.Parser
open Translator.Generator

/-- Translation result -/
structure TranslationResult where
  files : List (String × String)  -- (filename, content) pairs
  warnings : List String
  errors : List String
deriving Repr

/-- Translate Solidity source to Lean modules -/
def translate (source : String) : TranslationResult :=
  -- Parse (tokenization is internal)
  match Parser.parse source with
  | .error err =>
    { files := [], warnings := [], errors := [s!"Parse error: {err.message} at line {err.pos.line}"] }
  | .ok sourceFile =>
    -- Generate
    let files := generateAll sourceFile
    { files := files, warnings := [], errors := [] }

/-- Format translation result for display -/
def formatResult (result : TranslationResult) : String :=
  if !result.errors.isEmpty then
    let errLines := result.errors.map (· ++ "\n")
    "Errors:\n" ++ errLines.foldl (· ++ ·) ""
  else
    let header := s!"Generated {result.files.length} files:\n"
    let fileList := result.files.map fun (name, _) => s!"  - {name}\n"
    header ++ fileList.foldl (· ++ ·) ""

/-- Write files to output directory -/
def writeFiles (outDir : String) (files : List (String × String)) : IO Unit := do
  for (name, content) in files do
    let path := System.FilePath.mk outDir / name
    -- Ensure parent directory exists
    if let some parent := path.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile path content
    IO.println s!"  Created: {path}"

/-- Preview translation without writing files -/
def preview (source : String) : IO Unit := do
  let result := translate source
  if !result.errors.isEmpty then
    for err in result.errors do
      IO.eprintln s!"Error: {err}"
  else
    IO.println "=== Translation Preview ==="
    for (name, content) in result.files do
      IO.println s!"\n--- {name} ---"
      IO.println content

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "Usage: sol2lean <input.sol> [--output <dir>] [--preview]"
    IO.println ""
    IO.println "Options:"
    IO.println "  --output <dir>  Output directory (default: ./Generated)"
    IO.println "  --preview       Preview output without writing files"
    return 1
  | inputFile :: rest =>
    -- Read input
    let source ← IO.FS.readFile inputFile

    -- Check for preview mode
    if rest.contains "--preview" then
      preview source
      return 0

    -- Translate
    let result := translate source

    if !result.errors.isEmpty then
      for err in result.errors do
        IO.eprintln s!"Error: {err}"
      return 1

    -- Determine output directory
    let outDir := match rest.dropWhile (· != "--output") with
      | "--output" :: dir :: _ => dir
      | _ => "."

    -- Write files
    IO.println s!"Translating {inputFile}..."
    writeFiles outDir result.files
    IO.println s!"\nGenerated {result.files.length} Lean files."

    return 0

end Translator.CLI
