import Translator.Parser.AST
import Translator.Generator.StateGen
import Translator.Generator.OpGen

/-!
# Transition System Generator

Generates ContractTransitionSystem skeleton for formal verification.

## Output Structure

```lean
def contractInit (s : State) : Prop := ...
def contractNext (s s' : State) : Prop := ...
def contractSafe (s : State) : Prop := ...
def contractInv (s : State) : Prop := ...

def contractTS : ContractTransitionSystem State := ...
```

## Invariant Templates

Based on contract pattern, applies pre-defined invariants:
- ERC20: balance bounds, supply conservation
- Vault: solvency, share conservation
- Lending: health factor bounds
-/

namespace Translator.Generator

open Translator.Parser

/-! ## Contract Pattern Detection -/

/-- Detected contract pattern -/
inductive ContractPattern
  | erc20      -- Has balances mapping and totalSupply
  | erc721     -- Has ownerOf mapping
  | vault      -- Has shares/assets pattern
  | lending    -- Has collateral/debt pattern
  | generic    -- Unknown pattern
deriving Repr, DecidableEq

/-- Detect contract pattern from state variables -/
def detectPattern (stateVars : List StateVar) : ContractPattern :=
  let names := stateVars.map (·.name.name)
  if names.contains "balances" && names.contains "totalSupply" then .erc20
  else if names.contains "ownerOf" || names.contains "_owners" then .erc721
  else if names.contains "shares" && names.contains "totalAssets" then .vault
  else if names.contains "collateral" && names.contains "debt" then .lending
  else .generic

/-! ## Invariant Templates -/

/-- Generate ERC20 invariants -/
def erc20Invariants (stateName : String) : String :=
  joinLines [
    s!"def MAX_UINT256 : Nat := 2^256 - 1",
    "",
    s!"/-- ERC20 Invariant: All balances bounded by total supply -/",
    s!"def balancesBounded (s : {stateName}) : Prop :=",
    s!"  ∀ addr, s.balances addr ≤ s.totalSupply",
    "",
    s!"/-- ERC20 Invariant: Total supply bounded -/",
    s!"def supplyBounded (s : {stateName}) : Prop :=",
    s!"  s.totalSupply ≤ MAX_UINT256"
  ]

/-- Generate Vault invariants -/
def vaultInvariants (stateName : String) : String :=
  joinLines [
    s!"/-- Vault Invariant: Solvency -/",
    s!"def solvency (s : {stateName}) : Prop :=",
    s!"  s.totalAssets ≥ s.totalShares",
    "",
    s!"/-- Vault Invariant: Shares bounded -/",
    s!"def sharesBounded (s : {stateName}) : Prop :=",
    s!"  ∀ addr, s.shares addr ≤ s.totalShares"
  ]

/-- Generate Lending invariants -/
def lendingInvariants (stateName : String) : String :=
  joinLines [
    s!"/-- Lending Invariant: Health factor -/",
    s!"def healthyPositions (s : {stateName}) : Prop :=",
    s!"  ∀ addr, s.debt addr = 0 ∨ s.collateral addr * 100 ≥ s.debt addr * 150",
    "",
    s!"/-- Lending Invariant: Reserve accounting -/",
    s!"def reserveAccounting (s : {stateName}) : Prop :=",
    s!"  s.totalDeposits ≥ s.totalBorrowed"
  ]

/-- Generate pattern-specific invariants -/
def genPatternInvariants (stateName : String) (pattern : ContractPattern) : String :=
  match pattern with
  | .erc20 => erc20Invariants stateName
  | .vault => vaultInvariants stateName
  | .lending => lendingInvariants stateName
  | _ => s!"/-- Add custom invariants here -/\ndef customInvariant (s : {stateName}) : Prop := True"

/-! ## Transition System Generation -/

/-- Generate Init predicate -/
def genInit (stateName : String) : String :=
  joinLines [
    s!"/-- Initial state predicate -/",
    s!"def {stateName}Init (s : {stateName}) : Prop :=",
    s!"  s = {stateName}.empty"
  ]

/-- Escape identifier if it's a Lean keyword -/
private def escapeIdentTS (name : String) : String :=
  let keywords := ["to", "in", "do", "if", "then", "else", "match", "with", "where", "let", "have",
   "fun", "forall", "import", "open", "variable", "def", "theorem", "lemma", "example",
   "structure", "class", "instance", "namespace", "section", "end", "return", "for"]
  if keywords.contains name then s!"{name}_" else name

/-- Generate Next predicate from functions -/
def genNext (stateName : String) (functions : List FunctionDef) : String :=
  let modifyingFns := functions.filter (·.modifiesState)
  if modifyingFns.isEmpty then
    joinLines [
      s!"/-- Transition relation (no state-modifying functions) -/",
      s!"def {stateName}Next (s s' : {stateName}) : Prop :=",
      s!"  False  -- TODO: Add transition cases"
    ]
  else
    let cases := modifyingFns.map fun fn =>
      let params := fn.params.map fun p => escapeIdentTS p.name.name
      let paramExists := params.map fun p => s!"∃ {p},"
      let fnCall := s!"{fn.name.name} s msg {" ".intercalate params} = Result.ok s'"
      s!"  ({" ".intercalate paramExists} {fnCall})"

    joinLines [
      s!"/-- Transition relation: successful operations -/",
      s!"def {stateName}Next (s s' : {stateName}) : Prop :=",
      s!"  ∃ msg,",
      " ∨\n".intercalate cases
    ]

/-- Generate Safe predicate -/
def genSafe (stateName : String) (pattern : ContractPattern) : String :=
  let invariantName := match pattern with
    | .erc20 => "balancesBounded"
    | .vault => "solvency"
    | .lending => "healthyPositions"
    | _ => "customInvariant"

  joinLines [
    s!"/-- Safety property -/",
    s!"def {stateName}Safe (s : {stateName}) : Prop :=",
    s!"  {invariantName} s"
  ]

/-- Generate Inv predicate -/
def genInv (stateName : String) (pattern : ContractPattern) : String :=
  let invariants := match pattern with
    | .erc20 => ["balancesBounded s", "supplyBounded s"]
    | .vault => ["solvency s", "sharesBounded s"]
    | .lending => ["healthyPositions s", "reserveAccounting s"]
    | _ => ["customInvariant s"]

  joinLines [
    s!"/-- Inductive invariant -/",
    s!"def {stateName}Inv (s : {stateName}) : Prop :=",
    s!"  {" ∧ ".intercalate invariants}"
  ]

/-- Generate transition system instance -/
def genTSInstance (stateName : String) : String :=
  joinLines [
    s!"/-- {stateName} transition system -/",
    s!"def {stateName}TS : ContractTransitionSystem {stateName} :=",
    "  { init := " ++ stateName ++ "Init",
    "  , next := " ++ stateName ++ "Next",
    "  , safe := " ++ stateName ++ "Safe",
    "  , inv := " ++ stateName ++ "Inv }"
  ]

/-- Generate proof stubs -/
def genProofStubs (stateName : String) : String :=
  joinLines [
    "/-! ## Proof Obligations -/",
    "",
    s!"/-- Initial states satisfy invariant -/",
    s!"theorem {stateName.toLower}_invInit : {stateName}TS.invInit' := by",
    s!"  intro s h_init",
    s!"  sorry  -- TODO: Prove init establishes invariant",
    "",
    s!"/-- Invariant implies safety -/",
    s!"theorem {stateName.toLower}_invSafe : {stateName}TS.invSafe' := by",
    s!"  intro s h_inv",
    s!"  sorry  -- TODO: Prove invariant implies safety",
    "",
    s!"/-- Transitions preserve invariant -/",
    s!"theorem {stateName.toLower}_invConsecution : {stateName}TS.invConsecution' := by",
    s!"  intro s s' h_inv h_next",
    s!"  sorry  -- TODO: Prove invariant preservation",
    "",
    s!"/-- Main theorem: Invariant is inductive -/",
    s!"theorem {stateName.toLower}_invInductive : {stateName}TS.invInductive' :=",
    s!"  ⟨{stateName.toLower}_invInit, {stateName.toLower}_invConsecution, {stateName.toLower}_invSafe⟩"
  ]

/-! ## Full Module Generation -/

/-- Generate transition system module -/
def genTransitionModule (contract : ContractDef) : String :=
  let name := contract.name.name
  let stateName := s!"{name}State"
  let pattern := detectPattern contract.stateVars
  let functions := contract.functions

  joinLines [
    s!"import Generated.{name}.State",
    s!"import Generated.{name}.Operations",
    s!"import Lab.ERC20.Model.TransitionSystem",
    "",
    s!"/-!",
    s!"# {name} Transition System",
    s!"",
    s!"Formal verification framework for {name} contract.",
    s!"Pattern detected: {repr pattern}",
    s!"-/",
    "",
    s!"namespace Generated.{name}.Model",
    "",
    "open Lab.ERC20 (Address Amount Result MsgContext)",
    "open Lab.ERC20.Model (ContractTransitionSystem)",
    s!"open Generated.{name}",
    "",
    "/-! ## Invariants -/",
    "",
    genPatternInvariants stateName pattern,
    "",
    "/-! ## Transition System Components -/",
    "",
    genInit stateName,
    "",
    genNext stateName functions,
    "",
    genSafe stateName pattern,
    "",
    genInv stateName pattern,
    "",
    "/-! ## Transition System Instance -/",
    "",
    genTSInstance stateName,
    "",
    genProofStubs stateName,
    "",
    s!"end Generated.{name}.Model"
  ]

/-! ## Invariants Module Generation -/

/-- Generate standalone invariants module for manual editing -/
def genInvariantsModule (contract : ContractDef) : String :=
  let name := contract.name.name
  let stateName := s!"{name}State"
  let pattern := detectPattern contract.stateVars

  joinLines [
    s!"import Generated.{name}.State",
    "",
    s!"/-!",
    s!"# {name} Custom Invariants",
    s!"",
    s!"Add custom invariants and properties here.",
    s!"Auto-detected pattern: {repr pattern}",
    s!"-/",
    "",
    s!"namespace Generated.{name}.Invariants",
    "",
    "open Lab.ERC20 (Address Amount)",
    s!"open Generated.{name}",
    "",
    genPatternInvariants stateName pattern,
    "",
    "/-! ## Custom Invariants -/",
    "",
    "-- Add your custom invariants below",
    "",
    s!"-- Example: def myInvariant (s : {stateName}) : Prop := ...",
    "",
    s!"end Generated.{name}.Invariants"
  ]

/-! ## Main Entry Points -/

/-- Generate transition system module from source file -/
def generateTransition (source : SourceFile) : List (String × String) :=
  source.contracts.map fun c =>
    let moduleName := s!"Generated/{c.name.name}/TransitionSystem.lean"
    let content := genTransitionModule c
    (moduleName, content)

/-- Generate invariants module from source file -/
def generateInvariants (source : SourceFile) : List (String × String) :=
  source.contracts.map fun c =>
    let moduleName := s!"Generated/{c.name.name}/Invariants.lean"
    let content := genInvariantsModule c
    (moduleName, content)

/-- Generate all modules for a contract -/
def generateAll (source : SourceFile) : List (String × String) :=
  generateState source ++
  generateOps source ++
  generateTransition source ++
  generateInvariants source

end Translator.Generator
