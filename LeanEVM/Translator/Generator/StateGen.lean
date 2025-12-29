import Translator.Parser.AST

/-!
# State Structure Generator

Generates Lean state structures from Solidity contracts.

## Output Format

For a Solidity contract:
```solidity
mapping(address => uint256) public balances;
uint256 public totalSupply;
```

Generates:
```lean
structure MyContractState where
  balances : Address → Amount
  totalSupply : Amount
```
-/

namespace Translator.Generator

open Translator.Parser

/-! ## Lean Type Mapping -/

/-- Map Solidity type to Lean type string -/
def solTypeToLean : SolType → String
  | .uint256 => "Nat"
  | .address => "Address"
  | .bool => "Bool"
  | .mapping k v => s!"({solTypeToLean k} → {solTypeToLean v})"
  | .array t => s!"(List {solTypeToLean t})"
  | .custom id => id.name

/-- Map Solidity type to default value -/
def solTypeDefault : SolType → String
  | .uint256 => "0"
  | .address => "⟨0⟩"
  | .bool => "false"
  | .mapping _ v => s!"(fun _ => {solTypeDefault v})"
  | .array _ => "[]"
  | .custom _ => "default"

/-! ## Code Generation Helpers -/

/-- Indentation helper -/
def indent (n : Nat) (s : String) : String :=
  String.mk (List.replicate (n * 2) ' ') ++ s

/-- Join lines -/
def joinLines (lines : List String) : String :=
  String.intercalate "\n" lines

/-! ## State Structure Generation -/

/-- Generate state structure field -/
def genStateField (sv : StateVar) : String :=
  let ty := solTypeToLean sv.type
  let comment := if sv.visibility == .public_ then " -- public" else ""
  indent 1 s!"{sv.name.name} : {ty}{comment}"

/-- Generate empty state constructor -/
def genEmptyState (name : String) (stateVars : List StateVar) : String :=
  let fields := stateVars.map fun sv =>
    indent 1 s!"{sv.name.name} := {solTypeDefault sv.type}"
  joinLines [
    s!"/-- Create empty {name} state -/",
    s!"def {name}State.empty : {name}State :=",
    "  {",
    joinLines fields,
    "  }"
  ]

/-- Check if state has any function types (mappings/arrays) -/
def hasNonReprable (stateVars : List StateVar) : Bool :=
  stateVars.any fun sv => match sv.type with
    | .mapping _ _ => true
    | .array _ => true
    | _ => false

/-- Generate state structure -/
def genStateStruct (contract : ContractDef) : String :=
  let name := contract.name.name
  let stateVars := contract.stateVars
  let fields := stateVars.map genStateField
  -- Only derive Repr if no function types
  let deriveClause := if hasNonReprable stateVars then "" else "deriving Repr"

  if fields.isEmpty then
    joinLines [
      s!"/-- State for {name} contract -/",
      s!"structure {name}State where",
      indent 1 "dummy : Unit := ()"
    ]
  else
    joinLines [
      s!"/-- State for {name} contract -/",
      s!"structure {name}State where",
      joinLines fields,
      deriveClause,
      "",
      genEmptyState name stateVars
    ]

/-! ## Getter/Setter Generation -/

/-- Generate getter for public state variable -/
def genGetter (contractName : String) (sv : StateVar) : String :=
  match sv.type with
  | .mapping k v =>
    let keyType := solTypeToLean k
    let valType := solTypeToLean v
    joinLines [
      s!"/-- Get {sv.name.name} for key -/",
      s!"def {contractName}State.get{capitalize sv.name.name} (s : {contractName}State) (key : {keyType}) : {valType} :=",
      s!"  s.{sv.name.name} key"
    ]
  | t =>
    let retType := solTypeToLean t
    joinLines [
      s!"/-- Get {sv.name.name} -/",
      s!"def {contractName}State.get{capitalize sv.name.name} (s : {contractName}State) : {retType} :=",
      s!"  s.{sv.name.name}"
    ]
where
  capitalize (s : String) : String :=
    match s.data with
    | c :: cs => String.mk (c.toUpper :: cs)
    | [] => s

/-- Generate setter for state variable -/
def genSetter (contractName : String) (sv : StateVar) : String :=
  let valType := solTypeToLean sv.type
  match sv.type with
  | .mapping k v =>
    let keyType := solTypeToLean k
    let innerType := solTypeToLean v
    joinLines [
      s!"/-- Set {sv.name.name} for key -/",
      s!"def {contractName}State.set{capitalize sv.name.name} (s : {contractName}State) (key : {keyType}) (val : {innerType}) : {contractName}State :=",
      "  { s with " ++ sv.name.name ++ " := fun k => if k == key then val else s." ++ sv.name.name ++ " k }"
    ]
  | _ =>
    joinLines [
      s!"/-- Set {sv.name.name} -/",
      s!"def {contractName}State.set{capitalize sv.name.name} (s : {contractName}State) (val : {valType}) : {contractName}State :=",
      "  { s with " ++ sv.name.name ++ " := val }"
    ]
where
  capitalize (s : String) : String :=
    match s.data with
    | c :: cs => String.mk (c.toUpper :: cs)
    | [] => s

/-- Generate all getters and setters -/
def genAccessors (contract : ContractDef) : String :=
  let name := contract.name.name
  let stateVars := contract.stateVars
  let accessors := stateVars.map fun sv =>
    let getter := if sv.visibility == .public_ then genGetter name sv else ""
    let setter := genSetter name sv
    if getter.isEmpty then setter else getter ++ "\n\n" ++ setter
  joinLines (accessors.intersperse "\n")

/-! ## Full State Module Generation -/

/-- Generate complete state module -/
def genStateModule (contract : ContractDef) : String :=
  let name := contract.name.name
  joinLines [
    s!"import Lab.ERC20.Contracts.Interface",
    "",
    s!"/-!",
    s!"# {name} State",
    s!"",
    s!"Auto-generated state structure for {name} contract.",
    s!"-/",
    "",
    s!"namespace Generated.{name}",
    "",
    "open Lab.ERC20 (Address Amount Result MsgContext require)",
    "",
    "/-! ## State Structure -/",
    "",
    genStateStruct contract,
    "",
    "/-! ## Accessors -/",
    "",
    genAccessors contract,
    "",
    s!"end Generated.{name}"
  ]

/-! ## Main Entry Point -/

/-- Generate state module from source file -/
def generateState (source : SourceFile) : List (String × String) :=
  source.contracts.map fun c =>
    let moduleName := s!"Generated/{c.name.name}/State.lean"
    let content := genStateModule c
    (moduleName, content)

end Translator.Generator
