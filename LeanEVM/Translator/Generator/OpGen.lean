import Translator.Parser.AST
import Translator.Generator.StateGen

/-!
# Operation Generator

Translates Solidity function bodies to Lean Result monad operations.

## Translation Rules

| Solidity | Lean |
|----------|------|
| `require(cond, msg)` | `require cond msg` |
| `a = b` | `let s := { s with a := b }` |
| `mapping[k] = v` | `let s := s.setField k v` |
| `if (c) { ... }` | `if c then ... else ...` |
| `return x` | `pure (s, x)` |
-/

namespace Translator.Generator

open Translator.Parser

/-! ## Expression Translation -/

/-- Translate binary operator -/
def binOpToLean : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .eq => "="
  | .ne => "≠"
  | .lt => "<"
  | .le => "≤"
  | .gt => ">"
  | .ge => "≥"
  | .and => "&&"
  | .or => "||"

/-- Escape identifier if it's a Lean keyword (inline version for exprToLean) -/
def escapeIdentExpr (name : String) : String :=
  let keywords := ["to", "in", "do", "if", "then", "else", "match", "with", "where", "let", "have",
   "fun", "forall", "import", "open", "variable", "def", "theorem", "lemma", "example",
   "structure", "class", "instance", "namespace", "section", "end", "return", "for"]
  if keywords.contains name then s!"{name}_" else name

/-- Translate expression to Lean, with locals set for non-state identifiers -/
partial def exprToLean (stateVar : String := "s") (locals : List String := []) : Expr → String
  | .intLit n => s!"{n}"
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .addrLit n => s!"⟨{n}⟩"
  | .stringLit str => s!"\"{str}\""
  | .ident id =>
    -- Escape the identifier and check if it's a local
    let escaped := escapeIdentExpr id.name
    if locals.contains escaped then escaped
    else s!"{stateVar}.{id.name}"
  | .member e field =>
    let base := exprToLean stateVar locals e
    s!"{base}.{field.name}"
  | .index e idx =>
    let base := exprToLean stateVar locals e
    let idxStr := exprToLean stateVar locals idx
    s!"({base} {idxStr})"
  | .call fn args =>
    let fnStr := match fn with
      | .ident id => id.name
      | _ => exprToLean stateVar locals fn
    let argsStr := ", ".intercalate (args.map (exprToLean stateVar locals))
    s!"{fnStr} {argsStr}"
  | .binOp op l r =>
    let lStr := exprToLean stateVar locals l
    let rStr := exprToLean stateVar locals r
    let opStr := binOpToLean op
    s!"({lStr} {opStr} {rStr})"
  | .unaryOp .not e =>
    let eStr := exprToLean stateVar locals e
    s!"(!{eStr})"
  | .unaryOp .neg e =>
    let eStr := exprToLean stateVar locals e
    s!"(-{eStr})"
  | .ternary c t e =>
    let cStr := exprToLean stateVar locals c
    let tStr := exprToLean stateVar locals t
    let eStr := exprToLean stateVar locals e
    s!"(if {cStr} then {tStr} else {eStr})"
  | .msgSender => "msg.sender"
  | .msgValue => "msg.value"

/-! ## Statement Translation -/

/-- Analyze expression to extract state variable assignment -/
def analyzeAssign (lhs : Expr) : Option (String × Option Expr) :=
  match lhs with
  | .ident id => some (id.name, none)
  | .member (.ident base) field =>
    if base.name == "s" then some (field.name, none)
    else some (s!"{base.name}.{field.name}", none)
  | .index (.ident id) key => some (id.name, some key)
  | .index (.member _ field) key => some (field.name, some key)
  | _ => none

/-- Translate assignment to Lean -/
def assignToLean (stateVar : String) (locals : List String) (lhs : Expr) (rhs : Expr) : String :=
  let rhsStr := exprToLean stateVar locals rhs
  match analyzeAssign lhs with
  | some (field, none) =>
    "let " ++ stateVar ++ " := { " ++ stateVar ++ " with " ++ field ++ " := " ++ rhsStr ++ " }"
  | some (field, some key) =>
    let keyStr := exprToLean stateVar locals key
    "let " ++ stateVar ++ " := { " ++ stateVar ++ " with " ++ field ++ " := fun k => if k = " ++ keyStr ++ " then " ++ rhsStr ++ " else " ++ stateVar ++ "." ++ field ++ " k }"
  | none =>
    -- Fallback: treat as simple assignment
    "let " ++ stateVar ++ " := { " ++ stateVar ++ " with " ++ exprToLean stateVar locals lhs ++ " := " ++ rhsStr ++ " }"

/-- Translate compound assignment (+=, -=, etc.) -/
def compoundAssignToLean (stateVar : String) (locals : List String) (op : BinOp) (lhs : Expr) (rhs : Expr) : String :=
  let rhsStr := exprToLean stateVar locals rhs
  let opStr := binOpToLean op
  match analyzeAssign lhs with
  | some (field, none) =>
    "let " ++ stateVar ++ " := { " ++ stateVar ++ " with " ++ field ++ " := " ++ stateVar ++ "." ++ field ++ " " ++ opStr ++ " " ++ rhsStr ++ " }"
  | some (field, some key) =>
    let keyStr := exprToLean stateVar locals key
    "let " ++ stateVar ++ " := { " ++ stateVar ++ " with " ++ field ++ " := fun k => if k = " ++ keyStr ++ " then " ++ stateVar ++ "." ++ field ++ " k " ++ opStr ++ " " ++ rhsStr ++ " else " ++ stateVar ++ "." ++ field ++ " k }"
  | none =>
    let lhsStr := exprToLean stateVar locals lhs
    "let " ++ stateVar ++ " := { " ++ stateVar ++ " with " ++ lhsStr ++ " := " ++ lhsStr ++ " " ++ opStr ++ " " ++ rhsStr ++ " }"

/-- Translate multiple statements, tracking locals -/
partial def stmtsToLean (stateVar : String) (locals : List String) (indentLevel : Nat) (stmts : List Stmt) : String :=
  let (_, lines) := stmts.foldl (fun (locs, acc) stmt =>
    let line := stmtToLean stateVar locs indentLevel stmt
    let newLocs := match stmt with
      | .varDecl name _ _ => name.name :: locs
      | _ => locs
    (newLocs, acc ++ [line])
  ) (locals, [])
  joinLines lines
where
  /-- Translate single statement to Lean -/
  stmtToLean (stateVar : String) (locals : List String) (indentLevel : Nat) : Stmt → String
    | .require cond msg =>
      let condStr := exprToLean stateVar locals cond
      let msgStr := msg.getD "error"
      indent indentLevel s!"require ({condStr}) \"{msgStr}\""
    | .assign lhs rhs =>
      indent indentLevel (assignToLean stateVar locals lhs rhs)
    | .assignOp op lhs rhs =>
      indent indentLevel (compoundAssignToLean stateVar locals op lhs rhs)
    | .ifStmt cond thenStmts elseStmts =>
      let condStr := exprToLean stateVar locals cond
      let thenBlock := stmtsToLean stateVar locals (indentLevel + 1) thenStmts
      match elseStmts with
      | some elseBody =>
        let elseBlock := stmtsToLean stateVar locals (indentLevel + 1) elseBody
        joinLines [
          indent indentLevel s!"if {condStr} then",
          thenBlock,
          indent indentLevel "else",
          elseBlock
        ]
      | none =>
        joinLines [
          indent indentLevel s!"if {condStr} then",
          thenBlock
        ]
    | .returnStmt (some e) =>
      let eStr := exprToLean stateVar locals e
      indent indentLevel s!"pure ({stateVar}, {eStr})"
    | .returnStmt none =>
      indent indentLevel s!"pure {stateVar}"
    | .varDecl name ty init =>
      let tyStr := solTypeToLean ty
      match init with
      | some e =>
        let eStr := exprToLean stateVar locals e
        indent indentLevel s!"let {name.name} : {tyStr} := {eStr}"
      | none =>
        indent indentLevel s!"let {name.name} : {tyStr} := {solTypeDefault ty}"
    | .exprStmt e =>
      indent indentLevel s!"let _ := {exprToLean stateVar locals e}"

/-! ## Function Translation -/

/-- Lean keywords that need escaping -/
def leanKeywords : List String :=
  ["to", "in", "do", "if", "then", "else", "match", "with", "where", "let", "have",
   "fun", "forall", "import", "open", "variable", "def", "theorem", "lemma", "example",
   "structure", "class", "instance", "namespace", "section", "end", "return", "for"]

/-- Escape identifier if it's a Lean keyword -/
def escapeIdent (name : String) : String :=
  if leanKeywords.contains name then s!"{name}_" else name

/-- Generate function parameter list -/
def genParams (params : List Param) : String :=
  let paramStrs := params.map fun p =>
    s!"({escapeIdent p.name.name} : {solTypeToLean p.type})"
  " ".intercalate paramStrs

/-- Generate function return type -/
def genReturnType (stateName : String) (returns : List Param) : String :=
  match returns with
  | [] => s!"Result {stateName}"
  | [r] => s!"Result ({stateName} × {solTypeToLean r.type})"
  | rs =>
    let types := rs.map fun r => solTypeToLean r.type
    let tupleType := " × ".intercalate types
    s!"Result ({stateName} × {tupleType})"

/-- Check if function body ends with return -/
def endsWithReturn : List Stmt → Bool
  | [] => false
  | [.returnStmt _] => true
  | [.ifStmt _ thenB (some elseB)] => endsWithReturn thenB && endsWithReturn elseB
  | _ :: rest => endsWithReturn rest

/-- Add implicit return if needed -/
def addImplicitReturn (stmts : List Stmt) : List Stmt :=
  if endsWithReturn stmts then stmts
  else stmts ++ [.returnStmt none]

/-- Generate function implementation -/
def genFunction (stateName : String) (fn : FunctionDef) : String :=
  let params := genParams fn.params
  let retType := genReturnType stateName fn.returns
  let stmts := addImplicitReturn fn.body
  -- Extract parameter names as initial locals (escaped)
  let paramNames := fn.params.map fun p => escapeIdent p.name.name
  let body := stmtsToLean "s" paramNames 1 stmts

  let mutNote := match fn.mutability with
    | .view => " (view function)"
    | .pure_ => " (pure function)"
    | _ => ""

  joinLines [
    s!"/-- {fn.name.name}{mutNote} -/",
    s!"def {fn.name.name} (s : {stateName}) (msg : MsgContext)",
    s!"    {params} : {retType} := do",
    body
  ]

/-! ## Full Operations Module Generation -/

/-- Generate operations module -/
def genOpsModule (contract : ContractDef) : String :=
  let name := contract.name.name
  let stateName := s!"{name}State"
  let functions := contract.functions.filter (·.visibility != .private_)
  let fnDefs := functions.map (genFunction stateName)

  joinLines [
    s!"import Generated.{name}.State",
    "",
    s!"/-!",
    s!"# {name} Operations",
    s!"",
    s!"Auto-generated operations for {name} contract.",
    s!"-/",
    "",
    s!"namespace Generated.{name}",
    "",
    "open Lab.ERC20 (Address Amount Result MsgContext require)",
    "",
    "/-! ## Operations -/",
    "",
    joinLines (fnDefs.intersperse "\n"),
    "",
    s!"end Generated.{name}"
  ]

/-! ## Main Entry Point -/

/-- Generate operations module from source file -/
def generateOps (source : SourceFile) : List (String × String) :=
  source.contracts.map fun c =>
    let moduleName := s!"Generated/{c.name.name}/Operations.lean"
    let content := genOpsModule c
    (moduleName, content)

end Translator.Generator
