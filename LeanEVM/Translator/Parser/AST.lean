/-!
# Solidity Abstract Syntax Tree

AST types for representing Solidity contracts.
Focused on the subset needed for verification:
- State variables: uint256, address, bool, mapping
- Functions: public, external, view
- Control flow: require, if/else, return

## Design Notes

- Positions track source locations for error messages
- Types are simplified (uint256 only, no smaller uints)
- Modifiers are inlined (no modifier blocks)
-/

namespace Translator.Parser

/-! ## Source Positions -/

/-- Source position for error reporting -/
structure Position where
  line : Nat
  column : Nat
deriving Repr, DecidableEq, Inhabited

/-- Source span (start to end) -/
structure Span where
  start : Position
  stop : Position
deriving Repr, DecidableEq

/-- Attach span to any AST node -/
structure Located (α : Type) where
  span : Span
  val : α
deriving Repr

/-! ## Identifiers -/

/-- Solidity identifier -/
structure Ident where
  name : String
deriving Repr, DecidableEq, Hashable

instance : ToString Ident where
  toString i := i.name

/-! ## Types -/

/-- Solidity types (simplified subset) -/
inductive SolType
  | uint256    : SolType
  | address    : SolType
  | bool       : SolType
  | mapping    : SolType → SolType → SolType  -- mapping(K => V)
  | array      : SolType → SolType            -- T[] (dynamic array)
  | custom     : Ident → SolType              -- user-defined type
deriving Repr, DecidableEq, Inhabited

namespace SolType

/-- Pretty print type -/
def toString : SolType → String
  | uint256 => "uint256"
  | address => "address"
  | bool => "bool"
  | mapping k v => s!"mapping({k.toString} => {v.toString})"
  | array t => s!"{t.toString}[]"
  | custom id => id.name

instance : ToString SolType where
  toString := SolType.toString

/-- Check if type is a value type (not mapping/array) -/
def isValueType : SolType → Bool
  | uint256 => true
  | address => true
  | bool => true
  | mapping _ _ => false
  | array _ => false
  | custom _ => true  -- assume custom types are value types

end SolType

/-! ## Expressions -/

/-- Binary operators -/
inductive BinOp
  | add | sub | mul | div | mod  -- arithmetic
  | eq | ne | lt | le | gt | ge  -- comparison
  | and | or                      -- logical
deriving Repr, DecidableEq

namespace BinOp

def toString : BinOp → String
  | add => "+" | sub => "-" | mul => "*" | div => "/" | mod => "%"
  | eq => "==" | ne => "!=" | lt => "<" | le => "<=" | gt => ">" | ge => ">="
  | and => "&&" | or => "||"

instance : ToString BinOp where
  toString := BinOp.toString

end BinOp

/-- Unary operators -/
inductive UnaryOp
  | not   -- logical not
  | neg   -- arithmetic negation (rarely used with uint)
deriving Repr, DecidableEq

/-- Expressions -/
inductive Expr
  | intLit   : Nat → Expr                         -- integer literal
  | boolLit  : Bool → Expr                        -- true/false
  | addrLit  : Nat → Expr                         -- address literal (0x...)
  | stringLit : String → Expr                     -- string literal
  | ident    : Ident → Expr                       -- variable reference
  | member   : Expr → Ident → Expr                -- expr.field
  | index    : Expr → Expr → Expr                 -- expr[index]
  | call     : Expr → List Expr → Expr            -- func(args)
  | binOp    : BinOp → Expr → Expr → Expr         -- a op b
  | unaryOp  : UnaryOp → Expr → Expr              -- op a
  | ternary  : Expr → Expr → Expr → Expr          -- cond ? then : else
  | msgSender : Expr                              -- msg.sender
  | msgValue  : Expr                              -- msg.value
deriving Repr, Inhabited

/-! ## Statements -/

/-- Statement in function body -/
inductive Stmt
  | require    : Expr → Option String → Stmt           -- require(cond, "msg")
  | assign     : Expr → Expr → Stmt                    -- lhs = rhs
  | assignOp   : BinOp → Expr → Expr → Stmt           -- lhs += rhs (compound)
  | ifStmt     : Expr → List Stmt → Option (List Stmt) → Stmt  -- if/else
  | returnStmt : Option Expr → Stmt                    -- return expr?
  | varDecl    : Ident → SolType → Option Expr → Stmt  -- Type name = init
  | exprStmt   : Expr → Stmt                           -- expr; (for calls)
deriving Repr, Inhabited

/-! ## Function Definitions -/

/-- Function visibility -/
inductive Visibility
  | public_
  | external
  | internal
  | private_
deriving Repr, DecidableEq

/-- Function mutability -/
inductive Mutability
  | pure_      -- no state read/write
  | view       -- read only
  | payable    -- can receive ETH
  | nonpayable -- default: can modify state
deriving Repr, DecidableEq

/-- Function parameter -/
structure Param where
  name : Ident
  type : SolType
deriving Repr

/-- Function definition -/
structure FunctionDef where
  name : Ident
  params : List Param
  returns : List Param
  visibility : Visibility
  mutability : Mutability
  body : List Stmt
deriving Repr

/-! ## State Variables -/

/-- State variable declaration -/
structure StateVar where
  name : Ident
  type : SolType
  visibility : Visibility  -- public generates getter
  initialValue : Option Expr
deriving Repr

/-! ## Modifiers -/

/-- Modifier invocation (we inline these) -/
structure ModifierInvocation where
  name : Ident
  args : List Expr
deriving Repr

/-! ## Contract Definition -/

/-- Contract member -/
inductive ContractMember
  | stateVar : StateVar → ContractMember
  | function : FunctionDef → ContractMember
  | constructor : List Param → List Stmt → ContractMember
deriving Repr

/-- Contract definition -/
structure ContractDef where
  name : Ident
  members : List ContractMember
deriving Repr

/-! ## Source File -/

/-- Top-level source file -/
structure SourceFile where
  pragmas : List String           -- pragma solidity ^0.8.0
  imports : List String           -- import statements
  contracts : List ContractDef    -- contract definitions
deriving Repr

/-! ## Utilities -/

namespace ContractDef

/-- Get all state variables -/
def stateVars (c : ContractDef) : List StateVar :=
  c.members.filterMap fun
    | .stateVar sv => some sv
    | _ => none

/-- Get all functions -/
def functions (c : ContractDef) : List FunctionDef :=
  c.members.filterMap fun
    | .function f => some f
    | _ => none

/-- Get constructor if present -/
def constructor (c : ContractDef) : Option (List Param × List Stmt) :=
  c.members.findSome? fun
    | .constructor params body => some (params, body)
    | _ => none

end ContractDef

namespace FunctionDef

/-- Check if function modifies state -/
def modifiesState (f : FunctionDef) : Bool :=
  f.mutability == .nonpayable || f.mutability == .payable

/-- Check if function is a view/pure function -/
def isReadOnly (f : FunctionDef) : Bool :=
  f.mutability == .view || f.mutability == .pure_

end FunctionDef

end Translator.Parser
