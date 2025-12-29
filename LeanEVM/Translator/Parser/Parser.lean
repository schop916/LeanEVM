import Translator.Parser.AST
import Translator.Parser.Lexer

/-!
# Solidity Parser

Parses tokenized Solidity source into AST.

## Supported Grammar (v0.1)

```
contract    ::= 'contract' IDENT '{' member* '}'
member      ::= stateVar | function | constructor
stateVar    ::= type visibility? IDENT ';'
function    ::= 'function' IDENT '(' params ')' visibility mutability 'returns' '(' params ')' '{' stmt* '}'
stmt        ::= require | assign | if | return | varDecl
require     ::= 'require' '(' expr (',' STRING)? ')' ';'
```
-/

namespace Translator.Parser

/-! ## Parser State -/

/-- Parser error -/
structure ParseError where
  message : String
  pos : Position
deriving Repr, Inhabited

instance : ToString ParseError where
  toString e := s!"{e.pos.line}:{e.pos.column}: {e.message}"

/-- Parser state -/
structure ParserState where
  tokens : Array Token
  pos : Nat := 0
deriving Repr, Inhabited

/-- Parser result -/
abbrev ParseResult (α : Type) := Except ParseError α

/-- Parser monad -/
abbrev Parser (α : Type) := ParserState → ParseResult (α × ParserState)

namespace Parser

/-- Run parser -/
def run {α : Type} (p : Parser α) (tokens : Array Token) : ParseResult α := do
  let (a, _) ← p { tokens := tokens }
  pure a

/-- Current token -/
def current (s : ParserState) : Token :=
  s.tokens.getD s.pos { kind := .eof, pos := { line := 0, column := 0 } }

/-- Peek at current token kind -/
def peek (s : ParserState) : TokenKind :=
  (current s).kind

/-- Current position -/
def currentPos (s : ParserState) : Position :=
  (current s).pos

/-- Advance to next token -/
def advance : Parser Unit := fun s =>
  .ok ((), { s with pos := s.pos + 1 })

/-- Check if at end -/
def atEnd (s : ParserState) : Bool :=
  match peek s with
  | .eof => true
  | _ => false

/-- Error at current position -/
def error {α : Type} (msg : String) : Parser α := fun s =>
  .error { message := msg, pos := currentPos s }

/-- Expect specific token -/
def expect (kind : TokenKind) : Parser Unit := fun s =>
  if peek s == kind then
    .ok ((), { s with pos := s.pos + 1 })
  else
    .error { message := s!"expected {kind}, got {peek s}", pos := currentPos s }

/-- Try to consume token, return true if successful -/
def tryConsume (kind : TokenKind) : Parser Bool := fun s =>
  if peek s == kind then
    .ok (true, { s with pos := s.pos + 1 })
  else
    .ok (false, s)

/-- Get identifier name -/
def ident : Parser Ident := fun s =>
  match peek s with
  | .ident name => .ok ({ name := name }, { s with pos := s.pos + 1 })
  | other => .error { message := s!"expected identifier, got {other}", pos := currentPos s }

/-- Pure value -/
def pure {α : Type} (a : α) : Parser α := fun s => .ok (a, s)

/-- Bind -/
def bind {α β : Type} (p : Parser α) (f : α → Parser β) : Parser β := fun s => do
  let (a, s') ← p s
  f a s'

instance : Monad Parser where
  pure := @Parser.pure
  bind := @Parser.bind

/-- Alternative -/
def orElse {α : Type} (p : Parser α) (q : Unit → Parser α) : Parser α := fun s =>
  match p s with
  | .ok result => .ok result
  | .error _ => q () s

instance {α : Type} : OrElse (Parser α) where
  orElse := Parser.orElse

/-- Many (zero or more) -/
partial def many {α : Type} (p : Parser α) : Parser (List α) := fun s =>
  match p s with
  | .ok (a, s') =>
    match many p s' with
    | .ok (as, s'') => .ok (a :: as, s'')
    | .error _ => .ok ([a], s')
  | .error _ => .ok ([], s)

/-- Separated by -/
partial def sepBy {α : Type} (p : Parser α) (sep : TokenKind) : Parser (List α) := fun s =>
  match p s with
  | .ok (a, s') =>
    let rec go (s : ParserState) (acc : List α) : ParseResult (List α × ParserState) :=
      if peek s == sep then
        match advance s with
        | .ok ((), s') =>
          match p s' with
          | .ok (a', s'') => go s'' (a' :: acc)
          | .error _ => .ok (acc.reverse, s)
        | .error e => .error e
      else
        .ok (acc.reverse, s)
    match go s' [a] with
    | .ok (as, s'') => .ok (as, s'')
    | .error e => .error e
  | .error _ => .ok ([], s)

/-- Optional -/
def optional {α : Type} (p : Parser α) : Parser (Option α) := fun s =>
  match p s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

end Parser

/-! ## Type Parsing -/

/-- Parse type modifiers (array brackets) -/
partial def parseTypeModifiers (t : SolType) : Parser SolType := fun s =>
  if Parser.peek s == .lbracket then
    match Parser.advance s with
    | .ok ((), s') =>
      match Parser.expect .rbracket s' with
      | .ok ((), s'') => parseTypeModifiers (.array t) s''
      | .error e => .error e
    | .error e => .error e
  else
    .ok (t, s)

/-- Parse Solidity type -/
partial def parseType : Parser SolType := fun s =>
  match Parser.peek s with
  | .uint256 =>
    let s' := { s with pos := s.pos + 1 }
    parseTypeModifiers .uint256 s'
  | .address_ =>
    let s' := { s with pos := s.pos + 1 }
    parseTypeModifiers .address s'
  | .bool_ =>
    let s' := { s with pos := s.pos + 1 }
    parseTypeModifiers .bool s'
  | .string_ =>
    let s' := { s with pos := s.pos + 1 }
    parseTypeModifiers .uint256 s'  -- treat string as uint256
  | .mapping =>
    match Parser.expect .mapping s with
    | .error e => .error e
    | .ok ((), s) =>
    match Parser.expect .lparen s with
    | .error e => .error e
    | .ok ((), s) =>
    match parseType s with
    | .error e => .error e
    | .ok (keyType, s) =>
    match Parser.expect .arrow s with
    | .error e => .error e
    | .ok ((), s) =>
    match parseType s with
    | .error e => .error e
    | .ok (valType, s) =>
    match Parser.expect .rparen s with
    | .error e => .error e
    | .ok ((), s) =>
    parseTypeModifiers (.mapping keyType valType) s
  | .ident name =>
    let s' := { s with pos := s.pos + 1 }
    parseTypeModifiers (.custom { name := name }) s'
  | other => .error { message := s!"expected type, got {other}", pos := Parser.currentPos s }

/-! ## Expression Parsing -/

mutual
/-- Parse primary expression -/
partial def parsePrimary : Parser Expr := fun s =>
  match Parser.peek s with
  | .intLit n => .ok (.intLit n, { s with pos := s.pos + 1 })
  | .hexLit n => .ok (.addrLit n, { s with pos := s.pos + 1 })
  | .true_ => .ok (.boolLit true, { s with pos := s.pos + 1 })
  | .false_ => .ok (.boolLit false, { s with pos := s.pos + 1 })
  | .stringLit str => .ok (.stringLit str, { s with pos := s.pos + 1 })
  | .ident "msg" =>
    let s' := { s with pos := s.pos + 1 }
    if Parser.peek s' == .dot then
      let s'' := { s' with pos := s'.pos + 1 }
      match Parser.peek s'' with
      | .ident "sender" => .ok (.msgSender, { s'' with pos := s''.pos + 1 })
      | .ident "value" => .ok (.msgValue, { s'' with pos := s''.pos + 1 })
      | _ => .ok (.ident { name := "msg" }, s')
    else
      .ok (.ident { name := "msg" }, s')
  | .ident name => .ok (.ident { name := name }, { s with pos := s.pos + 1 })
  | .lparen =>
    let s' := { s with pos := s.pos + 1 }
    match parseExpr s' with
    | .error e => .error e
    | .ok (e, s'') =>
      match Parser.expect .rparen s'' with
      | .error e => .error e
      | .ok ((), s''') => .ok (e, s''')
  | .bang =>
    let s' := { s with pos := s.pos + 1 }
    match parsePrimary s' with
    | .error e => .error e
    | .ok (e, s'') => .ok (.unaryOp .not e, s'')
  | other => .error { message := s!"expected expression, got {other}", pos := Parser.currentPos s }

/-- Parse postfix expressions (calls, member access, indexing) -/
partial def parsePostfix (e : Expr) : Parser Expr := fun s =>
  match Parser.peek s with
  | .dot =>
    let s' := { s with pos := s.pos + 1 }
    match Parser.ident s' with
    | .ok (name, s'') => parsePostfix (.member e name) s''
    | .error err => .error err
  | .lbracket =>
    let s' := { s with pos := s.pos + 1 }
    match parseExpr s' with
    | .error err => .error err
    | .ok (idx, s'') =>
      match Parser.expect .rbracket s'' with
      | .error err => .error err
      | .ok ((), s''') => parsePostfix (.index e idx) s'''
  | .lparen =>
    let s' := { s with pos := s.pos + 1 }
    match Parser.sepBy parseExpr .comma s' with
    | .error err => .error err
    | .ok (args, s'') =>
      match Parser.expect .rparen s'' with
      | .error err => .error err
      | .ok ((), s''') => parsePostfix (.call e args) s'''
  | _ => .ok (e, s)

/-- Parse unary expression -/
partial def parseUnary : Parser Expr := fun s =>
  match parsePrimary s with
  | .error e => .error e
  | .ok (e, s') => parsePostfix e s'

/-- Parse multiplicative expression -/
partial def parseMul : Parser Expr := fun s =>
  match parseUnary s with
  | .error e => .error e
  | .ok (left, s') => parseMulRest left s'
where
  parseMulRest (left : Expr) : Parser Expr := fun s =>
    match Parser.peek s with
    | .star =>
      let s' := { s with pos := s.pos + 1 }
      match parseUnary s' with
      | .error e => .error e
      | .ok (right, s'') => parseMulRest (.binOp .mul left right) s''
    | .slash =>
      let s' := { s with pos := s.pos + 1 }
      match parseUnary s' with
      | .error e => .error e
      | .ok (right, s'') => parseMulRest (.binOp .div left right) s''
    | .percent =>
      let s' := { s with pos := s.pos + 1 }
      match parseUnary s' with
      | .error e => .error e
      | .ok (right, s'') => parseMulRest (.binOp .mod left right) s''
    | _ => .ok (left, s)

/-- Parse additive expression -/
partial def parseAdd : Parser Expr := fun s =>
  match parseMul s with
  | .error e => .error e
  | .ok (left, s') => parseAddRest left s'
where
  parseAddRest (left : Expr) : Parser Expr := fun s =>
    match Parser.peek s with
    | .plus =>
      let s' := { s with pos := s.pos + 1 }
      match parseMul s' with
      | .error e => .error e
      | .ok (right, s'') => parseAddRest (.binOp .add left right) s''
    | .minus =>
      let s' := { s with pos := s.pos + 1 }
      match parseMul s' with
      | .error e => .error e
      | .ok (right, s'') => parseAddRest (.binOp .sub left right) s''
    | _ => .ok (left, s)

/-- Parse comparison expression -/
partial def parseCompare : Parser Expr := fun s =>
  match parseAdd s with
  | .error e => .error e
  | .ok (left, s') => parseCompareOp left s'
where
  parseCompareOp (left : Expr) : Parser Expr := fun s =>
    match Parser.peek s with
    | .eq => parseBinOp .eq left s
    | .neq => parseBinOp .ne left s
    | .lt => parseBinOp .lt left s
    | .le => parseBinOp .le left s
    | .gt => parseBinOp .gt left s
    | .ge => parseBinOp .ge left s
    | _ => .ok (left, s)
  parseBinOp (op : BinOp) (left : Expr) : Parser Expr := fun s =>
    let s' := { s with pos := s.pos + 1 }
    match parseAdd s' with
    | .error e => .error e
    | .ok (right, s'') => .ok (.binOp op left right, s'')

/-- Parse logical AND expression -/
partial def parseAnd : Parser Expr := fun s =>
  match parseCompare s with
  | .error e => .error e
  | .ok (left, s') => parseAndRest left s'
where
  parseAndRest (left : Expr) : Parser Expr := fun s =>
    if Parser.peek s == .ampAmp then
      let s' := { s with pos := s.pos + 1 }
      match parseCompare s' with
      | .error e => .error e
      | .ok (right, s'') => parseAndRest (.binOp .and left right) s''
    else
      .ok (left, s)

/-- Parse logical OR expression -/
partial def parseOr : Parser Expr := fun s =>
  match parseAnd s with
  | .error e => .error e
  | .ok (left, s') => parseOrRest left s'
where
  parseOrRest (left : Expr) : Parser Expr := fun s =>
    if Parser.peek s == .pipePipe then
      let s' := { s with pos := s.pos + 1 }
      match parseAnd s' with
      | .error e => .error e
      | .ok (right, s'') => parseOrRest (.binOp .or left right) s''
    else
      .ok (left, s)

/-- Parse ternary expression -/
partial def parseTernary : Parser Expr := fun s =>
  match parseOr s with
  | .error e => .error e
  | .ok (cond, s') =>
    if Parser.peek s' == .question then
      let s'' := { s' with pos := s'.pos + 1 }
      match parseExpr s'' with
      | .error e => .error e
      | .ok (thenExpr, s''') =>
        match Parser.expect .colon s''' with
        | .error e => .error e
        | .ok ((), s4) =>
          match parseExpr s4 with
          | .error e => .error e
          | .ok (elseExpr, s5) => .ok (.ternary cond thenExpr elseExpr, s5)
    else
      .ok (cond, s')

/-- Parse full expression -/
partial def parseExpr : Parser Expr := parseTernary

end

/-! ## Statement Parsing -/

/-- Parse require statement -/
def parseRequire : Parser Stmt := do
  Parser.expect .require_
  Parser.expect .lparen
  let cond ← parseExpr
  let msg ← Parser.optional do
    Parser.expect .comma
    fun s => match Parser.peek s with
      | .stringLit str => .ok (str, { s with pos := s.pos + 1 })
      | _ => Parser.error "expected string literal" s
  Parser.expect .rparen
  Parser.expect .semi
  Parser.pure (.require cond msg)

/-- Parse assignment or expression statement -/
def parseAssignOrExpr : Parser Stmt := do
  let lhs ← parseExpr
  let kind ← fun s => .ok (Parser.peek s, s)
  match kind with
  | .assign => do
    Parser.advance
    let rhs ← parseExpr
    Parser.expect .semi
    Parser.pure (.assign lhs rhs)
  | .plusAssign => do
    Parser.advance
    let rhs ← parseExpr
    Parser.expect .semi
    Parser.pure (.assignOp .add lhs rhs)
  | .minusAssign => do
    Parser.advance
    let rhs ← parseExpr
    Parser.expect .semi
    Parser.pure (.assignOp .sub lhs rhs)
  | .starAssign => do
    Parser.advance
    let rhs ← parseExpr
    Parser.expect .semi
    Parser.pure (.assignOp .mul lhs rhs)
  | .slashAssign => do
    Parser.advance
    let rhs ← parseExpr
    Parser.expect .semi
    Parser.pure (.assignOp .div lhs rhs)
  | .semi => do
    Parser.advance
    Parser.pure (.exprStmt lhs)
  | _ => Parser.error s!"expected assignment or semicolon, got {kind}"

/-- Parse return statement -/
def parseReturn : Parser Stmt := do
  Parser.expect .return_
  let kind ← fun s => .ok (Parser.peek s, s)
  if kind == .semi then do
    Parser.advance
    Parser.pure (.returnStmt none)
  else do
    let e ← parseExpr
    Parser.expect .semi
    Parser.pure (.returnStmt (some e))

/-- Parse variable declaration -/
def parseVarDecl : Parser Stmt := do
  let ty ← parseType
  let name ← Parser.ident
  let hasInit ← Parser.tryConsume .assign
  if hasInit then do
    let initVal ← parseExpr
    Parser.expect .semi
    Parser.pure (.varDecl name ty (some initVal))
  else do
    Parser.expect .semi
    Parser.pure (.varDecl name ty none)

-- Mutual block for parseIf and parseStmt since they reference each other
mutual

/-- Parse if statement -/
partial def parseIf : Parser Stmt := fun s =>
  match Parser.expect .if_ s with
  | .error e => .error e
  | .ok ((), s1) =>
    match Parser.expect .lparen s1 with
    | .error e => .error e
    | .ok ((), s2) =>
      match parseExpr s2 with
      | .error e => .error e
      | .ok (cond, s3) =>
        match Parser.expect .rparen s3 with
        | .error e => .error e
        | .ok ((), s4) =>
          match Parser.expect .lbrace s4 with
          | .error e => .error e
          | .ok ((), s5) =>
            match Parser.many parseStmt s5 with
            | .error e => .error e
            | .ok (thenStmts, s6) =>
              match Parser.expect .rbrace s6 with
              | .error e => .error e
              | .ok ((), s7) =>
                match Parser.tryConsume .else_ s7 with
                | .error e => .error e
                | .ok (hasElse, s8) =>
                  if hasElse then
                    match Parser.expect .lbrace s8 with
                    | .error e => .error e
                    | .ok ((), s9) =>
                      match Parser.many parseStmt s9 with
                      | .error e => .error e
                      | .ok (elseStmts, s10) =>
                        match Parser.expect .rbrace s10 with
                        | .error e => .error e
                        | .ok ((), s11) =>
                          .ok (.ifStmt cond thenStmts (some elseStmts), s11)
                  else
                    .ok (.ifStmt cond thenStmts none, s8)

/-- Parse single statement -/
partial def parseStmt : Parser Stmt := fun s =>
  match Parser.peek s with
  | .require_ => parseRequire s
  | .if_ => parseIf s
  | .return_ => parseReturn s
  | .uint256 | .address_ | .bool_ | .mapping => parseVarDecl s
  | _ => parseAssignOrExpr s

end

/-! ## Function Parsing -/

/-- Parse function parameter -/
def parseParam : Parser Param := do
  let ty ← parseType
  -- Skip memory/storage/calldata
  let _ ← Parser.tryConsume .memory
  let _ ← Parser.tryConsume .storage
  let _ ← Parser.tryConsume .calldata
  let name ← Parser.ident
  Parser.pure { name := name, type := ty }

/-- Parse visibility -/
def parseVisibility : Parser Visibility := fun s =>
  match Parser.peek s with
  | .public_ => .ok (.public_, { s with pos := s.pos + 1 })
  | .private_ => .ok (.private_, { s with pos := s.pos + 1 })
  | .internal => .ok (.internal, { s with pos := s.pos + 1 })
  | .external => .ok (.external, { s with pos := s.pos + 1 })
  | _ => .ok (.internal, s)  -- default to internal

/-- Parse mutability -/
def parseMutability : Parser Mutability := fun s =>
  match Parser.peek s with
  | .view => .ok (.view, { s with pos := s.pos + 1 })
  | .pure_ => .ok (.pure_, { s with pos := s.pos + 1 })
  | .payable => .ok (.payable, { s with pos := s.pos + 1 })
  | _ => .ok (.nonpayable, s)  -- default

/-- Parse function definition -/
def parseFunction : Parser FunctionDef := do
  Parser.expect .function_
  let name ← Parser.ident
  Parser.expect .lparen
  let params ← Parser.sepBy parseParam .comma
  Parser.expect .rparen
  let vis ← parseVisibility
  let mutab ← parseMutability
  -- Parse returns if present
  let rets ← Parser.optional do
    Parser.expect .returns
    Parser.expect .lparen
    let retParams ← Parser.sepBy parseParam .comma
    Parser.expect .rparen
    Parser.pure retParams
  Parser.expect .lbrace
  let body ← Parser.many parseStmt
  Parser.expect .rbrace
  Parser.pure {
    name := name
    params := params
    returns := rets.getD []
    visibility := vis
    mutability := mutab
    body := body
  }

/-! ## Contract Parsing -/

/-- Parse state variable -/
def parseStateVar : Parser StateVar := do
  let ty ← parseType
  let vis ← parseVisibility
  let name ← Parser.ident
  let initVal ← Parser.optional do
    Parser.expect .assign
    parseExpr
  Parser.expect .semi
  Parser.pure {
    name := name
    type := ty
    visibility := vis
    initialValue := initVal
  }

/-- Parse constructor -/
def parseConstructor : Parser (List Param × List Stmt) := do
  Parser.expect .constructor_
  Parser.expect .lparen
  let params ← Parser.sepBy parseParam .comma
  Parser.expect .rparen
  -- Skip visibility/payable
  let _ ← parseVisibility
  let _ ← parseMutability
  Parser.expect .lbrace
  let body ← Parser.many parseStmt
  Parser.expect .rbrace
  Parser.pure (params, body)

/-- Parse contract member -/
def parseMember : Parser ContractMember := fun s =>
  match Parser.peek s with
  | .function_ => (parseFunction >>= fun f => Parser.pure (.function f)) s
  | .constructor_ => (parseConstructor >>= fun (ps, ss) => Parser.pure (.constructor ps ss)) s
  | _ => (parseStateVar >>= fun sv => Parser.pure (.stateVar sv)) s

/-- Parse contract definition -/
def parseContract : Parser ContractDef := do
  Parser.expect .contract
  let name ← Parser.ident
  Parser.expect .lbrace
  let members ← Parser.many parseMember
  Parser.expect .rbrace
  Parser.pure { name := name, members := members }

/-- Parse source file -/
def parseSourceFile : Parser SourceFile := do
  -- Skip pragmas and imports for now
  let contracts ← Parser.many parseContract
  Parser.pure { pragmas := [], imports := [], contracts := contracts }

/-! ## Public API -/

/-- Parse Solidity source code -/
def parse (source : String) : ParseResult SourceFile :=
  let tokens := tokenize source
  Parser.run parseSourceFile tokens.toArray

end Translator.Parser
