import Std.Data.HashMap
import Translator.Parser.AST

/-!
# Solidity Lexer

Tokenizes Solidity source code into a stream of tokens.
-/

namespace Translator.Parser

/-! ## Tokens -/

/-- Token types -/
inductive TokenKind
  -- Keywords
  | contract | function_ | modifier | event_ | struct_ | enum_
  | mapping | public_ | private_ | internal | external
  | view | pure_ | payable | memory | storage | calldata
  | returns | return_ | if_ | else_ | for_ | while_
  | require_ | revert | assert_ | emit
  | constructor_ | true_ | false_
  | uint256 | address_ | bool_ | string_
  -- Operators
  | plus | minus | star | slash | percent
  | eq | neq | lt | le | gt | ge
  | assign | plusAssign | minusAssign | starAssign | slashAssign
  | ampAmp | pipePipe | bang
  | amp | pipe | caret | tilde
  | ltLt | gtGt
  -- Punctuation
  | lparen | rparen | lbrace | rbrace | lbracket | rbracket
  | semi | comma | dot | arrow | question | colon
  -- Literals and identifiers
  | intLit (val : Nat)
  | hexLit (val : Nat)
  | stringLit (val : String)
  | ident (name : String)
  -- Special
  | eof
  | unknown (char : Char)
deriving Repr, DecidableEq

namespace TokenKind

def toString : TokenKind → String
  | contract => "contract" | function_ => "function" | modifier => "modifier"
  | event_ => "event" | struct_ => "struct" | enum_ => "enum"
  | mapping => "mapping" | public_ => "public" | private_ => "private"
  | internal => "internal" | external => "external"
  | view => "view" | pure_ => "pure" | payable => "payable"
  | memory => "memory" | storage => "storage" | calldata => "calldata"
  | returns => "returns" | return_ => "return"
  | if_ => "if" | else_ => "else" | for_ => "for" | while_ => "while"
  | require_ => "require" | revert => "revert" | assert_ => "assert" | emit => "emit"
  | constructor_ => "constructor" | true_ => "true" | false_ => "false"
  | uint256 => "uint256" | address_ => "address" | bool_ => "bool" | string_ => "string"
  | plus => "+" | minus => "-" | star => "*" | slash => "/" | percent => "%"
  | eq => "==" | neq => "!=" | lt => "<" | le => "<=" | gt => ">" | ge => ">="
  | assign => "=" | plusAssign => "+=" | minusAssign => "-=" | starAssign => "*=" | slashAssign => "/="
  | ampAmp => "&&" | pipePipe => "||" | bang => "!"
  | amp => "&" | pipe => "|" | caret => "^" | tilde => "~"
  | ltLt => "<<" | gtGt => ">>"
  | lparen => "(" | rparen => ")" | lbrace => "{" | rbrace => "}"
  | lbracket => "[" | rbracket => "]"
  | semi => ";" | comma => "," | dot => "." | arrow => "=>" | question => "?" | colon => ":"
  | intLit n => s!"{n}" | hexLit n => s!"0x{n}"
  | stringLit s => s!"\"{s}\"" | ident name => name
  | eof => "<eof>" | unknown c => s!"<unknown:{c}>"

instance : ToString TokenKind := ⟨TokenKind.toString⟩

end TokenKind

/-- Token with position -/
structure Token where
  kind : TokenKind
  pos : Position
deriving Repr

/-! ## Lexer State -/

structure LexerState where
  source : String
  pos : Nat := 0
  line : Nat := 1
  column : Nat := 1
deriving Repr

namespace LexerState

def fromString (s : String) : LexerState := { source := s }

def atEnd (l : LexerState) : Bool := l.pos >= l.source.length

def peek (l : LexerState) : Option Char := l.source.get? ⟨l.pos⟩

def peekNext (l : LexerState) : Option Char := l.source.get? ⟨l.pos + 1⟩

def advance (l : LexerState) : LexerState :=
  match l.peek with
  | none => l
  | some '\n' => { l with pos := l.pos + 1, line := l.line + 1, column := 1 }
  | some _ => { l with pos := l.pos + 1, column := l.column + 1 }

def currentPos (l : LexerState) : Position := { line := l.line, column := l.column }

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

def isIdentCont (c : Char) : Bool := c.isAlphanum || c == '_'

def isWhitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

end LexerState

/-! ## Keywords -/

def keywords : List (String × TokenKind) :=
  [ ("contract", .contract), ("function", .function_), ("modifier", .modifier)
  , ("event", .event_), ("struct", .struct_), ("enum", .enum_)
  , ("mapping", .mapping), ("public", .public_), ("private", .private_)
  , ("internal", .internal), ("external", .external)
  , ("view", .view), ("pure", .pure_), ("payable", .payable)
  , ("memory", .memory), ("storage", .storage), ("calldata", .calldata)
  , ("returns", .returns), ("return", .return_)
  , ("if", .if_), ("else", .else_), ("for", .for_), ("while", .while_)
  , ("require", .require_), ("revert", .revert), ("assert", .assert_), ("emit", .emit)
  , ("constructor", .constructor_), ("true", .true_), ("false", .false_)
  , ("uint256", .uint256), ("uint", .uint256)
  , ("address", .address_), ("bool", .bool_), ("string", .string_) ]

def lookupKeyword (s : String) : TokenKind :=
  match keywords.find? (fun (k, _) => k == s) with
  | some (_, tk) => tk
  | none => .ident s

/-! ## Lexer Helpers (with fuel for termination) -/

/-- Skip whitespace using fuel for termination -/
def skipWhitespace (l : LexerState) (fuel : Nat) : LexerState :=
  match fuel with
  | 0 => l
  | fuel' + 1 =>
    match l.peek with
    | some c => if LexerState.isWhitespace c then skipWhitespace l.advance fuel' else l
    | none => l

/-- Skip line comment using fuel -/
def skipLineComment (l : LexerState) (fuel : Nat) : LexerState :=
  match fuel with
  | 0 => l
  | fuel' + 1 =>
    match l.peek with
    | some '\n' => l.advance
    | some _ => skipLineComment l.advance fuel'
    | none => l

/-- Skip block comment using fuel -/
def skipBlockComment (l : LexerState) (fuel : Nat) : LexerState :=
  let l := l.advance.advance  -- skip /*
  go l fuel
where
  go (l : LexerState) (fuel : Nat) : LexerState :=
    match fuel with
    | 0 => l
    | fuel' + 1 =>
      match l.peek, l.peekNext with
      | some '*', some '/' => l.advance.advance
      | some _, _ => go l.advance fuel'
      | none, _ => l

/-- Skip whitespace and comments -/
partial def skipWhitespaceAndComments (l : LexerState) : LexerState :=
  let fuel := l.source.length - l.pos + 1
  let l := skipWhitespace l fuel
  match l.peek, l.peekNext with
  | some '/', some '/' => skipWhitespaceAndComments (skipLineComment l.advance.advance fuel)
  | some '/', some '*' => skipWhitespaceAndComments (skipBlockComment l fuel)
  | _, _ => l

/-- Collect identifier characters -/
def collectIdent (l : LexerState) (fuel : Nat) (acc : List Char) : LexerState × List Char :=
  match fuel with
  | 0 => (l, acc)
  | fuel' + 1 =>
    match l.peek with
    | some c => if LexerState.isIdentCont c then collectIdent l.advance fuel' (c :: acc) else (l, acc)
    | none => (l, acc)

/-- Collect decimal digits -/
def collectDigits (l : LexerState) (fuel : Nat) (acc : List Char) : LexerState × List Char :=
  match fuel with
  | 0 => (l, acc)
  | fuel' + 1 =>
    match l.peek with
    | some c => if c.isDigit then collectDigits l.advance fuel' (c :: acc) else (l, acc)
    | none => (l, acc)

/-- Collect hex digits -/
def collectHexDigits (l : LexerState) (fuel : Nat) (acc : List Char) : LexerState × List Char :=
  match fuel with
  | 0 => (l, acc)
  | fuel' + 1 =>
    match l.peek with
    | some c =>
      if c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
      then collectHexDigits l.advance fuel' (c :: acc)
      else (l, acc)
    | none => (l, acc)

/-- Collect string characters -/
def collectString (l : LexerState) (fuel : Nat) (acc : List Char) : LexerState × List Char :=
  match fuel with
  | 0 => (l, acc)
  | fuel' + 1 =>
    match l.peek with
    | some '"' => (l, acc)
    | some '\\' =>
      match l.advance.peek with
      | some 'n' => collectString l.advance.advance fuel' ('\n' :: acc)
      | some 't' => collectString l.advance.advance fuel' ('\t' :: acc)
      | some 'r' => collectString l.advance.advance fuel' ('\r' :: acc)
      | some '"' => collectString l.advance.advance fuel' ('"' :: acc)
      | some '\\' => collectString l.advance.advance fuel' ('\\' :: acc)
      | some c => collectString l.advance.advance fuel' (c :: acc)
      | none => (l, acc)
    | some c => collectString l.advance fuel' (c :: acc)
    | none => (l, acc)

/-! ## Lexer Functions -/

def lexIdent (l : LexerState) : LexerState × Token :=
  let startPos := l.currentPos
  let fuel := l.source.length - l.pos + 1
  let (l', chars) := collectIdent l fuel []
  let name := String.mk chars.reverse
  let kind := lookupKeyword name
  (l', { kind := kind, pos := startPos })

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def lexInt (l : LexerState) : LexerState × Token :=
  let startPos := l.currentPos
  let fuel := l.source.length - l.pos + 1
  match l.peek, l.peekNext with
  | some '0', some 'x' | some '0', some 'X' =>
    let (l', digits) := collectHexDigits l.advance.advance fuel []
    let val := digits.reverse.foldl (fun acc d => acc * 16 + hexVal d) 0
    (l', { kind := .hexLit val, pos := startPos })
  | _, _ =>
    let (l', digits) := collectDigits l fuel []
    let val := digits.reverse.foldl (fun acc d => acc * 10 + d.toNat - '0'.toNat) 0
    (l', { kind := .intLit val, pos := startPos })

def lexString (l : LexerState) : LexerState × Token :=
  let startPos := l.currentPos
  let l := l.advance  -- skip opening quote
  let fuel := l.source.length - l.pos + 1
  let (l', chars) := collectString l fuel []
  let l'' := l'.advance  -- skip closing quote
  (l'', { kind := .stringLit (String.mk chars.reverse), pos := startPos })

def lexToken (l : LexerState) : LexerState × Token :=
  let l := skipWhitespaceAndComments l
  if l.atEnd then
    (l, { kind := .eof, pos := l.currentPos })
  else
    let startPos := l.currentPos
    match l.peek, l.peekNext with
    | some '=', some '=' => (l.advance.advance, { kind := .eq, pos := startPos })
    | some '!', some '=' => (l.advance.advance, { kind := .neq, pos := startPos })
    | some '<', some '=' => (l.advance.advance, { kind := .le, pos := startPos })
    | some '>', some '=' => (l.advance.advance, { kind := .ge, pos := startPos })
    | some '<', some '<' => (l.advance.advance, { kind := .ltLt, pos := startPos })
    | some '>', some '>' => (l.advance.advance, { kind := .gtGt, pos := startPos })
    | some '&', some '&' => (l.advance.advance, { kind := .ampAmp, pos := startPos })
    | some '|', some '|' => (l.advance.advance, { kind := .pipePipe, pos := startPos })
    | some '+', some '=' => (l.advance.advance, { kind := .plusAssign, pos := startPos })
    | some '-', some '=' => (l.advance.advance, { kind := .minusAssign, pos := startPos })
    | some '*', some '=' => (l.advance.advance, { kind := .starAssign, pos := startPos })
    | some '/', some '=' => (l.advance.advance, { kind := .slashAssign, pos := startPos })
    | some '=', some '>' => (l.advance.advance, { kind := .arrow, pos := startPos })
    | some '+', _ => (l.advance, { kind := .plus, pos := startPos })
    | some '-', _ => (l.advance, { kind := .minus, pos := startPos })
    | some '*', _ => (l.advance, { kind := .star, pos := startPos })
    | some '/', _ => (l.advance, { kind := .slash, pos := startPos })
    | some '%', _ => (l.advance, { kind := .percent, pos := startPos })
    | some '<', _ => (l.advance, { kind := .lt, pos := startPos })
    | some '>', _ => (l.advance, { kind := .gt, pos := startPos })
    | some '=', _ => (l.advance, { kind := .assign, pos := startPos })
    | some '!', _ => (l.advance, { kind := .bang, pos := startPos })
    | some '&', _ => (l.advance, { kind := .amp, pos := startPos })
    | some '|', _ => (l.advance, { kind := .pipe, pos := startPos })
    | some '^', _ => (l.advance, { kind := .caret, pos := startPos })
    | some '~', _ => (l.advance, { kind := .tilde, pos := startPos })
    | some '(', _ => (l.advance, { kind := .lparen, pos := startPos })
    | some ')', _ => (l.advance, { kind := .rparen, pos := startPos })
    | some '{', _ => (l.advance, { kind := .lbrace, pos := startPos })
    | some '}', _ => (l.advance, { kind := .rbrace, pos := startPos })
    | some '[', _ => (l.advance, { kind := .lbracket, pos := startPos })
    | some ']', _ => (l.advance, { kind := .rbracket, pos := startPos })
    | some ';', _ => (l.advance, { kind := .semi, pos := startPos })
    | some ',', _ => (l.advance, { kind := .comma, pos := startPos })
    | some '.', _ => (l.advance, { kind := .dot, pos := startPos })
    | some '?', _ => (l.advance, { kind := .question, pos := startPos })
    | some ':', _ => (l.advance, { kind := .colon, pos := startPos })
    | some '"', _ => lexString l
    | some c, _ =>
      if c.isDigit then lexInt l
      else if LexerState.isIdentStart c then lexIdent l
      else (l.advance, { kind := .unknown c, pos := startPos })
    | none, _ => (l, { kind := .eof, pos := startPos })

/-- Tokenize entire source -/
partial def tokenize (source : String) : List Token :=
  go (LexerState.fromString source) []
where
  go (l : LexerState) (acc : List Token) : List Token :=
    let (l', tok) := lexToken l
    match tok.kind with
    | .eof => (tok :: acc).reverse
    | _ => go l' (tok :: acc)

end Translator.Parser
