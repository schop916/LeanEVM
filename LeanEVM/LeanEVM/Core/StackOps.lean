import LeanEVM.Core.Runtime

/-!
# EVM Stack Operations

This module provides safe stack manipulation primitives for EVM execution.
All operations check for underflow (popping empty stack) and overflow (pushing past 1024).

## Stack Properties

- Maximum depth: 1024 elements
- Word size: 256 bits (modeled as `Nat` with explicit wrapping)
- LIFO (Last In, First Out) structure

## Safety Guarantees

All functions return `Except String` to handle:
- Stack Underflow: Attempting to pop from insufficient stack
- Stack Overflow: Attempting to push beyond 1024 limit
-/

namespace LeanEVM.Core.StackOps

open LeanEVM.Core.Runtime

/-! ## Constants -/

/-- Maximum stack depth -/
def MAX_STACK_DEPTH : Nat := 1024

/-- Modulus for 256-bit arithmetic -/
def U256_MOD : Nat := 2 ^ 256

/-- Maximum 256-bit value -/
def U256_MAX : Nat := U256_MOD - 1

/-! ## Stack Primitives -/

/--
Pop `n` items from the stack safely.
Returns the popped items (in order, top first) and the remaining stack.
-/
def pop (stack : List Nat) (n : Nat) : Except String (List Nat × List Nat) :=
  if stack.length < n then
    .error "Stack Underflow"
  else
    let popped := stack.take n
    let remaining := stack.drop n
    .ok (popped, remaining)

/--
Pop exactly 1 item from the stack.
-/
def pop1 (stack : List Nat) : Except String (Nat × List Nat) := do
  let (items, rest) ← pop stack 1
  match items with
  | [a] => .ok (a, rest)
  | _ => .error "Stack Underflow"

/--
Pop exactly 2 items from the stack.
Returns (top, second, remaining).
-/
def pop2 (stack : List Nat) : Except String (Nat × Nat × List Nat) := do
  let (items, rest) ← pop stack 2
  match items with
  | [a, b] => .ok (a, b, rest)
  | _ => .error "Stack Underflow"

/--
Pop exactly 3 items from the stack.
Returns (top, second, third, remaining).
-/
def pop3 (stack : List Nat) : Except String (Nat × Nat × Nat × List Nat) := do
  let (items, rest) ← pop stack 3
  match items with
  | [a, b, c] => .ok (a, b, c, rest)
  | _ => .error "Stack Underflow"

/--
Push items onto the stack safely.
Checks for Stack Overflow (limit 1024).
Items are pushed in order (first item ends up on top).
-/
def push (stack : List Nat) (items : List Nat) : Except String (List Nat) :=
  if stack.length + items.length > MAX_STACK_DEPTH then
    .error "Stack Overflow"
  else
    .ok (items ++ stack)

/--
Push a single value onto the stack.
-/
def push1 (stack : List Nat) (val : Nat) : Except String (List Nat) :=
  push stack [val]

/--
Peek at an item without popping (for DUP/SWAP).
Index 0 = top of stack.
-/
def peek (stack : List Nat) (index : Nat) : Except String Nat :=
  match stack[index]? with
  | some val => .ok val
  | none => .error "Stack Underflow (Peek)"

/--
Duplicate the nth item (1-indexed, DUP1 = top).
-/
def dup (stack : List Nat) (n : Nat) : Except String (List Nat) := do
  if n = 0 || n > 16 then
    .error "Invalid DUP index"
  else
    let val ← peek stack (n - 1)
    push1 stack val

/--
Swap top with nth item (1-indexed, SWAP1 swaps top with 2nd).
-/
def swap (stack : List Nat) (n : Nat) : Except String (List Nat) := do
  if n = 0 || n > 16 then
    .error "Invalid SWAP index"
  else if stack.length < n + 1 then
    .error "Stack Underflow (SWAP)"
  else
    match stack[0]?, stack[n]? with
    | some top, some nth =>
      .ok (stack.set 0 nth |>.set n top)
    | _, _ => .error "Stack Underflow (SWAP)"

/-! ## Arithmetic Helpers -/

/-- Wrap a value to 256-bit range -/
def wrap256 (n : Nat) : Nat := n % U256_MOD

/-- Signed interpretation of 256-bit value (two's complement) -/
def toSigned (n : Nat) : Int :=
  if n < U256_MOD / 2 then
    Int.ofNat n
  else
    Int.ofNat n - Int.ofNat U256_MOD

/-- Convert signed integer back to 256-bit unsigned -/
def fromSigned (i : Int) : Nat :=
  if i >= 0 then
    (i.toNat) % U256_MOD
  else
    (U256_MOD - ((-i).toNat % U256_MOD)) % U256_MOD

/-! ## Verified Properties -/

section Properties

/-- Wrap preserves value for small numbers -/
theorem wrap_small (n : Nat) (h : n < U256_MOD) : wrap256 n = n := by
  simp only [wrap256]
  exact Nat.mod_eq_of_lt h

/-- Wrap is idempotent -/
theorem wrap_idempotent (n : Nat) : wrap256 (wrap256 n) = wrap256 n := by
  simp only [wrap256, U256_MOD]
  have pos : 0 < 2 ^ 256 := Nat.two_pow_pos 256
  have h : n % (2 ^ 256) < 2 ^ 256 := Nat.mod_lt n pos
  exact Nat.mod_eq_of_lt h

end Properties

end LeanEVM.Core.StackOps
