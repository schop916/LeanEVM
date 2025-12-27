import LeanEVM.Core.Types

/-!
# EVM Execution Model

This module defines the execution model for EVM smart contracts.
We model execution as state transitions with explicit handling of:
- Success/revert outcomes
- External calls and reentrancy
- Gas (abstractly)

## Key Design: The Callback Model

External calls are modeled as producing a `callback` that represents
what the called contract might do. This allows us to reason about
reentrancy without fully specifying the called contract's behavior.
-/

namespace LeanEVM

/-! ## Execution Results -/

/-- Result of executing a contract function -/
inductive ExecResult (α : Type) where
  | success : α → ExecResult α
  | revert : String → ExecResult α
  | outOfGas : ExecResult α
  deriving Repr

namespace ExecResult

/-- Map over successful results -/
def map {α β : Type} (f : α → β) : ExecResult α → ExecResult β
  | success a => success (f a)
  | revert msg => revert msg
  | outOfGas => outOfGas

/-- Bind for chaining operations -/
def bind {α β : Type} (x : ExecResult α) (f : α → ExecResult β) : ExecResult β :=
  match x with
  | success a => f a
  | revert msg => revert msg
  | outOfGas => outOfGas

/-- Check if result is successful -/
def isSuccess {α : Type} : ExecResult α → Bool
  | success _ => true
  | _ => false

/-- Check if result is a revert -/
def isRevert {α : Type} : ExecResult α → Bool
  | revert _ => true
  | _ => false

/-- Get value from successful result -/
def get? {α : Type} : ExecResult α → Option α
  | success a => some a
  | _ => none

end ExecResult

instance : Monad ExecResult where
  pure := ExecResult.success
  bind := ExecResult.bind

-- Note: LawfulMonad instance omitted for simplicity in this PoC
-- The monad laws hold but proofs are tedious

/-! ## Require/Assert Helpers -/

/-- Require a condition, revert with message if false -/
def require (cond : Bool) (msg : String) : ExecResult Unit :=
  if cond then ExecResult.success () else ExecResult.revert msg

/-- Assert (same as require but for internal checks) -/
def assert (cond : Bool) (msg : String) : ExecResult Unit :=
  require cond msg

/-! ## Contract State -/

/-- Generic contract state with storage and balance -/
structure ContractState where
  storage : Storage
  balance : Wei

/-- Global EVM state -/
structure EVMState where
  balances : Balances
  contracts : Address → Option ContractState

namespace EVMState

/-- Empty EVM state -/
def empty : EVMState :=
  { balances := fun _ => 0
  , contracts := fun _ => none }

/-- Get balance of an address -/
def getBalance (state : EVMState) (addr : Address) : Wei :=
  state.balances addr

/-- Set balance of an address -/
def setBalance (state : EVMState) (addr : Address) (bal : Wei) : EVMState :=
  { state with balances := state.balances.set addr bal }

/-- Transfer Ether between addresses -/
def transfer (state : EVMState) (from_ to_ : Address) (amount : Wei) : ExecResult EVMState :=
  if state.getBalance from_ < amount then
    ExecResult.revert "Insufficient balance"
  else
    let state' := state.setBalance from_ (state.getBalance from_ - amount)
    let state'' := state'.setBalance to_ (state'.getBalance to_ + amount)
    ExecResult.success state''

end EVMState

/-! ## Reentrancy Model -/

/-- Reentrancy lock state -/
inductive ReentrancyLock where
  | unlocked : ReentrancyLock
  | locked : ReentrancyLock
  deriving Repr, DecidableEq

/-- Contract state with reentrancy guard -/
structure GuardedState (S : Type) where
  inner : S
  lock : ReentrancyLock

namespace GuardedState

variable {S : Type}

/-- Create unlocked state -/
def unlocked (s : S) : GuardedState S :=
  { inner := s, lock := ReentrancyLock.unlocked }

/-- Check if locked -/
def isLocked (gs : GuardedState S) : Bool :=
  gs.lock == ReentrancyLock.locked

/-- Acquire lock -/
def acquireLock (gs : GuardedState S) : ExecResult (GuardedState S) :=
  if gs.isLocked then
    ExecResult.revert "ReentrancyGuard: reentrant call"
  else
    ExecResult.success { gs with lock := ReentrancyLock.locked }

/-- Release lock -/
def releaseLock (gs : GuardedState S) : GuardedState S :=
  { gs with lock := ReentrancyLock.unlocked }

end GuardedState

/-! ## External Call Model -/

/-- Result of an external call -/
inductive CallResult where
  | success : CallResult
  | failure : CallResult
  deriving Repr, DecidableEq

/-- Model of an external call that may trigger callbacks -/
structure ExternalCall where
  target : Address
  value : Wei
  -- In a full model, we'd include calldata and return data

/-- Execute with reentrancy protection -/
def withReentrancyGuard {S : Type} (gs : GuardedState S)
    (action : S → ExecResult S) : ExecResult (GuardedState S) := do
  let gs' ← gs.acquireLock
  match action gs'.inner with
  | ExecResult.success s' => ExecResult.success (GuardedState.unlocked s')
  | ExecResult.revert msg => ExecResult.revert msg
  | ExecResult.outOfGas => ExecResult.outOfGas

/-! ## Two-State Reasoning -/

/-- Specification that a property holds before and after a transition -/
structure TwoStateSpec (S : Type) where
  pre : S → Prop
  post : S → S → Prop

/-- A transition satisfies a spec if: pre(before) → post(before, after) -/
def satisfiesSpec {S : Type} (spec : TwoStateSpec S)
    (transition : S → ExecResult S) (before after : S) : Prop :=
  spec.pre before → transition before = ExecResult.success after → spec.post before after

/-! ## Invariant Reasoning -/

/-- An invariant is preserved by a transition -/
def preservesInvariant {S : Type} (inv : S → Prop)
    (transition : S → ExecResult S) : Prop :=
  ∀ s s', inv s → transition s = ExecResult.success s' → inv s'

/-- An invariant is established by initialization -/
def establishesInvariant {S : Type} (inv : S → Prop) (init : S) : Prop :=
  inv init

end LeanEVM
