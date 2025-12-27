import LeanEVM.Core.Types
import LeanEVM.Core.Execution

/-!
# Automated Market Maker (AMM) Model

This module models a simple constant-product AMM (Uniswap v2 style).
The invariant is: reserve0 * reserve1 = k (constant product)

## Key Concepts

- **Liquidity Pool**: Holds reserves of two tokens
- **LP Tokens**: Represent share of pool ownership
- **Swap**: Exchange one token for another
- **Constant Product**: x * y = k ensures fair pricing
-/

namespace LeanEVM.Contracts

open LeanEVM

/-! ## AMM State -/

/-- AMM Pool State -/
structure AMMState where
  /-- Reserve of token0 -/
  reserve0 : Nat
  /-- Reserve of token1 -/
  reserve1 : Nat
  /-- Total LP token supply -/
  totalSupply : Nat
  /-- LP token balances: address → balance -/
  lpBalances : Address → Nat
  /-- Accumulated fees for token0 -/
  feeAccum0 : Nat
  /-- Accumulated fees for token1 -/
  feeAccum1 : Nat

namespace AMMState

/-- Create empty pool -/
def empty : AMMState :=
  { reserve0 := 0
  , reserve1 := 0
  , totalSupply := 0
  , lpBalances := fun _ => 0
  , feeAccum0 := 0
  , feeAccum1 := 0 }

/-- Get LP balance of an address -/
def lpBalanceOf (state : AMMState) (owner : Address) : Nat :=
  state.lpBalances owner

/-- Set LP balance -/
def setLpBalance (state : AMMState) (addr : Address) (bal : Nat) : AMMState :=
  { state with lpBalances := fun a => if a == addr then bal else state.lpBalances a }

/-- Constant product (k value) -/
def k (state : AMMState) : Nat :=
  state.reserve0 * state.reserve1

/-- Check if pool is initialized -/
def isInitialized (state : AMMState) : Bool :=
  state.reserve0 > 0 && state.reserve1 > 0

end AMMState

/-! ## AMM Constants -/

/-- Fee denominator (0.3% fee = 3/1000) -/
def FEE_DENOMINATOR : Nat := 1000

/-- Fee numerator -/
def FEE_NUMERATOR : Nat := 3

/-- Minimum liquidity locked forever (prevents division by zero attacks) -/
def MINIMUM_LIQUIDITY : Nat := 1000

/-! ## AMM Operations -/

/-- Calculate output amount for a swap (with 0.3% fee) -/
def getAmountOut (amountIn : Nat) (reserveIn reserveOut : Nat) : Option Nat :=
  if reserveIn == 0 || reserveOut == 0 then
    none
  else
    -- amountInWithFee = amountIn * 997 (0.3% fee)
    let amountInWithFee := amountIn * (FEE_DENOMINATOR - FEE_NUMERATOR)
    let numerator := amountInWithFee * reserveOut
    let denominator := reserveIn * FEE_DENOMINATOR + amountInWithFee
    if denominator == 0 then none
    else some (numerator / denominator)

/-- Calculate input amount needed for desired output -/
def getAmountIn (amountOut : Nat) (reserveIn reserveOut : Nat) : Option Nat :=
  if reserveIn == 0 || reserveOut == 0 || amountOut >= reserveOut then
    none
  else
    let numerator := reserveIn * amountOut * FEE_DENOMINATOR
    let denominator := (reserveOut - amountOut) * (FEE_DENOMINATOR - FEE_NUMERATOR)
    if denominator == 0 then none
    else some (numerator / denominator + 1)

/-- Square root (integer, floor) using Newton's method -/
partial def sqrt (n : Nat) : Nat :=
  if n == 0 then 0
  else
    let rec loop (x : Nat) : Nat :=
      let x' := (x + n / x) / 2
      if x' >= x then x else loop x'
    loop n

/-- Initialize liquidity pool with first deposit -/
def initializeLiquidity (state : AMMState) (msg : MsgContext)
    (amount0 : Nat) (amount1 : Nat) : ExecResult AMMState := do
  -- Check: pool must not be initialized
  require (!state.isInitialized) "AMM: already initialized"
  -- Check: amounts must be positive
  require (amount0 > 0 && amount1 > 0) "AMM: insufficient initial liquidity"
  -- Calculate initial LP tokens: sqrt(amount0 * amount1) - MINIMUM_LIQUIDITY
  let liquidity := sqrt (amount0 * amount1)
  require (liquidity > MINIMUM_LIQUIDITY) "AMM: insufficient liquidity minted"
  let lpTokens := liquidity - MINIMUM_LIQUIDITY
  -- Effect: set reserves
  let state' := { state with
    reserve0 := amount0
    reserve1 := amount1
    totalSupply := liquidity
    -- Lock MINIMUM_LIQUIDITY to zero address, rest to sender
    lpBalances := fun a =>
      if a == msg.sender then lpTokens
      else if a.isZero then MINIMUM_LIQUIDITY
      else 0
  }
  pure state'

/-- Add liquidity to existing pool -/
def addLiquidity (state : AMMState) (msg : MsgContext)
    (amount0Desired : Nat) (amount1Desired : Nat)
    (amount0Min : Nat) (amount1Min : Nat) : ExecResult (AMMState × Nat × Nat × Nat) := do
  -- Check: pool must be initialized
  require state.isInitialized "AMM: not initialized"
  -- Calculate optimal amounts to maintain ratio
  let amount1Optimal := amount0Desired * state.reserve1 / state.reserve0
  let (amount0, amount1) :=
    if amount1Optimal <= amount1Desired then
      (amount0Desired, amount1Optimal)
    else
      let amount0Optimal := amount1Desired * state.reserve0 / state.reserve1
      (amount0Optimal, amount1Desired)
  -- Check: amounts meet minimums
  require (amount0 >= amount0Min) "AMM: insufficient amount0"
  require (amount1 >= amount1Min) "AMM: insufficient amount1"
  require (amount0 > 0 && amount1 > 0) "AMM: insufficient liquidity"
  -- Calculate LP tokens to mint (proportional to contribution)
  let liquidity := Nat.min
    (amount0 * state.totalSupply / state.reserve0)
    (amount1 * state.totalSupply / state.reserve1)
  require (liquidity > 0) "AMM: insufficient liquidity minted"
  -- Effect: update state
  let state' := { state with
    reserve0 := state.reserve0 + amount0
    reserve1 := state.reserve1 + amount1
    totalSupply := state.totalSupply + liquidity
    lpBalances := fun a =>
      if a == msg.sender then state.lpBalances a + liquidity
      else state.lpBalances a
  }
  pure (state', amount0, amount1, liquidity)

/-- Remove liquidity from pool -/
def removeLiquidity (state : AMMState) (msg : MsgContext)
    (liquidity : Nat) (amount0Min : Nat) (amount1Min : Nat) :
    ExecResult (AMMState × Nat × Nat) := do
  -- Check: user has enough LP tokens
  require (state.lpBalanceOf msg.sender >= liquidity) "AMM: insufficient liquidity"
  require (liquidity > 0) "AMM: zero liquidity"
  -- Calculate token amounts to return (proportional to share)
  let amount0 := liquidity * state.reserve0 / state.totalSupply
  let amount1 := liquidity * state.reserve1 / state.totalSupply
  -- Check: amounts meet minimums
  require (amount0 >= amount0Min) "AMM: insufficient amount0"
  require (amount1 >= amount1Min) "AMM: insufficient amount1"
  -- Effect: update state
  let state' := { state with
    reserve0 := state.reserve0 - amount0
    reserve1 := state.reserve1 - amount1
    totalSupply := state.totalSupply - liquidity
    lpBalances := fun a =>
      if a == msg.sender then state.lpBalances a - liquidity
      else state.lpBalances a
  }
  pure (state', amount0, amount1)

/-- Swap token0 for token1 -/
def swap0For1 (state : AMMState) (_msg : MsgContext)
    (amountIn : Nat) (amountOutMin : Nat) : ExecResult (AMMState × Nat) := do
  -- Check: pool is initialized
  require state.isInitialized "AMM: not initialized"
  require (amountIn > 0) "AMM: insufficient input amount"
  -- Calculate output amount
  match getAmountOut amountIn state.reserve0 state.reserve1 with
  | none => ExecResult.revert "AMM: insufficient liquidity"
  | some amountOut =>
    require (amountOut >= amountOutMin) "AMM: insufficient output amount"
    require (amountOut < state.reserve1) "AMM: insufficient liquidity"
    -- Effect: update reserves
    let state' := { state with
      reserve0 := state.reserve0 + amountIn
      reserve1 := state.reserve1 - amountOut
    }
    pure (state', amountOut)

/-- Swap token1 for token0 -/
def swap1For0 (state : AMMState) (_msg : MsgContext)
    (amountIn : Nat) (amountOutMin : Nat) : ExecResult (AMMState × Nat) := do
  -- Check: pool is initialized
  require state.isInitialized "AMM: not initialized"
  require (amountIn > 0) "AMM: insufficient input amount"
  -- Calculate output amount
  match getAmountOut amountIn state.reserve1 state.reserve0 with
  | none => ExecResult.revert "AMM: insufficient liquidity"
  | some amountOut =>
    require (amountOut >= amountOutMin) "AMM: insufficient output amount"
    require (amountOut < state.reserve0) "AMM: insufficient liquidity"
    -- Effect: update reserves
    let state' := { state with
      reserve0 := state.reserve0 - amountOut
      reserve1 := state.reserve1 + amountIn
    }
    pure (state', amountOut)

/-! ## Verified Properties -/

section Properties

/-! ### Property 1: Cannot Initialize Twice -/

/-- Initializing an already-initialized pool reverts -/
theorem initialize_twice_reverts
    (state : AMMState) (msg : MsgContext) (amount0 amount1 : Nat)
    (h_init : state.isInitialized = true) :
    ∃ m, initializeLiquidity state msg amount0 amount1 = ExecResult.revert m := by
  refine ⟨"AMM: already initialized", ?_⟩
  unfold initializeLiquidity require
  simp only [bind, pure, ExecResult.bind, h_init, Bool.not_true]
  rfl

/-! ### Property 2: Cannot Swap on Empty Pool -/

/-- Swapping on uninitialized pool reverts -/
theorem swap_empty_reverts
    (state : AMMState) (msg : MsgContext) (amountIn amountOutMin : Nat)
    (h_empty : state.isInitialized = false) :
    ∃ m, swap0For1 state msg amountIn amountOutMin = ExecResult.revert m := by
  refine ⟨"AMM: not initialized", ?_⟩
  unfold swap0For1 require
  simp only [bind, pure, ExecResult.bind, h_empty]
  rfl

/-! ### Property 3: Zero Input Swap Reverts -/

/-- Swapping zero tokens reverts -/
theorem swap_zero_reverts
    (state : AMMState) (msg : MsgContext) (amountOutMin : Nat)
    (h_init : state.isInitialized = true) :
    ∃ m, swap0For1 state msg 0 amountOutMin = ExecResult.revert m := by
  refine ⟨"AMM: insufficient input amount", ?_⟩
  unfold swap0For1 require
  simp only [bind, pure, ExecResult.bind, h_init, Nat.lt_irrefl, Bool.and_self]
  rfl

/-! ### Property 4: Insufficient LP Tokens Reverts -/

/-- Removing more liquidity than owned reverts -/
theorem remove_insufficient_reverts
    (state : AMMState) (msg : MsgContext)
    (liquidity amount0Min amount1Min : Nat)
    (h_insufficient : state.lpBalanceOf msg.sender < liquidity) :
    ∃ m, removeLiquidity state msg liquidity amount0Min amount1Min = ExecResult.revert m := by
  refine ⟨"AMM: insufficient liquidity", ?_⟩
  unfold removeLiquidity require
  simp only [bind, pure, ExecResult.bind]
  have h : decide (state.lpBalanceOf msg.sender >= liquidity) = false := by
    simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]
    exact h_insufficient
  simp only [h]
  rfl

/-! ### Property 5: Initialized Pool Has Positive Reserves -/

/-- An initialized pool has positive reserves -/
theorem initialized_has_reserves (state : AMMState)
    (h_init : state.isInitialized = true) :
    state.reserve0 > 0 ∧ state.reserve1 > 0 := by
  unfold AMMState.isInitialized at h_init
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_init
  exact h_init

/-! ### Property 6: Empty Pool Not Initialized -/

/-- An empty pool is not initialized -/
theorem empty_not_initialized : AMMState.empty.isInitialized = false := by
  unfold AMMState.empty AMMState.isInitialized
  simp only [Nat.lt_irrefl, decide_False, Bool.and_self]

/-! ### Property 7: getAmountOut Returns None for Empty Reserve -/

/-- getAmountOut returns none when reserves are zero -/
theorem getAmountOut_none_zero_reserve
    (amountIn : Nat) :
    getAmountOut amountIn 0 100 = none ∧ getAmountOut amountIn 100 0 = none := by
  constructor <;> unfold getAmountOut <;> simp

/-! ### Property 8: Minimum Liquidity Locked -/

/-- Initial liquidity locks MINIMUM_LIQUIDITY tokens to zero address (when sender is not zero) -/
theorem init_locks_minimum_liquidity
    (state state' : AMMState) (msg : MsgContext)
    (amount0 amount1 : Nat)
    (h_sender_not_zero : msg.sender ≠ ⟨0⟩)
    (h_success : initializeLiquidity state msg amount0 amount1 = ExecResult.success state') :
    state'.lpBalanceOf ⟨0⟩ = MINIMUM_LIQUIDITY := by
  unfold initializeLiquidity require at h_success
  simp only [bind, pure, ExecResult.bind] at h_success
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  split at h_success <;> try simp_all
  cases h_success
  simp only [AMMState.lpBalanceOf, Address.isZero]
  have h : (⟨0⟩ : Address) ≠ msg.sender := Ne.symm h_sender_not_zero
  simp only [ne_eq, h, not_false_eq_true, ↓reduceIte, beq_self_eq_true]

end Properties

/-! ## Invariants -/

/-- The constant product invariant (approximately preserved after fees) -/
def constantProductInvariant (state : AMMState) (k₀ : Nat) : Prop :=
  state.k >= k₀

/-- LP shares are proportional to pool ownership -/
def lpSharesProportional (state : AMMState) (owner : Address) : Prop :=
  state.totalSupply > 0 →
  let share := state.lpBalanceOf owner * 1000 / state.totalSupply
  let reserve0Share := share * state.reserve0 / 1000
  let reserve1Share := share * state.reserve1 / 1000
  reserve0Share <= state.reserve0 ∧ reserve1Share <= state.reserve1

end LeanEVM.Contracts
