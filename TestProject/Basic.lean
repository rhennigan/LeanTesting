/-
  Lean 4 Basics
  =============
  This file introduces fundamental concepts in Lean 4.
-/

-- ============================================
-- SECTION 1: Simple Values and Types
-- ============================================

-- In Lean, every expression has a type.
-- We can use #check to see the type of an expression.

#check 2          -- 2 : Nat (natural number)
#check 2 + 2      -- 2 + 2 : Nat
#check "hello"    -- "hello" : String
#check true       -- true : Bool

-- We can use #eval to evaluate expressions
#eval 2 + 2       -- outputs: 4
#eval 10 * 5      -- outputs: 50

-- ============================================
-- SECTION 2: Defining Constants
-- ============================================

-- Use `def` to define a constant
def myNumber : Nat := 42

#eval myNumber    -- outputs: 42

-- Lean can often infer the type
def anotherNumber := 100

#eval anotherNumber + myNumber  -- outputs: 142

-- ============================================
-- SECTION 3: Functions
-- ============================================

-- A simple function that doubles a number
def double (n : Nat) : Nat := n + n

#eval double 5    -- outputs: 10

-- Function with multiple arguments
def add (a b : Nat) : Nat := a + b

#eval add 3 7     -- outputs: 10

-- ============================================
-- SECTION 4: Propositions and Proofs
-- ============================================

-- In Lean, propositions are types and proofs are values.
-- The type `Prop` is the type of all propositions.

#check 2 + 2 = 4  -- 2 + 2 = 4 : Prop (this is a proposition)
#check 1 = 2      -- 1 = 2 : Prop (also a proposition, but false)

-- ============================================
-- SECTION 5: Proving Equality with rfl
-- ============================================

-- `rfl` (reflexivity) proves that something equals itself.
-- It works when both sides compute to the same value.

-- Since 2 + 2 computes to 4, we can prove they're equal:
theorem two_plus_two : 2 + 2 = 4 := rfl

-- More examples using rfl:
theorem three_times_three : 3 * 3 = 9 := rfl
theorem simple_arithmetic : (1 + 2) * 3 = 9 := rfl

-- ============================================
-- SECTION 6: Example Proofs with Tactics
-- ============================================

-- We can also write proofs using tactic mode with `by`
theorem two_plus_two' : 2 + 2 = 4 := by
  rfl  -- the `rfl` tactic

-- A slightly more interesting proof using tactics
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl  -- works because n + 0 reduces to n by definition

-- ============================================
-- SECTION 7: Using native_decide for decidable props
-- ============================================

-- For decidable propositions, we can use native_decide
theorem two_plus_two'' : 2 + 2 = 4 := by native_decide

-- ============================================
-- Summary
-- ============================================

/-
  Key takeaways:
  1. Every expression in Lean has a type
  2. Propositions (like 2 + 2 = 4) are types
  3. Proofs are values that inhabit proposition types
  4. `rfl` proves equality when both sides compute to the same value
  5. Tactics (like `rfl` in `by rfl`) can also construct proofs
-/
