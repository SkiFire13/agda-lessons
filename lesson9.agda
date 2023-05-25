-- In classical mathematics we have that every statement is either true or false

data _⊎_ (X Y : Set) : Set where
  left  : X → X ⊎ Y
  right : Y → X ⊎ Y

data ⊥ : Set where

-- This does not hold in general in constructive mathematics
-- law-of-excluded-middle : {A : Set} → A ⊎ (A → ⊥)
-- law-of-excluded-middle = {!   !}

-- But it can be postulated
postulate
  law-of-excluded-middle : {A : Set} → A ⊎ (A → ⊥)

  -- But we can also postulate contradictions...
  contradiction : ⊥

-- And we can prove everything...
theorem : {A : Set} → A
theorem with () ← contradiction

-- Or by using module parameters
module _ (law-of-double-negation : {A : Set} → ((A → ⊥) → ⊥) → A) where

-- Note: {-# OPTIONS --safe #-} disables postulates
-- but module parameters are still valid because they "infect" the theorems

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

-- Number of digits of n
-- digits : ℕ → ℕ
-- digits zero     = zero
-- digits (succ n) = succ (digits (half (succ n)) )
-- Problem: termination checking fails
--   the function makes sense and terminates but Agda can't realize this

-- Can be ignored with {-# TERMINATING #-} annotation, disabled by safe mode though.
-- Another way is to use {-# NON_TERMINATING #-} annotation, which silence the warning
--   but prevents the function from being evaluated.
-- You could write another algorithm...
-- Use gas (give upper bound to recursion depth -> must terminate):

digits : ℕ → ℕ
digits n = go n n
  where
  go : ℕ → ℕ → ℕ
  go zero       n        = zero -- bailout
  go (succ gas) zero     = zero
  go (succ gas) (succ n) = succ (go gas (half (succ n)))

-- The fix is ad-hoc: we need to know the gas is enough, and proofs become harder

-- Final option: use "generalized" gas that's fundamental to natural number
