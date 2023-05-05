data Bool : Set where
  false true : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

eq? : ℕ → ℕ → Bool
eq? zero     zero     = true
eq? zero     (succ b) = false
eq? (succ a) zero     = false
eq? (succ a) (succ b) with eq? a b
... | false = false
... | true  = true

! : Bool → Bool
! false = true
! true  = false

even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even?' n

data Even : ℕ → Set where
  base : Even zero
  step : {n : ℕ} → Even n → Even (succ (succ n))

fact-zero-is-even : Even zero
fact-zero-is-even = base

fact-two-is-even : Even (succ (succ zero))
fact-two-is-even = step base

fact-six-is-even : Even (succ (succ (succ (succ (succ (succ zero))))))
fact-six-is-even = step (step (step base))

data ⊥ : Set where -- \bot -- Empty data type

fact-if-n-is-even-then-n-is-even : {n : ℕ} → Even n → Even n
-- In computing terms: this functions reads a number n and a witness that
-- n is even and output a withness that n is even
-- In logical terms: For every number n, if n is even then n is even
fact-if-n-is-even-then-n-is-even e = e

-- By definition something is not true iff it implies a contradiction
fact-one-is-not-even : Even (succ zero) → ⊥
fact-one-is-not-even ()

module playground where
  plus2 : ℕ → ℕ
  plus2 n = succ (succ n)

  double : ℕ → ℕ
  double zero = zero
  double (succ n) = plus2 (double n)

  data Even₂ : ℕ → Set where
    even : {n : ℕ} → Even₂ (double n)

  even-to-even₂ : {n : ℕ} → Even n → Even₂ n
  even-to-even₂ base = even
  even-to-even₂ (step e) with even-to-even₂ e
  ... | even = even

  even₂-to-even : {n : ℕ} → Even₂ n → Even n
  even₂-to-even (even {zero}) = base
  even₂-to-even (even {succ n}) = step (even₂-to-even even)
