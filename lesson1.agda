data Bool : Set where
  false true : Bool

id : Bool → Bool
id x = x

¬ : Bool → Bool
¬ false = true
¬ true  = false

_&&_ : Bool → Bool → Bool
false && _ = false
true  && y = y

-- Type \bN for ℕ \to for →
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one : ℕ
one = succ zero

-- one : ℕ : Set : Set₁ : Set₂ : ...

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

-- Exercises

_||_ : Bool → Bool → Bool
false || y = y
true  || _ = true

is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f true && f false

is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = is-tautology₁ (f true) && is-tautology₁ (f false)

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

half : ℕ → ℕ
half zero = zero
half (succ zero) = zero
half (succ (succ n)) = succ (half n)

_-_ : ℕ → ℕ → ℕ
a - zero = a
zero - succ b = zero
succ a - succ b = a - b

eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (succ _) = false
eq? (succ n) zero = false
eq? (succ n) (succ m) = eq? n m

≤? : ℕ → ℕ → Bool
≤? zero m = true
≤? (succ n) zero = false
≤? (succ n) (succ m) = ≤? n m

even? : ℕ → Bool
even? zero = true
even? (succ zero) = false
even? (succ (succ n)) = even? n

data Weird : Set where
  foo : Weird → Weird

weird-elim : {S : Set} → Weird → S
weird-elim (foo weird) = weird-elim weird

data Empty : Set where
-- Manifestly empty


