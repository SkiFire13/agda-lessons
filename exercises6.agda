{-# OPTIONS --allow-unsolved-metas #-}
-- AGDA IN PADOVA 2023
-- Exercise sheet 6

-- The usual naturals, the constructor names shortened to "zer" and "suc"
-- to not confuse them with the ordinal zero and ordinal successor
-- (Agda wouldn't mind, but we might).
data ℕ : Set where
  zer : ℕ
  suc : ℕ → ℕ


-----------------------------
----[ BASIC DEFINITIONS ]----
-----------------------------

-- "O" will be the type of (representations of) (countable) ordinal numbers.
data O : Set

-- "x ≤ y" will be the type of witnesses that "x" is smaller or equal to "y".
data _≤_ : O → O → Set

-- "x < y" will be the type of witnesses that "x" is strictly smaller than "y".
_<_ : O → O → Set

-- "Monotonic f" is the type of witnesses that "f" is a strictly increasing sequence
-- of ordinals.
Monotonic : (ℕ → O) → Set
Monotonic f = (a : ℕ) → f a < f (suc a)

-- The following definition expresses the three fundamental convictions regarding
-- (countable) ordinal numbers:
-- 1. zero should exist.
-- 2. Every number should have a successor.
-- 3. Every (strictly increasing) sequence should have a limit.
data O where
  zero : O
  succ : O → O
  lim  : (f : ℕ → O) → Monotonic f → O

infixl 5 _≤_ _<_

data _≤_ where
  ≤-zero     : {x : O}     → zero ≤ x
  ≤-trans    : {x y z : O} → x ≤ y → y ≤ z → x ≤ z
  ≤-succ-mon : {x y : O}   → x ≤ y → succ x ≤ succ y
  ≤-cocone   : {f : ℕ → O} {fmon : Monotonic f} {x : O} {n : ℕ}
             → x ≤ f n → x ≤ lim f fmon
  ≤-limiting : {f : ℕ → O} {fmon : Monotonic f} {x : O}
             → ((n : ℕ) → f n ≤ x) → lim f fmon ≤ x

x < y = succ x ≤ y

----------------------------
----[ BASIC PROPERTIES ]----
----------------------------

-- If the terms of "f" are all smaller than the corresponding term in "g",
-- then the limit of "f" is smaller than the limit of "g".
lim-mon
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → ((n : ℕ) → f n ≤ g n)
  → lim f fmon ≤ lim g gmon
lim-mon p = ≤-limiting (λ n → ≤-cocone (p n))

refl : {x : O} → x ≤ x
refl {zero}       = ≤-zero
refl {succ x}     = ≤-succ-mon refl
refl {lim f fmon} = lim-mon (λ a → refl)

id≤succ : {x : O} → x ≤ succ x
id≤succ {zero}    = ≤-zero
id≤succ {succ x}  = ≤-succ-mon id≤succ
id≤succ {lim f x} = ≤-limiting (λ n → ≤-trans id≤succ (≤-succ-mon (≤-cocone refl)))

flim-mon : {f : ℕ → O} {fmon : Monotonic f} {n : ℕ} → f n ≤ lim f fmon
flim-mon {f} {fmon} {n} = ≤-cocone refl

<-to-≤ : {x y : O} → x < y → x ≤ y
<-to-≤ (≤-trans x<z z≤y) = ≤-trans (<-to-≤ x<z) z≤y
<-to-≤ (≤-succ-mon x≤y) = ≤-trans x≤y id≤succ
<-to-≤ (≤-cocone x<y) = ≤-cocone (<-to-≤ x<y)

--------------------------
----[ BASIC EXAMPLES ]----
--------------------------

fromℕ : ℕ → O
fromℕ zer     = zero
fromℕ (suc n) = succ (fromℕ n)

fromℕ-monotonic : Monotonic fromℕ
fromℕ-monotonic n = refl

ω : O
ω = lim fromℕ fromℕ-monotonic

ω' : O
ω' = lim (λ n → fromℕ (suc n)) (λ n → refl)

example₀ : ω ≤ ω'
example₀ = lim-mon (λ n → id≤succ)

example₁ : ω' ≤ ω
example₁ = ≤-limiting (λ n → ≤-cocone {n = suc n} refl)


----------------------------
----[ ORDINAL ADDITION ]----
----------------------------

infixl 6 _+_

-- The following two functions are defined in a mutually recursive fashion.
_+_ : O → O → O
+-mon : {x a b : O} → a ≤ b → (x + a) ≤ (x + b)

a + zero       = a
a + succ b     = succ (a + b)
a + lim f fmon = lim (λ n → a + f n) (λ n → +-mon (fmon n))

+-mon {b = zero} ≤-zero       = refl
+-mon {b = succ b} ≤-zero     = ≤-trans id≤succ (≤-succ-mon (+-mon ≤-zero))
+-mon {b = lim f fmon} ≤-zero = ≤-cocone (+-mon (≤-zero {f zer}))
+-mon (≤-trans p q)           = ≤-trans (+-mon p) (+-mon q)
+-mon (≤-succ-mon p)          = ≤-succ-mon (+-mon p)
+-mon (≤-cocone p)            = ≤-cocone (+-mon p)
+-mon (≤-limiting p)          = ≤-limiting (λ b → +-mon (p b))

example₂ : ω < (ω + succ zero)
example₂ = refl

example₃ : (succ zero + ω) ≤ ω
example₃ = ≤-limiting (λ n → ≤-cocone {n = suc n} (lemma n))
  where
  lemma : (n : ℕ) → (succ zero + fromℕ n) ≤ succ (fromℕ n)
  lemma zer = refl
  lemma (suc n) = ≤-succ-mon (lemma n)

-- EXERCISE: Prove this.
+-zero : (a : O) → (zero + a) ≤ a
+-zero zero = ≤-zero
+-zero (succ a) = ≤-succ-mon (+-zero a)
+-zero (lim f x) = ≤-limiting (λ n → ≤-cocone {n = n} (+-zero (f n)))

-- EXERCISE: Prove this. For some clauses, you may need to case split
-- on the implicit variable a.
+-mon' : {x y a : O} → x ≤ y → (x + a) ≤ (y + a)
+-mon' {a = zero} x≤y = x≤y
+-mon' {a = succ a} x≤y = ≤-succ-mon (+-mon' x≤y)
+-mon' {a = lim f fmon} x≤y = lim-mon (λ n → +-mon' x≤y)

one≤fone : {f : ℕ → O} {fmon : Monotonic f} → succ zero ≤ f (suc zer)
one≤fone {fmon = fmon} = ≤-trans (≤-succ-mon ≤-zero) (fmon zer)

-----------------------------------
----[ MORE ORDINAL ARITHMETIC ]----
-----------------------------------

-- EXERCISE: Define ordinal multiplication and exponentiation, by
-- implementing the rules listed on the Wikipedia page on ordinal arithmetic.
_·_ : O → O → O
·-mon : {x a b : O} → a ≤ b → (x · a) ≤ (x · b)
succ-·-smon : {x a b : O} → a < b → (succ x · a) < (succ x · b)
lim-·-smon : {a b : O} {f : ℕ → O} {fmon : Monotonic f} → a < b → (lim f fmon · a) < (lim f fmon · b)

a · zero = zero
a · succ b = (a · b) + a
a · lim f fmon with a
... | zero           = zero
... | a' @ (succ _)  = lim (λ n → a' · f n) (λ n → succ-·-smon (fmon n))
... | a' @ (lim _ _) = lim (λ n → a' · f n) (λ n → lim-·-smon (fmon n))

·-zero : {x : O} → zero · x ≤ zero
·-zero {zero} = ≤-zero
·-zero {succ x} = ·-zero {x}
·-zero {lim f x} = ≤-zero

·-mon ≤-zero = ≤-zero
·-mon (≤-trans a≤c c≤b) = ≤-trans (·-mon a≤c) (·-mon c≤b)
·-mon (≤-succ-mon a≤b) = +-mon' (·-mon a≤b)
·-mon {zero} (≤-cocone {x = x} a≤b) = ·-zero {x}
·-mon {succ _} (≤-cocone {n = n} a≤fn) = ≤-cocone {n = n} (·-mon a≤fn)
·-mon {lim _ _} (≤-cocone {n = n} a≤fn) = ≤-cocone {n = n} (·-mon a≤fn)
·-mon {zero} (≤-limiting g) = ≤-zero
·-mon {succ x} (≤-limiting g) = ≤-limiting (λ n → ·-mon (g n))
·-mon {lim f x} (≤-limiting g) = ≤-limiting (λ n → ·-mon (g n))

succ-·-smon (≤-trans a<y y≤b) = ≤-trans (succ-·-smon a<y) (·-mon y≤b)
succ-·-smon (≤-succ-mon a≤b) = ≤-succ-mon (≤-trans (·-mon a≤b) (+-mon ≤-zero))
succ-·-smon {x} (≤-cocone a<b) =
  ≤-trans (≤-succ-mon (+-mon ≤-zero)) (≤-cocone (·-mon {succ x} a<b))

lim-·-smon (≤-trans a<y y≤b) = ≤-trans (lim-·-smon a<y) (·-mon y≤b)
lim-·-smon {f = f} {fmon = fmon} (≤-succ-mon a≤y) =
  ≤-cocone (≤-trans (≤-succ-mon (·-mon a≤y)) (+-mon (one≤fone {f} {fmon})))
lim-·-smon {f = f} (≤-cocone {f'} {fmon'} {x} {n} a<f'n) = ≤-cocone (lim-·-smon a<f'n)

-- EXERCISE: Define the ordinal number ε₀.

-- EXERCISE: State and prove that ω ^ ε₀ is the same as ε₀.

-- EXERCISE: Define the numbers ε₁, ε₂, ...


----------------------------------
----[ LEMMAS FOR COMPARISONS ]----
----------------------------------

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

proj₁ : {A : Set} {B : A → Set} → Σ A B → A
proj₁ (x , y) = x

proj₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (proj₁ p)
proj₂ (x , y) = y

-- "f simulates g" expresses that every term in the sequence "g"
-- is dominated by some term in the sequence "f".
-- For instance, the sequence 0,1,2,… simulates the sequence 0,1,2,4,8,16,…
-- (and vice versa).
_simulates_ : (ℕ → O) → (ℕ → O) → Set
f simulates g = (a : ℕ) → Σ ℕ (λ b → g a ≤ f b)

-- EXERCISE: Prove this.
comparison-lemma
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → f simulates g → lim g gmon ≤ lim f fmon
comparison-lemma sim = ≤-limiting (λ n → ≤-cocone {n = proj₁ (sim n)} (proj₂ (sim n)))

-- EXERCISE: Reprove "lim-mon" from above using "comparison-lemma".
lim-mon'
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → ((n : ℕ) → f n ≤ g n)
  → lim f fmon ≤ lim g gmon
lim-mon' p = comparison-lemma (λ n → n , p n)


--------------------------------------
----[ THE FAST-GROWING HIERARCHY ]----
--------------------------------------

-- EXERCISE: Implement the "fast-growing hierarchy" of functions,
-- by following the definition of the respective Wikipedia entry.   