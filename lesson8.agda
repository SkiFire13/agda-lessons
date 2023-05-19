{-
  0, 1, ...
  ω, ω+1, ...
  ω^(ω^(ω^…)) = ε₀, ...
  ε₀^(ε₀^(ε₀^…)) = ε₁, ...
  ε_(ε_(ε_…)) = ζ₀, ...


  ω : 
  - I I I I I ...

  ω + 2 :
    +---------------+
  - | I I I I I ... | I I
    +---------------+

  1 + ω :
  - I I I I I I ...

  ω + ω + 1 :
    +---------------+ +---------------+
  - | I I I I I ... | | I I I I I ... | I
    +---------------+ +---------------+

  ω + 1 vs 1 + ω ?
  succ ω = ω + 1 > 1 + ω = ω

  Fundamental convictions of the (countable) ordinal numbers:
  - zero exists
  - every number has a successor
  - every (strictly ascending) sequence has a limit
-}

data ℕ : Set where
  zer : ℕ
  suc : ℕ → ℕ

data O : Set
Monotonic : (ℕ → O) → Set
_<_ : O → O → Set
data _≤_ : O → O → Set

Monotonic f = (n : ℕ) → f n < f (suc n)

data O where
  zero : O
  succ : O → O
  lim  : (f : ℕ → O) → Monotonic f → O

x < y = succ x ≤ y

data _≤_ where
  ≤-zero     : {x : O} → zero ≤ x
  ≤-succ-mon : {x y : O} → x ≤ y → succ x ≤ succ y
  ≤-trans    : {x y z : O} → x ≤ y → y ≤ z → x ≤ z
  ≤-cocone   : {f : ℕ → O} {fmon : Monotonic f} {x : O} {n : ℕ} → x ≤ f n → x ≤ lim f fmon
  -- What if ≤-cocone : f n ≤ lim f fmon ?
  ≤-limiting : {f : ℕ → O} {fmon : Monotonic f} {x : O} → ((n : ℕ) → f n ≤ x) → lim f fmon ≤ x

fromℕ : ℕ → O
fromℕ zer     = zero
fromℕ (suc n) = succ (fromℕ n)

fromℕ-monotonic : Monotonic fromℕ
fromℕ-monotonic zer     = ≤-succ-mon ≤-zero
fromℕ-monotonic (suc n) = ≤-succ-mon (fromℕ-monotonic n)

ω : O
ω = lim fromℕ fromℕ-monotonic

fromℕsuc-monotonic : Monotonic (λ n → fromℕ (suc n))
fromℕsuc-monotonic zer = ≤-succ-mon (≤-succ-mon ≤-zero)
fromℕsuc-monotonic (suc n) = ≤-succ-mon (fromℕsuc-monotonic n)

ω' : O
ω' = lim (λ n → fromℕ (suc n)) fromℕsuc-monotonic

data ⊥ : Set where

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

lemma-lim-f-cong : {f f' : ℕ → O} {fmon : Monotonic f} {fmon' : Monotonic f'}
          (n : ℕ) → lim f fmon ≡ lim f' fmon' → f n ≡ f' n
lemma-lim-f-cong _ refl = refl

-- example : ω ≡ ω' -- Not true, only ω≤ω' and ω'≤ω can be proven
example₀ : ω ≡ ω' → ⊥
example₀ ω≡ω' with () ← lemma-lim-f-cong zer ω≡ω'

≤-refl : (o : O) → o ≤ o
≤-refl zero = ≤-zero
≤-refl (succ o) = ≤-succ-mon (≤-refl o)
≤-refl (lim f x) = ≤-limiting (λ n → ≤-cocone (≤-refl (f n)))

lemma-≤-fn-limf : (f : ℕ → O) (fmon : Monotonic f) (n : ℕ) → f n ≤ lim f fmon
lemma-≤-fn-limf f fmon n = ≤-cocone (≤-refl (f n))

lemma-≤-succ : (o : O) → o ≤ succ o
lemma-≤-succ zero = ≤-zero
lemma-≤-succ (succ o) = ≤-succ-mon (lemma-≤-succ o)
lemma-≤-succ (lim f x) = ≤-limiting (λ n → ≤-trans
  (lemma-≤-succ (f n))
  (≤-succ-mon (lemma-≤-fn-limf f x n)))

example₁ : ω ≤ ω'
example₁ = ≤-limiting λ n → ≤-cocone {n = n} (lemma-≤-succ (fromℕ n))

example₂ : ω' ≤ ω
example₂ = ≤-limiting (λ n → ≤-cocone {n = suc n} (≤-refl (succ (fromℕ n))))


infixl 5 _≤_ _<_
infixl 6 _+_

_+_ : O → O → O
+-mon : {x a b : O} → a ≤ b → (x + a) ≤ (x + b)

x + zero       = x
x + succ y     = succ (x + y)
x + lim f fmon = lim (λ n → x + f n) λ n → +-mon (fmon n)

+-mon {x} {b = zero} ≤-zero   = ≤-refl x
+-mon {x} {b = succ b} ≤-zero = ≤-trans (lemma-≤-succ x) (≤-succ-mon (+-mon ≤-zero))
+-mon {b = lim f fmon} ≤-zero = ≤-cocone (+-mon (≤-zero {f zer}))
+-mon (≤-trans p q)           = ≤-trans (+-mon p) (+-mon q)
+-mon (≤-succ-mon p)          = ≤-succ-mon (+-mon p)
+-mon (≤-cocone p)            = ≤-cocone (+-mon p)
+-mon (≤-limiting p)          = ≤-limiting (λ b → +-mon (p b))

example₃ : ω < succ ω
example₃ = ≤-refl (succ ω)

lemma-1+n≤n+1 : (n : ℕ) → (succ zero) + fromℕ n ≤ succ (fromℕ n)
lemma-1+n≤n+1 zer     = ≤-succ-mon ≤-zero
lemma-1+n≤n+1 (suc n) = ≤-succ-mon (lemma-1+n≤n+1 n)

lemma-1+n≤ω : (n : ℕ) → (succ zero) + fromℕ n ≤ ω
lemma-1+n≤ω zer = ≤-cocone {n = suc zer} (≤-succ-mon ≤-zero)
lemma-1+n≤ω (suc n) = ≤-cocone {n = suc (suc n)} (≤-succ-mon (lemma-1+n≤n+1 n))

example₄ : (succ zero) + ω ≤ ω
example₄ = ≤-limiting (λ n → lemma-1+n≤ω n)
