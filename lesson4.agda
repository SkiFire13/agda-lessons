data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

data ⊥ : Set where

-- Notion of twin numbers. es: 10 and 12, 31 and 33
-- "Twin a b" witness that a and b are twin.
-- For many values of "a" and "b" this will be empty. (es "Twin zero zero")
data Twin : ℕ → ℕ → Set where
  link : {n : ℕ} → Twin n (succ (succ n))

ex : Twin (succ zero) (succ (succ (succ zero)))
ex = link {succ zero}

ex' : Twin zero zero  → ⊥
ex' () 

infix 5 _≡_
data _≡_ : ℕ → ℕ → Set where
  refl : {n : ℕ} → n ≡ n

lemma₀ : zero ≡ zero
lemma₀ = refl

lemma₁ : (succ zero + succ zero) ≡ succ (succ zero)
lemma₁ = refl

lemma₂ : (b : ℕ) → zero + b ≡ b
lemma₂ b = refl

cong : {x y : ℕ} → (f : ℕ → ℕ) → x ≡ y → f x ≡ f y
cong f refl = refl

lemma-+-zero : (b : ℕ) → b + zero ≡ b
lemma-+-zero zero     = refl
lemma-+-zero (succ b) = cong succ (lemma-+-zero b)
  