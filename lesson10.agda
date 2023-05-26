{-# OPTIONS --no-positivity-check #-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

_ : half (succ (succ (succ zero))) ≡ succ zero
_ = refl

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → n < succ n
  step : {a b : ℕ} → a < b → a < succ b

lemma-succ-mon : {a b : ℕ} → a < b → succ a < succ b
lemma-succ-mon base       = base
lemma-succ-mon (step a<b) = step (lemma-succ-mon a<b)

<-trans : {a b c : ℕ} → a < b → b < c → a < c
<-trans a<b base = step a<b
<-trans a<b (step b<c) = step (<-trans a<b b<c)

half< : {n : ℕ} → half (succ n) < (succ n)
half< {zero} = base
half< {succ zero} = base
half< {succ (succ n)} = lemma-succ-mon (step half<)

-- Witness of the fact that n is accessible
-- Logically for every number x if every number y
--   less than x is accessible then x is accessible
data Acc : ℕ → Set where
  acc : {x : ℕ} → ({y : ℕ} → y < x → Acc y) → Acc x

lemma-zero-is-accessible : Acc zero
lemma-zero-is-accessible = acc λ ()

lemma-one-is-accessible : Acc (succ zero)
lemma-one-is-accessible = acc λ { base → lemma-zero-is-accessible }

ℕ-is-wellfounded : (n : ℕ) → Acc n
ℕ-is-wellfounded zero = lemma-zero-is-accessible
ℕ-is-wellfounded (succ n)
  with acc f ← ℕ-is-wellfounded n
  = acc (λ {
    base     → acc f ;
    (step p) → f p
  })

-- digits : ℕ → ℕ
-- digits zero     = zero
-- digits (succ n) = succ (digits (half (succ n)) )

go : (n : ℕ) → Acc n → ℕ
go zero g = zero
go (succ n) (acc f) = succ (go (half (succ n)) (f half<))
--                                             ^^^^^^^^^^
--                        structurally smaller than acc f

digits : ℕ → ℕ
digits n = go n (ℕ-is-wellfounded n)

data BinaryTree : Set where
  leaf : BinaryTree
  fork : BinaryTree → BinaryTree → BinaryTree

-- By writing `fork s t`, `s` and `t` must be structurally smaller

data CountablyBranchingTree : Set where
  leaf : CountablyBranchingTree
  fork : (ℕ → CountablyBranchingTree) → CountablyBranchingTree

data V : Set where
  fork : (V → V) → V

-- But V can imply an absurd
data ⊥ : Set where
absurd : ⊥
absurd = lemma (fork λ v → v)
  where
  lemma : V → ⊥
  lemma (fork x) = lemma (x (fork x))

data AbsurdlyBranchingTree : Set₁ where
  leaf : AbsurdlyBranchingTree
  fork : (Set → AbsurdlyBranchingTree) → AbsurdlyBranchingTree
