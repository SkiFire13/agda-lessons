{-
  Sequence of natural numbers is good if there exists an earlier term
  in the sequence that is less than some later term.

  Dickson's Lemma
  Every infinite sequence of natural numbers is good.
  Proof: take minimal value of the sequence, which is α(i),
  then α(i+1) ≤ α(i). Thus the sequence is good.

  NB: taking minimal value of the sequence is not provable in
  constructive mathematics.
  If this was the case then there would be an algorithm to find
  such value for any sequence of natural numbers, which is impossible.
-}

module _ where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum

Dickson : (ℕ → ℕ) → Set
Dickson α = Σ[ i ∈ ℕ ] α i ≤ α (suc i)

module Classical where
  open import Data.Empty
  open import Relation.Nullary

  postulate
    oracle : (X : Set) → X ⊎ (X → ⊥)

  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → (Σ[ i ∈ ℕ ] ((j : ℕ) → α i ≤ α j))
    go i with oracle (Σ[ j ∈ ℕ ] α j < α i)
    ... | inj₁ (j , p) = go j
    ... | inj₂ q = i , h
      where
      h : (j : ℕ) → α i ≤ α j
      h j with ≤-<-connex (α i) (α j)
      ... | inj₁ αi≤αj = αi≤αj
      ... | inj₂ αj<αi = ⊥-elim (q (j , αj<αi))

    minimum : Σ[ i ∈ ℕ ] ((j : ℕ) → α i ≤ α j)
    minimum = go 0

    theorem : Dickson α
    theorem with minimum
    ... | i , p = i , p (suc i)

-- Note: all of this doesn't case about what is ⊥
module ConstructiveButUninformative (⊥ : Set) where
  ¬_ : Set → Set
  ¬ X = X → ⊥

  ⊥-elim : {X : Set} → ⊥ → ¬ ¬ X
  ⊥-elim p = λ _ → p

  dni : {X : Set} → X → ¬ ¬ X
  dni p = λ k → k p
  -- But we don't always have the converse
  -- Note: we can prove all the classical mathematics
  -- theorems if we add enough ¬¬

  return = dni

  -- This works only for ⊥
  escape : ¬ ¬ ⊥ → ⊥
  escape p = p (λ z → z)

  oracle : (X : Set) → ¬ ¬ (X ⊎ (X → ⊥))
  oracle X = λ z → z (inj₂ (λ x → z (inj₁ x)))

  _⟫=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
  _⟫=_ f = λ z z₁ → f (λ z₂ → z z₂ z₁)

  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
    go i = oracle (Σ[ j ∈ ℕ ] α j < α i) ⟫= g
      where
      g : Σ[ j ∈ ℕ ] α j < α i ⊎ ¬ (Σ[ j ∈ ℕ ] α j < α i) 
          → ¬ ¬  (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
      g (inj₁ (j , p)) = go j
      g (inj₂ q) = return (i , h)
        where
        h : (j : ℕ) → ¬ ¬ (α i ≤ α j)
        h j with ≤-<-connex (α i) (α j)
        ... | inj₁ αi≤αj = return αi≤αj
        ... | inj₂ αj<αi = ⊥-elim (q (j , αj<αi))

    minimum : ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ (α i ≤ α j)))
    minimum = go 0

    theorem : ¬ ¬ (Dickson α)
    theorem = minimum ⟫= λ (i , p) → p (suc i) ⟫= λ q → return (i , q)

module Constructive where
  module _ (α : ℕ → ℕ) where
    open ConstructiveButUninformative (Dickson α)

    thm : Dickson α
    thm = escape (theorem α)

    -- Trick is called:
    --  - Friedman's A-translation
    --  - the continuation trick
    --  - Barr's theorem

    -- Double negation translation of ϕ is the same as ϕ but with ¬¬
    -- in front of every ∃, ∨, =, ≤, ...

    -- 2 metatheorems:
    -- - Statement ϕ provable classically iff double negation translation
    --   provable constructively
    -- - If ϕ consists of just ∃,∨,∧,=,≤ but NOT ∀,⇒, then the double negation
    --   translation is equivalent to just ¬¬ϕ

    -- Double negation monad is also called "continuation monad" in compsci
    -- The transformation we did is also called Continuation Passing Style (CPS)
