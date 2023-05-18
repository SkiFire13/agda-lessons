-- Insertion sort

data Bool : Set where
  true false : Bool

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

module Implementation
  (A : Set)
  (_≤_ : A → A → Set) -- Witness that x ≤ y
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  where

  data List : Set where
    []  : List
    _∷_ : A → List → List

  infixr 5 _∷_

  insert : A → List → List
  insert x []       = x ∷ []
  insert x (y ∷ ys) with cmp? x y
  ... | left  x≤y = x ∷ y ∷ ys
  ... | right y≤x = y ∷ insert x ys

  sort : List → List
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)

module Verification
  (A : Set)
  (_≤_ : A → A → Set) -- Witness that x ≤ y
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  where

  open Implementation A _≤_ cmp?

  -- Witnesses that the given list is sorted
  data IsSorted : List → Set where
    empty     : IsSorted []
    singleton : {x : A} → IsSorted (x ∷ [])
    cons      : {x y : A} {ys : List} → IsSorted (y ∷ ys) → x ≤ y → IsSorted (x ∷ y ∷ ys)

  lemma₀ : (x y : A) (ys : List) → y ≤ x → IsSorted (y ∷ ys) → IsSorted (y ∷ (insert x ys))
  lemma₀ x y [] y≤x p = cons singleton y≤x
  lemma₀ x y (z ∷ ys) y≤x (cons p y≤z) with cmp? x z
  ... | left  x≤z = cons (cons p x≤z) y≤x
  ... | right z≤x = cons (lemma₀ x z ys z≤x p) y≤z

  lemma : (x : A) (ys : List) → IsSorted ys → IsSorted (insert x ys)
  lemma x []       p = singleton
  lemma x (y ∷ ys) p with cmp? x y
  ... | left  x≤y = cons {x} {y} {ys} p x≤y
  ... | right y≤x = lemma₀ x y ys y≤x p

  -- Logical : for every list `xs` it is true that `sort xs` is sorted
  -- Computational : read a list `xs` and computes a witness that `sort xs` is sorted 
  theorem : (xs : List) → IsSorted (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)

module CorrectByConstruction
  (A : Set)
  (_≤_ : A → A → Set) -- Witness that x ≤ y
  (-∞ : A)
  (is-min : {x : A} → -∞ ≤ x)
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  where

  data List : Set where
    []  : List
    _∷_ : A → List → List

  infixr 5 _∷_

  -- data SList : Set where
  --   nil  : SList
  --   cons : (x : A) → (xs : SList) → x ≤ head xs → SList

  -- Sorted lists bounded below by `l`
  data SList (l : A) : Set where
    nil  : SList l
    cons : (x : A) → (xs : SList x) → l ≤ x → SList l

  insert : {l : A} (x : A) (ys : SList l ) → l ≤ x → SList l
  insert x nil           l≤x = cons x nil l≤x
  insert x (cons y ys l≤y) l≤x with cmp? x y 
  ... | left  x≤y = cons x (cons y ys x≤y) l≤x
  ... | right y≤x = cons y (insert x ys y≤x) l≤y

  sort : List → SList -∞
  sort [] = nil
  sort (x ∷ xs) = insert x (sort xs) is-min
