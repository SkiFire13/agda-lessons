-- Insertion sort

data Bool : Set where
  true false : Bool

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

module _
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

  data Sorted : List → Set where
    empty  : Sorted []
    single : {x : A} → Sorted (x ∷ [])
    other  : {x y : A} {xs : List} → x ≤ y → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)

  insert-sorted : (x : A) (xs : List) → Sorted xs -> Sorted (insert x xs)
  insert-sorted x []           s = single
  insert-sorted x (y ∷ xs)     s with cmp? x y
  insert-sorted x (y ∷ xs)     s             | left  x≤y = other x≤y s
  insert-sorted x (y ∷ [])     single        | right y≤x = other y≤x single
  insert-sorted x (y ∷ z ∷ xs) (other y≤z s) | right y≤x with s' <- insert-sorted x (z ∷ xs) s with cmp? x z
  ... | left  x≤z = other y≤x (other x≤z s)
  ... | right z≤x = other y≤z s'

  sort-sorted : (xs : List) -> Sorted (sort xs)
  sort-sorted []       = empty
  sort-sorted (x ∷ xs) = insert-sorted x (sort xs) (sort-sorted xs)

  data Perm : List → List → Set where
    refl  : {xs : List} → Perm xs xs
    prep  : {xs ys : List} {x : A} → Perm xs ys → Perm (x ∷ xs) (x ∷ ys)
    swap  : {xs ys : List} {x y : A} → Perm xs ys → Perm (x ∷ y ∷ xs) (y ∷ x ∷ ys)
    trans : {xs ys zs : List} → Perm xs ys → Perm ys zs → Perm xs zs

  insert-permutation : (x : A) (xs : List) → Perm (x ∷ xs) (insert x xs)
  insert-permutation x [] = refl
  insert-permutation x (y ∷ xs) with cmp? x y
  ... | left  x≤y = refl
  ... | right y≤x = trans (swap refl) (prep (insert-permutation x xs))

  sort-permutation : (xs : List) → Perm xs (sort xs)
  sort-permutation []       = refl
  sort-permutation (x ∷ xs) = trans (prep (sort-permutation xs)) (insert-permutation x (sort xs))
