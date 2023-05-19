-- AGDA IN PADOVA 2023
-- Exercise sheet 5

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

module Implementation
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- Given an ordered list "ys", "insert x ys" is the same as "ys",
  -- but with "x" inserted at the correct place to ensure that the
  -- resulting list is again ordered.
  insert : (x : A) → List A → List A
  insert x []       = x ∷ []
  insert x (y ∷ ys) with cmp x y
  ... | left  x≤y = x ∷ y ∷ ys
  ... | right y≤x = y ∷ insert x ys

  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)

-- TWO METHODS FOR VERIFYING CORRECTNESS:
-- (a) first implement, then separately verify correctness
-- (b) correct by construction

module Verification₁ {A : Set} (_≤_ : A → A → Set) (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Implementation _≤_ cmp

  data IsOrdered : List A → Set where
    empty     : IsOrdered []
    singleton : {x : A} → IsOrdered (x ∷ [])
    cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ y ∷ ys)

  lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered (y ∷ insert x ys)
  lemma₀ x y []       y≤x p = cons y≤x singleton
  lemma₀ x y (z ∷ ys) y≤x (cons y≤z q) with cmp x z
  ... | left  x≤z = cons y≤x (cons x≤z q)
  ... | right z≤x = cons y≤z (lemma₀ x z ys z≤x q)

  lemma : (x : A) (ys : List A) → IsOrdered ys → IsOrdered (insert x ys)
  lemma x []       p = singleton
  lemma x (y ∷ ys) p with cmp x y
  ... | left  x≤y = cons x≤y p
  ... | right y≤x = lemma₀ x y ys y≤x p

  theorem : (xs : List A) → IsOrdered (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)

  cheatsort : List A → List A
  cheatsort xs = []

  cheattheorem : (xs : List A) → IsOrdered (cheatsort xs)
  cheattheorem xs = empty

module Verification₂ {A : Set} (_≤_ : A → A → Set) (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Implementation _≤_ cmp

  -- "(x ◂ ys ↝ xys)" should be the type of witnesses that inserting "x" into "ys" somewhere
  -- yields the list "xys".     -- ◂\t  ↝\leadsto
  data _◂_↝_ : A → List A → List A → Set where
    here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
    there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)

  -- "IsPerm xs ys" should be the type of witnesses that the two lists "xs" and "ys"
  -- are permutations of each other, that is, contain exactly the same elements just
  -- perhaps in different order.
  data IsPerm : List A → List A → Set where
    empty : IsPerm [] []
    cons  : {x : A} {xs ys xys : List A} → (x ◂ ys ↝ xys) → IsPerm xs ys → IsPerm (x ∷ xs) xys

  -- EXERCISE: Make sense of the preceding two definitions.

  -- EXERCISE: Fill in this hole.
  example : (x y z : A) → IsPerm (x ∷ y ∷ z ∷ []) (z ∷ x ∷ y ∷ [])
  example x y z = cons (there here) (cons (there here) (cons here empty))

  -- EXERCISE: Verify this lemma.
  lemma : (x : A) (ys : List A) → x ◂ ys ↝ insert x ys
  lemma x [] = here
  lemma x (y ∷ ys) with cmp x y
  ... | left  x≤y = here
  ... | right y≤x = there (lemma x ys)

  -- EXERCISE: Deduce this theorem.
  theorem : (xs : List A) → IsPerm xs (sort xs)
  theorem [] = empty
  theorem (x ∷ xs) = cons (lemma x (sort xs)) (theorem xs)

module CorrectByConstruction₀
  {A : Set} (_≤_ : A → A → Set)
  (max : A) (≤max : {x : A} → x ≤ max)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- "OList l" is the type of ordered lists of elements of A.
  data OList : Set
  -- The usual "where" is missing because the definition of "OList"
  -- mutually depends on the following function extracting the head
  -- of an ordered list.

  head : OList → A
  -- This is just a declaration. The definition will follow once
  -- the constructors of "OList" have been introduced.

  data OList where
    nil  : OList
    cons : (x : A) (xs : OList) → x ≤ head xs → OList

  head nil           = max
  head (cons x xs _) = x

  
  insert : A → OList → OList
  
  insert-head : (x y : A) (ys : OList) → y ≤ x → y ≤ head ys → y ≤ head (insert x ys)

  insert x nil = cons x nil ≤max
  insert x (cons y ys y≤hys) with cmp x y
  ... | left  x≤y = cons x (cons y ys y≤hys) x≤y
  ... | right y≤x = cons y (insert x ys) (insert-head x y ys y≤x y≤hys)

  insert-head x y nil           y≤x y≤hys = y≤x
  insert-head x y (cons z zs p) y≤x y≤hys with cmp x z
  ... | left  x≤z = y≤x
  ... | right z≤x = y≤hys

  sort : List A → OList
  sort []       = nil
  sort (x ∷ xs) = insert x (sort xs)

module CorrectByConstruction₁
  {A : Set} (_≤_ : A → A → Set)
  (min : A) (min≤ : {x : A} → min ≤ x)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- "OList l" is the type of ordered lists of elements of A which are bounded from below by l.
  data OList (l : A) : Set where
    nil  : OList l
    cons : (x : A) → l ≤ x → OList x → OList l

  insert : {l : A} → (x : A) → l ≤ x → OList l → OList l
  insert x l≤x nil             = cons x l≤x nil
  insert x l≤x (cons y l≤y ys) with cmp x y
  ... | left  x≤y = cons x l≤x (cons y x≤y ys)
  ... | right y≤x = cons y l≤y (insert x y≤x ys)

  sort : List A → OList min
  sort []       = nil
  sort (x ∷ xs) = insert x min≤ (sort xs) 

module CorrectByConstruction₂
  {A : Set} (_≤_ : A → A → Set)
  (min : A) (min≤ : {x : A} → min ≤ x)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- As in module Verification₂ above
  data _◂_↝_ : A → List A → List A → Set where
    here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
    there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)

  -- "OPList l xs" is the type of ordered lists whose elements are bounded from below by l
  -- and which are permutations of xs
  
  data OPList (l : A) : List A → Set where
    nil  : OPList l []
    cons : {ys xys : List A} → (x : A) → OPList x ys → l ≤ x → (x ◂ ys ↝ xys) → OPList l xys

  -- EXERCISE: Fill this in.
  insert : {l : A} (x : A) {ys : List A} (oys : OPList l ys) → l ≤ x → OPList l (x ∷ ys)
  insert x nil                l≤x = cons x nil l≤x here
  insert x (cons y oys l≤y p) l≤x with cmp x y
  ... | left  x≤y = cons x (cons y oys x≤y p) l≤x here
  ... | right y≤x = cons y (insert x oys y≤x) l≤y (there p)

  -- EXERCISE: Fill this in.
  sort : (xs : List A) → OPList min xs
  sort []       = nil
  sort (x ∷ xs) = insert x (sort xs) min≤

-- The modules CorrectByConstruction₁ and CorrectByConstruction₂ require a least element "min".
-- EXERCISE: Define for any type A together with a relation _≤_ on A a new
-- type "* A" which is A adjoined by a new least element -∞. Use
-- this construction to get rid of the additional requirement.
data *_ (A : Set) : Set where
  -∞ : * A
  *ₐ : A → * A

module Lift {A : Set} (_≤_ : A → A → Set) where
  -- EXERCISE: Define a relation _≼_ on * A.
  data _≼_ : * A → * A → Set where
    -∞ : {*a : * A} → -∞ ≼ *a
    *ₐ : {a b : A} → a ≤ b → *ₐ a ≼ *ₐ b

  -- EXERCISE: Verify that there is a least element for this relation.
  -∞≼_ : (*a : * A) → -∞ ≼ *a
  -∞≼ _ = -∞

  -- EXERCISE: Verify that if we have a function cmp for A then we also have such a function for * A.
  *cmp : ((x y : A) → (x ≤ y) ⊎ (y ≤ x)) → (*x *y : * A) → (*x ≼ *y) ⊎ (*y ≼ *x)
  *cmp cmp -∞     *y     = left -∞
  *cmp cmp (*ₐ x) -∞     = right -∞
  *cmp cmp (*ₐ x) (*ₐ y) with cmp x y
  ... | left  x≤y = left (*ₐ x≤y)
  ... | right y≤x = right (*ₐ y≤x)

-- EXERCISE: Define a correct-by-construction sort function for A, by using * A.
module CorrectByConstruction₃
  {A : Set} (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  open Lift _≤_
  
  data _◂_↝_ : A → List A → List A → Set where
    here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
    there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)

  data OPList (l : * A) : List A → Set where
    nil  : OPList l []
    cons : {ys xys : List A} → (x : A) → OPList (*ₐ x) ys → l ≼ *ₐ x → (x ◂ ys ↝ xys) → OPList l xys

  insert : {l : * A} (x : A) {ys : List A} (oys : OPList l ys) → l ≼ *ₐ x → OPList l (x ∷ ys)
  insert x nil                l≼x = cons x nil l≼x here
  insert x (cons y oys l≼y p) l≼x with cmp x y
  ... | left  x≤y = cons x (cons y oys (*ₐ x≤y) p) l≼x here
  ... | right y≤x = cons y (insert x oys (*ₐ y≤x)) l≼y (there p)

  sort : (xs : List A) → OPList -∞ xs
  sort [] = nil
  sort (x ∷ xs) = insert x (sort xs) (-∞≼ *ₐ x)
