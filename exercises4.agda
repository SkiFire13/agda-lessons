-- AGDA IN PADOVA 2023
-- Exercise sheet 5

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ⊥ : Set where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixl 5 _≡_
infixl 6 _+_
infixl 7 _·_

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)


------------------------------------
----[ GENERALITIES ON EQUALITY ]----
------------------------------------

data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- EQUATIONAL REASONING

infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p


---------------------------------
----[ EQUALITIES OF NUMBERS ]----
---------------------------------

lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero     = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)
-- (lemma-+-zero a) is a value of type ((a + zero) ≡ a).
-- What we need is a value of type (succ (a + zero) ≡ succ a).

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero     b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero     b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b =
  trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))

lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative zero     b c = refl
lemma-+-associative (succ a) b c = begin
  succ (a + (b + c)) ≡⟨ cong succ (lemma-+-associative a b c) ⟩
  succ ((a + b) + c) ≡⟨⟩
  ((succ a + b) + c) ∎

lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive zero b c = refl
lemma-·-distributive (succ a) b c = begin
  ((succ a + b) · c)      ≡⟨⟩
  ((succ (a + b)) · c)    ≡⟨⟩
  (c + (a + b) · c)       ≡⟨ cong (c +_) (lemma-·-distributive a b c) ⟩
  c + ((a · c) + (b · c)) ≡⟨ lemma-+-associative c (a · c) (b · c) ⟩
  (c + a · c) + (b · c)   ≡⟨⟩
  (succ a · c) + (b · c)  ∎

-- EXERCISE: Prove this theorem.
lemma-+-swap : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap zero     b c = refl
lemma-+-swap (succ a) b c = begin
  ((succ a) + (b + c)) ≡⟨⟩
  (succ (a + (b + c))) ≡⟨ cong succ (lemma-+-swap a b c) ⟩
  (succ (b + (a + c))) ≡⟨ symm (lemma-+-succ b (a + c)) ⟩
  (b + succ (a + c))   ≡⟨⟩
  (b + ((succ a) + c)) ∎
-- Note: There is a second solution without a case distinction.
-- This second solution instead appeals to associativity and commutativity.

lemma-+-swap' : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap' a b c = begin
  (a + (b + c)) ≡⟨ lemma-+-associative a b c ⟩
  ((a + b) + c) ≡⟨ cong (_+ c) (lemma-+-commutative a b) ⟩
  ((b + a) + c) ≡⟨ symm (lemma-+-associative b a c) ⟩
  (b + (a + c)) ∎

-- EXERCISE: Verify associativity of multiplication.
lemma-·-associative : (a b c : ℕ) → ((a · (b · c)) ≡ ((a · b) · c))
lemma-·-associative zero     b c = refl
lemma-·-associative (succ a) b c = begin
  (succ a) · (b · c)  ≡⟨⟩
  b · c + a · (b · c) ≡⟨ cong (b · c +_) (lemma-·-associative a b c) ⟩
  b · c + (a · b) · c ≡⟨ symm (lemma-·-distributive b (a · b) c) ⟩
  (b + (a · b)) · c   ≡⟨⟩
  (succ a · b) · c    ∎

-- EXERCISE: Fill in this hole.
lemma-·-zero : (a : ℕ) → ((a · zero) ≡ zero)
lemma-·-zero zero     = refl
lemma-·-zero (succ a) = lemma-·-zero a

-- EXERCISE: Fill in this hole.
lemma-·-succ : (a b : ℕ) → ((a · succ b) ≡ (a + (a · b)))
lemma-·-succ zero b     = refl
lemma-·-succ (succ a) b = begin
  (succ a) · (succ b)       ≡⟨⟩
  (succ b) + (a · succ b)   ≡⟨⟩
  succ (b + (a · succ b))   ≡⟨ cong succ (cong (b +_) (lemma-·-succ a b)) ⟩
  succ (b + (a + (a · b)))  ≡⟨ cong succ (lemma-+-swap b a (a · b)) ⟩
  succ (a + ((succ a) · b)) ≡⟨⟩
  (succ a) + ((succ a) · b) ∎

-- EXERCISE: Verify commutativity of multiplication.
-- Hint: lemma-·-zero and lemma-·-succ will come in handy.
lemma-·-commutative : (a b : ℕ) → ((a · b) ≡ (b · a))
lemma-·-commutative a zero     = lemma-·-zero a
lemma-·-commutative a (succ b) = begin
  a · (succ b) ≡⟨ lemma-·-succ a b ⟩
  a + a · b    ≡⟨ cong (a +_) (lemma-·-commutative a b) ⟩
  a + b · a    ≡⟨⟩
  (succ b) · a ∎

-----------------------------
----[ MORE ON RELATIONS ]----
-----------------------------

data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- EXERCISE: Define a predicate "AllEven" for lists of natural numbers
-- such that "AllEven xs" is inhabited if and only if all entries of the list "xs" are even.
-- By convention, the empty list counts as consisting of even-only elements.
data AllEven : List ℕ → Set where
  even-[]   : AllEven []
  even-∷ : {x : ℕ} {xs : List ℕ} → Even x → AllEven xs → AllEven (x ∷ xs)

data Dec (X : Set) : Set where
  yes : X       → Dec X
  no  : (X → ⊥) → Dec X

data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero     = left base-even
lemma-even-odd (succ zero) = right base-odd
lemma-even-odd (succ (succ a)) with lemma-even-odd a
... | left e  = left (step-even e)
... | right o = right (step-odd o)

lemma-odd-and-even : {a : ℕ} → Odd a → Even a → ⊥
lemma-odd-and-even (step-odd q) (step-even p) = lemma-odd-and-even q p

-- EXERCISE: Fill this hole, establishing that the property for
-- a number to be even is decidable.
even? : (n : ℕ) → Dec (Even n)
even? zero            = yes base-even
even? (succ zero)     = no (λ ())
even? (succ (succ n)) with even? n
... | yes e = yes (step-even e)
... | no  o = no (λ e → o (extract-step-even e))
  where
  extract-step-even : Even (succ (succ n)) → Even n
  extract-step-even (step-even e) = e

-- EXERCISE: Fill this hole, establishing that the property for
-- a list of numbers to consist only of even numbers is decidable.
all-even? : (xs : List ℕ) → Dec (AllEven xs)
all-even? []       = yes even-[]
all-even? (x ∷ xs) with even? x | all-even? xs
... | yes yx | yes yxs = yes (even-∷ yx yxs)
... | no ¬ex | _       = no λ { (even-∷ ex _) → ¬ex ex }
... | _      | no ¬exs = no λ { (even-∷ _ exs) → ¬exs exs }

-- EXERCISE: Show that the sum of the elements of a list satisfying "AllEven" is even.
sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs

lemma-+-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-+-even base-even     q = q
lemma-+-even (step-even p) q = step-even (lemma-+-even p q)

sum-is-even : (xs : List ℕ) → AllEven xs → Even (sum xs)
sum-is-even []       p               = base-even
sum-is-even (x ∷ xs) (even-∷ ex exs) = lemma-+-even ex (sum-is-even xs exs)


-- EXERCISE: Define a predicate "All P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "All P xs" is inhabited if
-- and only if all entries of the list "xs" satisfy P.
-- The special case "All Even" should coincide with the predicate
-- "AllEven" from the previous exercise.
data All {A : Set} (P : A → Set) : List A → Set where
  all-[] : All P []
  all-∷  : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

-- EXERCISE: Define a predicate "Any P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "Any P xs" is inhabited if
-- and only if at least one entry of the list "xs" satisfies P.
data Any {A : Set} (P : A → Set) : List A → Set where
  base-any : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  step-any : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- EXERCISE: Define a relation "_∈_" such that "x ∈ ys" is the type
-- of witnesses that x occurs in the list ys.
data _∈_ {A : Set} : A → List A → Set where
  base-∈ : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  step-∈ : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

-- EXERCISE: Show that "x ∈ ys" if and only if "Any (_≡_ x) ys".
∈-to-Any : {A : Set} {x : A} {ys : List A} → x ∈ ys → Any (_≡_ x) ys
∈-to-Any base-∈        = base-any refl
∈-to-Any (step-∈ x∈ys) = step-any (∈-to-Any x∈ys)

Any-to-∈ : {A : Set} {x : A} {ys : List A} → Any (_≡_ x) ys → x ∈ ys
Any-to-∈ (base-any refl) = base-∈
Any-to-∈ (step-any any)  = step-∈ (Any-to-∈ any)
