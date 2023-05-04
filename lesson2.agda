data Weird : Set where
  foo : Weird → Weird

data Empty : Set where
-- Manifestly empty

g : Empty → Empty
g x = x

h : Weird → Empty
h (foo w) = h w


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = (a · b) + b

_^_ : ℕ → ℕ → ℕ
a ^ zero   = succ zero
a ^ succ b = a · (a ^ b)

data ListOfNats : Set where
  []  : ListOfNats
  _∷_ : ℕ → ListOfNats → ListOfNats -- ∷ = \:: "cons"

infixr 5 _∷_

example-list : ListOfNats
example-list = zero ∷ succ (succ zero) ∷ succ zero ∷ []

-- For each type X introduces a new type List X
data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X
