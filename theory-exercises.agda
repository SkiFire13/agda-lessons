module _
  (Id : (A : Set) → (a : A) → (b : A) → Set)
  (id : {A : Set} → (a : A) → Id A a a)
  (E-Id : {A : Set}
    → (M : (z₁ z₂ : A) → (z₃ : Id A z₁ z₂) → Set)
    → (a b : A)
    → (t : Id A a b)
    → (e : (x : A) → M x x (id x))
    → M a b t)
  (Π : (B : Set) → (C : B → Set) → Set)
  (lambda : {B : Set} {C : B → Set} → ((x : B) → C x) → Π B C)
  (Ap : {B : Set} {C : B → Set} → Π B C → (b : B) → C b)
  where
  
  -- Chapter 3.6 Exercise 10
  subst : {A : Set} → (P : A → Set) → (x y : A) → (z : P x) → (w : Id A x y) → P y
  subst P x y z w = Ap (E-Id (λ z₁ z₂ z₃ → Π (P z₁) (λ _ → P z₂)) x y w (λ _ → lambda (λ Px → Px))) z

  -- Chapter 3.6 Exercise 11
  trans : {A : Set} → (x y z : A) → (w₁ : Id A x y) → (w₂ : Id A y z) → Id A x z
  trans {A} x y z w₁ w₂ = Ap (E-Id (λ z₁ z₂ z₃ → Π (Id A x z₁) (λ _ → Id A x z₂)) y z w₂ (λ _ → lambda (λ t → t))) w₁
