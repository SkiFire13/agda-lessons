data _≡_ {l : _} {A : Set l} : A → A → Set where
  refl : {x : A} → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

transport : {A B : Set} → A ≡ B → A → B
transport refl a = a

module _
  (Id : (A : Set) → (a : A) → (b : A) → Set)
  (id : {A : Set} → (a : A) → Id A a a)
  (E-Id : {A : Set}
    → (M : (z₁ z₂ : A) → (z₃ : Id A z₁ z₂) → Set)
    → (a b : A)
    → (t : Id A a b)
    → (e : (x : A) → M x x (id x))
    → M a b t)
  (eq-F-Id : {A : Set} {a₁ a₂ b₁ b₂ : A} → a₁ ≡ a₂ → b₁ ≡ b₂ → Id A a₁ b₁ ≡ Id A a₂ b₂)

  (Π : (B : Set) → (C : B → Set) → Set)
  (lambda : {B : Set} {C : B → Set} → ((x : B) → C x) → Π B C)
  (Ap : {B : Set} {C : B → Set} → Π B C → (b : B) → C b)

  (_+_ : (B : Set) → (C : Set) → Set)
  (inl : {B C : Set} → B → B + C)
  (inr : {B C : Set} → C → B + C)
  (E-+ : {l : _} {B C : Set}
    → (M : (z : B + C) → Set l)
    → (t : B + C)
    → (e₁ : (x₁ : B) → M (inl x₁))
    → (e₂ : (x₂ : C) → M (inr x₂))
    → M t)
  (C₁-+ : {l : _} {B C : Set}
    → (M : (z : B + C) → Set l)
    → (x : B)
    → (e₁ : (x₁ : B) → M (inl x₁))
    → (e₂ : (x₂ : C) → M (inr x₂))
    → E-+ M (inl x) e₁ e₂ ≡ e₁ x)

  (N₁ : Set)
  (⋆ : N₁)
  where
  
  -- Chapter 3.6 Exercise 10
  subst : {A : Set} → (P : A → Set) → (x y : A) → (z : P x) → (w : Id A x y) → P y
  subst P x y z w = Ap (E-Id (λ z₁ z₂ z₃ → Π (P z₁) (λ _ → P z₂)) x y w (λ _ → lambda (λ Px → Px))) z

  -- Chapter 3.6 Exercise 11
  trans : {A : Set} → (x y z : A) → (w₁ : Id A x y) → (w₂ : Id A y z) → Id A x z
  trans {A} x y z w₁ w₂ = Ap (E-Id (λ z₁ z₂ z₃ → Π (Id A x z₁) (λ _ → Id A x z₂)) y z w₂ (λ _ → lambda (λ t → t))) w₁

  -- Chapter 5 Exercise 12
  es12 : {B C : Set} → (x₁ x₂ : B) → Id (B + C) (inl x₁) (inl x₂) → Id B x₁ x₂
  es12 {B} {C} x₁ x₂ z = sol₂
    where
    c : (t : B + C) (d : B) → B
    c t d = E-+ (λ _ → B) t (λ y → y) (λ _ → d)

    c-inl-≡ : (t d : B) → (c (inl t) d) ≡ t
    c-inl-≡ t d = C₁-+ (λ _ → B) t (λ y → y) (λ _ → d)
 
    M : (w₁ w₂ : B + C) (w₃ : Id (B + C) w₁ w₂) → Set
    M w₁ w₂ w₃ = Id B (c w₁ x₁) (c w₂ x₁)

    sol₁ = E-Id M (inl x₁) (inl x₂) z (λ x → id (c x x₁))
    sol₂ = transport (eq-F-Id (c-inl-≡ x₁ x₁) (c-inl-≡ x₂ x₁)) sol₁
 