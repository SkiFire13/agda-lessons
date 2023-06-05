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
  (C₂-+ : {l : _} {B C : Set}
    → (M : (z : B + C) → Set l)
    → (x : C)
    → (e₁ : (x₁ : B) → M (inl x₁))
    → (e₂ : (x₂ : C) → M (inr x₂))
    → E-+ M (inr x) e₁ e₂ ≡ e₂ x)

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
  es12 {B} {C} x₁ x₂ z = id₃
    where
    U₀ = Set
    T : U₀ → Set
    T s = s

    e₂₁ : (z₁ : B) → (z₂ : B) → U₀
    e₂₁ z₁ z₂ = Id B z₁ z₂

    e₂ : C → U₀
    e₂ _ = N₁

    t₂ : (w₂ : B + C) → (z₁ : B) → U₀
    t₂ w₂ z₁ = E-+ (λ _ → U₀) w₂ (e₂₁ z₁) e₂

    e₁₁ : (w₂ : B + C) → (z₁ : B) → U₀
    e₁₁ w₂ z₁ = t₂ w₂ z₁

    t₁ : (w₁ w₂ : B + C) → (w₃ : Id (B + C) w₁ w₂) → Set
    t₁ w₁ w₂ w₃ = T (E-+ (λ _ → U₀) w₁ (e₁₁ w₂) e₂)

    f₁₁ : (x : B) → t₁ (inl x) (inl x) (id (inl x))
    f₁₁ x
      rewrite C₁-+ (λ _ → U₀) x (e₁₁ (inl x)) e₂
      rewrite C₁-+ (λ _ → U₀) x (e₂₁ x) e₂
      = id x

    f₁₂ : (x : C) → t₁ (inr x) (inr x) (id (inr x))
    f₁₂ x rewrite C₂-+ (λ _ → U₀) x (e₁₁ (inr x)) e₂ = ⋆

    f : (x : B + C) → t₁ x x (id x)
    f x = E-+ (λ z → t₁ z z (id z)) x f₁₁ f₁₂
    
    id₁ = E-Id t₁ (inl x₁) (inl x₂) z f
    id₂ = transport (C₁-+ (λ _ → U₀) x₁ (e₁₁ (inl x₂)) e₂) id₁
    id₃ = transport (C₁-+ (λ _ → U₀) x₂ (e₂₁ x₁) e₂) id₂
