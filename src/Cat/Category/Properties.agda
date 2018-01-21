{-# OPTIONS --allow-unsolved-metas #-}

module Cat.Category.Properties where

open import Agda.Primitive
open import Data.Product
open import Cubical.PathPrelude

open import Cat.Category
open import Cat.Functor
open import Cat.Categories.Sets

module _ {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} { A B : ℂ .Category.Object } {X : ℂ .Category.Object} (f : ℂ .Category.Arrow A B) where
  open Category ℂ
  open IsCategory (isCategory)

  iso-is-epi : Isomorphism {ℂ = ℂ} f → Epimorphism {ℂ = ℂ} {X = X} f
  iso-is-epi (f- , left-inv , right-inv) g₀ g₁ eq =
    begin
    g₀              ≡⟨ sym (proj₁ ident) ⟩
    g₀ ⊕ 𝟙          ≡⟨ cong (_⊕_ g₀) (sym right-inv) ⟩
    g₀ ⊕ (f ⊕ f-)   ≡⟨ assoc ⟩
    (g₀ ⊕ f) ⊕ f-   ≡⟨ cong (λ φ → φ ⊕ f-) eq ⟩
    (g₁ ⊕ f) ⊕ f-   ≡⟨ sym assoc ⟩
    g₁ ⊕ (f ⊕ f-)   ≡⟨ cong (_⊕_ g₁) right-inv ⟩
    g₁ ⊕ 𝟙          ≡⟨ proj₁ ident ⟩
    g₁              ∎

  iso-is-mono : Isomorphism {ℂ = ℂ} f → Monomorphism {ℂ = ℂ} {X = X} f
  iso-is-mono (f- , (left-inv , right-inv)) g₀ g₁ eq =
    begin
    g₀            ≡⟨ sym (proj₂ ident) ⟩
    𝟙 ⊕ g₀        ≡⟨ cong (λ φ → φ ⊕ g₀) (sym left-inv) ⟩
    (f- ⊕ f) ⊕ g₀ ≡⟨ sym assoc ⟩
    f- ⊕ (f ⊕ g₀) ≡⟨ cong (_⊕_ f-) eq ⟩
    f- ⊕ (f ⊕ g₁) ≡⟨ assoc ⟩
    (f- ⊕ f) ⊕ g₁ ≡⟨ cong (λ φ → φ ⊕ g₁) left-inv ⟩
    𝟙 ⊕ g₁        ≡⟨ proj₂ ident ⟩
    g₁            ∎

  iso-is-epi-mono : Isomorphism {ℂ = ℂ} f → Epimorphism {ℂ = ℂ} {X = X} f × Monomorphism {ℂ = ℂ} {X = X} f
  iso-is-epi-mono iso = iso-is-epi iso , iso-is-mono iso

{-
epi-mono-is-not-iso : ∀ {ℓ ℓ'} → ¬ ((ℂ : Category {ℓ} {ℓ'}) {A B X : Object ℂ} (f : Arrow ℂ A B ) → Epimorphism {ℂ = ℂ} {X = X} f → Monomorphism {ℂ = ℂ} {X = X} f → Isomorphism {ℂ = ℂ} f)
epi-mono-is-not-iso f =
  let k = f {!!} {!!} {!!} {!!}
  in {!!}
-}


module _ {ℓ ℓ'} (ℂ : Category ℓ ℓ') {{hasProducts : HasProducts ℂ}} (B C : ℂ .Category.Object) where
  open Category
  open HasProducts hasProducts
  open Product
  prod-obj : (A B : ℂ .Object) → ℂ .Object
  prod-obj A B = Product.obj (product A B)
  -- The product mentioned in awodey in Def 6.1 is not the regular product of arrows.
  -- It's a "parallel" product
  ×A : {A A' B B' : ℂ .Object} → ℂ .Arrow A A' → ℂ .Arrow B B'
    → ℂ .Arrow (prod-obj A B) (prod-obj A' B')
  ×A {A = A} {A' = A'} {B = B} {B' = B'} a b = arrowProduct (product A' B')
    (ℂ ._⊕_ a ((product A B) .proj₁))
    (ℂ ._⊕_ b ((product A B) .proj₂))

  IsExponential : {Cᴮ : ℂ .Object} → ℂ .Arrow (prod-obj Cᴮ B) C → Set (ℓ ⊔ ℓ')
  IsExponential eval = ∀ (A : ℂ .Object) (f : ℂ .Arrow (prod-obj A B) C)
    → ∃![ f~ ] (ℂ ._⊕_ eval (×A f~ (ℂ .𝟙)) ≡ f)

  record Exponential : Set (ℓ ⊔ ℓ') where
    field
      -- obj ≡ Cᴮ
      obj : ℂ .Object
      eval : ℂ .Arrow ( prod-obj obj B ) C
      {{isExponential}} : IsExponential eval

_⇑_ = Exponential

-- yoneda : ∀ {ℓ ℓ'} → {ℂ : Category ℓ ℓ'} → Functor ℂ (Sets ⇑ (Opposite ℂ))
-- yoneda = {!!}
