{-# OPTIONS --allow-unsolved-metas --cubical #-}

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

module _ {ℓ : Level} {ℂ : Category ℓ ℓ} where
  open import Cat.Category
  open Category
  open import Cat.Categories.Cat using (Cat)
  module Cat = Cat.Categories.Cat
  open Exponential
  private
    Catℓ = Cat ℓ ℓ

  -- Exp : Set (lsuc (lsuc ℓ))
  -- Exp = Exponential (Cat (lsuc ℓ) ℓ)
  --   Sets (Opposite ℂ)

  _⇑_ : (A B : Catℓ .Object) → Catℓ .Object
  A ⇑ B = (exponent A B) .obj
    where
      open HasExponentials (Cat.hasExponentials ℓ)

  private
    -- I need `Sets` to be a `Category ℓ ℓ` but it simlpy isn't.
    Setz : Category ℓ ℓ
    Setz = {!Sets!}
    :func*: : ℂ .Object → (Setz ⇑ Opposite ℂ) .Object
    :func*: A = {!!}

    -- prsh = presheaf {ℂ = ℂ}
    -- k = prsh {!!}
    -- :func*:' : ℂ .Object → Presheaf ℂ
    -- :func*:' = prsh
    -- module _ {A B : ℂ .Object} (f : ℂ .Arrow A B) where
    --   open import Cat.Categories.Fun
    --   :func→:' : NaturalTransformation (prsh A) (prsh B)

  yoneda : Functor ℂ (Setz ⇑ (Opposite ℂ))
  yoneda = record
    { func* = :func*:
    ; func→ = {!!}
    ; ident = {!!}
    ; distrib = {!!}
    }
