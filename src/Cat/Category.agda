{-# OPTIONS --cubical #-}

module Cat.Category where

open import Agda.Primitive
open import Data.Unit.Base
open import Data.Product renaming
  ( proj₁ to fst
  ; proj₂ to snd
  ; ∃! to ∃!≈
  )
open import Data.Empty
open import Function
open import Cubical

∃! : ∀ {a b} {A : Set a}
  → (A → Set b) → Set (a ⊔ b)
∃! = ∃!≈ _≡_

∃!-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃!-syntax = ∃

syntax ∃!-syntax (λ x → B) = ∃![ x ] B

record IsCategory {ℓ ℓ' : Level}
  (Object : Set ℓ)
  (Arrow  : Object → Object → Set ℓ')
  (𝟙      : {o : Object} → Arrow o o)
  (_⊕_    : { a b c : Object } → Arrow b c → Arrow a b → Arrow a c)
  : Set (lsuc (ℓ' ⊔ ℓ)) where
  field
    assoc : {A B C D : Object} { f : Arrow A B } { g : Arrow B C } { h : Arrow C D }
      → h ⊕ (g ⊕ f) ≡ (h ⊕ g) ⊕ f
    ident : {A B : Object} {f : Arrow A B}
      → f ⊕ 𝟙 ≡ f × 𝟙 ⊕ f ≡ f

-- open IsCategory public

record Category (ℓ ℓ' : Level) : Set (lsuc (ℓ' ⊔ ℓ)) where
  -- adding no-eta-equality can speed up type-checking.
  no-eta-equality
  field
    Object : Set ℓ
    Arrow  : Object → Object → Set ℓ'
    𝟙      : {o : Object} → Arrow o o
    _⊕_    : { a b c : Object } → Arrow b c → Arrow a b → Arrow a c
    {{isCategory}} : IsCategory Object Arrow 𝟙 _⊕_
  infixl 45 _⊕_
  domain : { a b : Object } → Arrow a b → Object
  domain {a = a} _ = a
  codomain : { a b : Object } → Arrow a b → Object
  codomain {b = b} _ = b

open Category

module _ {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} where
  module _ { A B : ℂ .Object } where
    Isomorphism : (f : ℂ .Arrow A B) → Set ℓ'
    Isomorphism f = Σ[ g ∈ ℂ .Arrow B A ] ℂ ._⊕_ g f ≡ ℂ .𝟙 × ℂ ._⊕_ f g ≡ ℂ .𝟙

    Epimorphism : {X : ℂ .Object } → (f : ℂ .Arrow A B) → Set ℓ'
    Epimorphism {X} f = ( g₀ g₁ : ℂ .Arrow B X ) → ℂ ._⊕_ g₀ f ≡ ℂ ._⊕_ g₁ f → g₀ ≡ g₁

    Monomorphism : {X : ℂ .Object} → (f : ℂ .Arrow A B) → Set ℓ'
    Monomorphism {X} f = ( g₀ g₁ : ℂ .Arrow X A ) → ℂ ._⊕_ f g₀ ≡ ℂ ._⊕_ f g₁ → g₀ ≡ g₁

  -- Isomorphism of objects
  _≅_ : (A B : Object ℂ) → Set ℓ'
  _≅_ A B = Σ[ f ∈ ℂ .Arrow A B ] (Isomorphism f)

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') {A B obj : Object ℂ} where
  IsProduct : (π₁ : Arrow ℂ obj A) (π₂ : Arrow ℂ obj B) → Set (ℓ ⊔ ℓ')
  IsProduct π₁ π₂
    = ∀ {X : ℂ .Object} (x₁ : ℂ .Arrow X A) (x₂ : ℂ .Arrow X B)
    → ∃![ x ] (ℂ ._⊕_ π₁ x ≡ x₁ × ℂ ._⊕_ π₂ x ≡ x₂)

-- Tip from Andrea; Consider this style for efficiency:
-- record IsProduct {ℓ ℓ' : Level} (ℂ : Category {ℓ} {ℓ'})
--   {A B obj : Object ℂ} (π₁ : Arrow ℂ obj A) (π₂ : Arrow ℂ obj B) : Set (ℓ ⊔ ℓ') where
--   field
--      isProduct : ∀ {X : ℂ .Object} (x₁ : ℂ .Arrow X A) (x₂ : ℂ .Arrow X B)
--        → ∃![ x ] (ℂ ._⊕_ π₁ x ≡ x₁ × ℂ. _⊕_ π₂ x ≡ x₂)

record Product {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} (A B : ℂ .Object) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    obj : ℂ .Object
    proj₁ : ℂ .Arrow obj A
    proj₂ : ℂ .Arrow obj B
    {{isProduct}} : IsProduct ℂ proj₁ proj₂

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  Opposite : Category ℓ ℓ'
  Opposite =
    record
      { Object = ℂ .Object
      ; Arrow = flip (ℂ .Arrow)
      ; 𝟙 = ℂ .𝟙
      ; _⊕_ = flip (ℂ ._⊕_)
      ; isCategory = record { assoc = sym assoc ; ident = swap ident }
      }
      where
        open IsCategory (ℂ .isCategory)

-- A consequence of no-eta-equality; `Opposite-is-involution` is no longer
-- definitional - i.e.; you must match on the fields:
--
-- Opposite-is-involution : ∀ {ℓ ℓ'} → {C : Category {ℓ} {ℓ'}} → Opposite (Opposite C) ≡ C
-- Object (Opposite-is-involution {C = C} i) = Object C
-- Arrow (Opposite-is-involution i) = {!!}
-- 𝟙 (Opposite-is-involution i) = {!!}
-- _⊕_ (Opposite-is-involution i) = {!!}
-- assoc (Opposite-is-involution i) = {!!}
-- ident (Opposite-is-involution i) = {!!}

Hom : {ℓ ℓ' : Level} → (ℂ : Category ℓ ℓ') → (A B : Object ℂ) → Set ℓ'
Hom ℂ A B = Arrow ℂ A B

module _ {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} where
  HomFromArrow : (A : ℂ .Object) → {B B' : ℂ .Object} → (g : ℂ .Arrow B B')
    → Hom ℂ A B → Hom ℂ A B'
  HomFromArrow _A = _⊕_ ℂ