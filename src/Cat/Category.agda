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

module _ {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} { A B : ℂ .Object } where
  private
    open module ℂ = Category ℂ
    _+_ = ℂ._⊕_

  Isomorphism : (f : ℂ.Arrow A B) → Set ℓ'
  Isomorphism f = Σ[ g ∈ ℂ.Arrow B A ] g ℂ.⊕ f ≡ ℂ.𝟙 × f + g ≡ ℂ.𝟙

  Epimorphism : {X : ℂ.Object } → (f : ℂ.Arrow A B) → Set ℓ'
  Epimorphism {X} f = ( g₀ g₁ : ℂ.Arrow B X ) → g₀ + f ≡ g₁ + f → g₀ ≡ g₁

  Monomorphism : {X : ℂ.Object} → (f : ℂ.Arrow A B) → Set ℓ'
  Monomorphism {X} f = ( g₀ g₁ : ℂ.Arrow X A ) → f + g₀ ≡ f + g₁ → g₀ ≡ g₁

  iso-is-epi : ∀ {X} (f : ℂ.Arrow A B) → Isomorphism f → Epimorphism {X = X} f
  iso-is-epi f (f- , left-inv , right-inv) g₀ g₁ eq =
    begin
    g₀              ≡⟨ sym (fst ident) ⟩
    g₀ + ℂ.𝟙        ≡⟨ cong (_+_ g₀) (sym right-inv) ⟩
    g₀ + (f + f-)   ≡⟨ assoc ⟩
    (g₀ + f) + f-   ≡⟨ cong (λ x → x + f-) eq ⟩
    (g₁ + f) + f-   ≡⟨ sym assoc ⟩
    g₁ + (f + f-)   ≡⟨ cong (_+_ g₁) right-inv ⟩
    g₁ + ℂ.𝟙        ≡⟨ fst ident ⟩
    g₁              ∎
    where
      open IsCategory ℂ.isCategory

  iso-is-mono : ∀ {X} (f : ℂ.Arrow A B ) → Isomorphism f → Monomorphism {X = X} f
  iso-is-mono f (f- , (left-inv , right-inv)) g₀ g₁ eq =
    begin
    g₀            ≡⟨ sym (snd ident) ⟩
    ℂ.𝟙 + g₀      ≡⟨ cong (λ x → x + g₀) (sym left-inv) ⟩
    (f- + f) + g₀ ≡⟨ sym assoc ⟩
    f- + (f + g₀) ≡⟨ cong (_+_ f-) eq ⟩
    f- + (f + g₁) ≡⟨ assoc ⟩
    (f- + f) + g₁ ≡⟨ cong (λ x → x + g₁) left-inv ⟩
    ℂ.𝟙 + g₁      ≡⟨ snd ident ⟩
    g₁            ∎
    where
      open IsCategory ℂ.isCategory

  iso-is-epi-mono : ∀ {X} (f : ℂ.Arrow A B ) → Isomorphism f → Epimorphism {X = X} f × Monomorphism {X = X} f
  iso-is-epi-mono f iso = iso-is-epi f iso , iso-is-mono f iso

{-
epi-mono-is-not-iso : ∀ {ℓ ℓ'} → ¬ ((ℂ : Category {ℓ} {ℓ'}) {A B X : Object ℂ} (f : Arrow ℂ A B ) → Epimorphism {ℂ = ℂ} {X = X} f → Monomorphism {ℂ = ℂ} {X = X} f → Isomorphism {ℂ = ℂ} f)
epi-mono-is-not-iso f =
  let k = f {!!} {!!} {!!} {!!}
  in {!!}
-}

-- Isomorphism of objects
_≅_ : ∀ {ℓ ℓ'} {ℂ : Category ℓ ℓ'} (A B : Object ℂ) → Set ℓ'
_≅_ {ℂ = ℂ} A B = Σ[ f ∈ ℂ .Arrow A B ] (Isomorphism {ℂ = ℂ} f)

IsProduct : ∀ {ℓ ℓ'} (ℂ : Category ℓ ℓ') {A B obj : Object ℂ} (π₁ : Arrow ℂ obj A) (π₂ : Arrow ℂ obj B) → Set (ℓ ⊔ ℓ')
IsProduct ℂ {A = A} {B = B} π₁ π₂
  = ∀ {X : ℂ.Object} (x₁ : ℂ.Arrow X A) (x₂ : ℂ.Arrow X B)
  → ∃![ x ] (π₁ ℂ.⊕ x ≡ x₁ × π₂ ℂ.⊕ x ≡ x₂)
  where
    open module ℂ = Category ℂ

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

-- Two pairs are equal if their components are equal.
eqpair : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} {a a' : A} {b b' : B}
  → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
eqpair eqa eqb i = eqa i , eqb i

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    instance
      _ : IsCategory (ℂ .Object) (flip (ℂ .Arrow)) (ℂ .𝟙) (flip (ℂ ._⊕_))
      _ = record { assoc = sym assoc ; ident = swap ident }
        where
          open IsCategory (ℂ .isCategory)

  Opposite : Category ℓ ℓ'
  Opposite =
    record
      { Object = ℂ .Object
      ; Arrow = flip (ℂ .Arrow)
      ; 𝟙 = ℂ .𝟙
      ; _⊕_ = flip (ℂ ._⊕_)
      }

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
