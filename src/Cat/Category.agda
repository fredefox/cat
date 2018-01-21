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

postulate undefined : {ℓ : Level} → {A : Set ℓ} → A

record Category {ℓ ℓ'} : Set (lsuc (ℓ' ⊔ ℓ)) where
  -- adding no-eta-equality can speed up type-checking.
  no-eta-equality
  field
    Object : Set ℓ
    Arrow  : Object → Object → Set ℓ'
    𝟙      : {o : Object} → Arrow o o
    _⊕_    : { a b c : Object } → Arrow b c → Arrow a b → Arrow a c
    assoc : { A B C D : Object } { f : Arrow A B } { g : Arrow B C } { h : Arrow C D }
      → h ⊕ (g ⊕ f) ≡ (h ⊕ g) ⊕ f
    ident  : { A B : Object } { f : Arrow A B }
      → f ⊕ 𝟙 ≡ f × 𝟙 ⊕ f ≡ f
  infixl 45 _⊕_
  domain : { a b : Object } → Arrow a b → Object
  domain {a = a} _ = a
  codomain : { a b : Object } → Arrow a b → Object
  codomain {b = b} _ = b

open Category public

module _ {ℓ ℓ' : Level} {ℂ : Category {ℓ} {ℓ'}} { A B : ℂ .Object } where
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
    g₀              ≡⟨ sym (fst ℂ.ident) ⟩
    g₀ + ℂ.𝟙        ≡⟨ cong (_+_ g₀) (sym right-inv) ⟩
    g₀ + (f + f-)   ≡⟨ ℂ.assoc ⟩
    (g₀ + f) + f-   ≡⟨ cong (λ x → x + f-) eq ⟩
    (g₁ + f) + f-   ≡⟨ sym ℂ.assoc ⟩
    g₁ + (f + f-)   ≡⟨ cong (_+_ g₁) right-inv ⟩
    g₁ + ℂ.𝟙        ≡⟨ fst ℂ.ident ⟩
    g₁              ∎

  iso-is-mono : ∀ {X} (f : ℂ.Arrow A B ) → Isomorphism f → Monomorphism {X = X} f
  iso-is-mono f (f- , (left-inv , right-inv)) g₀ g₁ eq =
    begin
    g₀            ≡⟨ sym (snd ℂ.ident) ⟩
    ℂ.𝟙 + g₀      ≡⟨ cong (λ x → x + g₀) (sym left-inv) ⟩
    (f- + f) + g₀ ≡⟨ sym ℂ.assoc ⟩
    f- + (f + g₀) ≡⟨ cong (_+_ f-) eq ⟩
    f- + (f + g₁) ≡⟨ ℂ.assoc ⟩
    (f- + f) + g₁ ≡⟨ cong (λ x → x + g₁) left-inv ⟩
    ℂ.𝟙 + g₁      ≡⟨ snd ℂ.ident ⟩
    g₁            ∎

  iso-is-epi-mono : ∀ {X} (f : ℂ.Arrow A B ) → Isomorphism f → Epimorphism {X = X} f × Monomorphism {X = X} f
  iso-is-epi-mono f iso = iso-is-epi f iso , iso-is-mono f iso

{-
epi-mono-is-not-iso : ∀ {ℓ ℓ'} → ¬ ((ℂ : Category {ℓ} {ℓ'}) {A B X : Object ℂ} (f : Arrow ℂ A B ) → Epimorphism {ℂ = ℂ} {X = X} f → Monomorphism {ℂ = ℂ} {X = X} f → Isomorphism {ℂ = ℂ} f)
epi-mono-is-not-iso f =
  let k = f {!!} {!!} {!!} {!!}
  in {!!}
-}

-- Isomorphism of objects
_≅_ : { ℓ ℓ' : Level } → { ℂ : Category {ℓ} {ℓ'} } → ( A B : Object ℂ ) → Set ℓ'
_≅_ {ℂ = ℂ} A B = Σ[ f ∈ ℂ .Arrow A B ] (Isomorphism {ℂ = ℂ} f)

IsProduct : ∀ {ℓ ℓ'} (ℂ : Category {ℓ} {ℓ'}) {A B obj : Object ℂ} (π₁ : Arrow ℂ obj A) (π₂ : Arrow ℂ obj B) → Set (ℓ ⊔ ℓ')
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

record Product {ℓ ℓ' : Level} {ℂ : Category {ℓ} {ℓ'}} (A B : ℂ .Object) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    obj : ℂ .Object
    proj₁ : ℂ .Arrow obj A
    proj₂ : ℂ .Arrow obj B
    {{isProduct}} : IsProduct ℂ proj₁ proj₂

mutual
  catProduct : {ℓ : Level} → (C D : Category {ℓ} {ℓ}) → Category {ℓ} {ℓ}
  catProduct C D =
    record
      { Object = C.Object × D.Object
      -- Why does "outlining   with `arrowProduct` not work?
      ; Arrow = λ {(c , d) (c' , d') → Arrow C c c' × Arrow D d d'}
      ; 𝟙 = C.𝟙 , D.𝟙
      ; _⊕_ = λ { (bc∈C , bc∈D) (ab∈C , ab∈D) → bc∈C C.⊕ ab∈C , bc∈D D.⊕ ab∈D}
      ; assoc = eqpair C.assoc D.assoc
      ; ident =
        let (Cl , Cr) = C.ident
            (Dl , Dr) = D.ident
        in eqpair Cl Dl , eqpair Cr Dr
      }
    where
      open module C = Category C
      open module D = Category D
      -- Two pairs are equal if their components are equal.
      eqpair : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} {a a' : A} {b b' : B}
        → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
      eqpair eqa eqb i = eqa i , eqb i


  -- arrowProduct : ∀ {ℓ} {C D : Category {ℓ} {ℓ}} → (Object C) × (Object D) → (Object C) × (Object D) → Set ℓ
  -- arrowProduct = {!!}

  -- Arrows in the product-category
  arrowProduct : ∀ {ℓ} {C D : Category {ℓ} {ℓ}} (c d : Object (catProduct C D)) → Set ℓ
  arrowProduct {C = C} {D = D} (c , d) (c' , d') = Arrow C c c' × Arrow D d d'

Opposite : ∀ {ℓ ℓ'} → Category {ℓ} {ℓ'} → Category {ℓ} {ℓ'}
Opposite ℂ =
  record
    { Object = ℂ.Object
    ; Arrow = λ A B → ℂ.Arrow B A
    ; 𝟙 = ℂ.𝟙
    ; _⊕_ = λ g f → f ℂ.⊕ g
    ; assoc = sym ℂ.assoc
    ; ident = swap ℂ.ident
    }
  where
    open module ℂ = Category ℂ

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

Hom : {ℓ ℓ' : Level} → (ℂ : Category {ℓ} {ℓ'}) → (A B : Object ℂ) → Set ℓ'
Hom ℂ A B = Arrow ℂ A B

module _ {ℓ ℓ' : Level} {ℂ : Category {ℓ} {ℓ'}} where
  HomFromArrow : (A : ℂ .Object) → {B B' : ℂ .Object} → (g : ℂ .Arrow B B')
    → Hom ℂ A B → Hom ℂ A B'
  HomFromArrow _A = _⊕_ ℂ
