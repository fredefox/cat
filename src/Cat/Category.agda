{-# OPTIONS --allow-unsolved-metas --cubical #-}

module Cat.Category where

open import Agda.Primitive
open import Data.Unit.Base
open import Data.Product renaming
  ( proj₁ to fst
  ; proj₂ to snd
  ; ∃! to ∃!≈
  )
open import Data.Empty
import Function
open import Cubical

∃! : ∀ {a b} {A : Set a}
  → (A → Set b) → Set (a ⊔ b)
∃! = ∃!≈ _≡_

∃!-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃!-syntax = ∃

syntax ∃!-syntax (λ x → B) = ∃![ x ] B

-- Thierry: All projections must be `isProp`'s

-- According to definitions 9.1.1 and 9.1.6 in the HoTT book the
-- arrows of a category form a set (arrow-is-set), and there is an
-- equivalence between the equality of objects and isomorphisms
-- (univalent).
record IsCategory {ℓ ℓ' : Level}
  (Object : Set ℓ)
  (Arrow  : Object → Object → Set ℓ')
  (𝟙      : {o : Object} → Arrow o o)
  (_∘_    : { a b c : Object } → Arrow b c → Arrow a b → Arrow a c)
  : Set (lsuc (ℓ' ⊔ ℓ)) where
  field
    assoc : {A B C D : Object} { f : Arrow A B } { g : Arrow B C } { h : Arrow C D }
      → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    ident : {A B : Object} {f : Arrow A B}
      → f ∘ 𝟙 ≡ f × 𝟙 ∘ f ≡ f
    arrow-is-set : ∀ {A B : Object} → isSet (Arrow A B)

  Isomorphism : ∀ {A B} → (f : Arrow A B) → Set ℓ'
  Isomorphism {A} {B} f = Σ[ g ∈ Arrow B A ] g ∘ f ≡ 𝟙 × f ∘ g ≡ 𝟙

  _≅_ : (A B : Object) → Set ℓ'
  _≅_ A B = Σ[ f ∈ Arrow A B ] (Isomorphism f)

  idIso : (A : Object) → A ≅ A
  idIso A = 𝟙 , (𝟙 , ident)

  id-to-iso : (A B : Object) → A ≡ B → A ≅ B
  id-to-iso A B eq = transp (\ i → A ≅ eq i) (idIso A)


  -- TODO: might want to implement isEquiv differently, there are 3
  -- equivalent formulations in the book.
  field
    univalent : {A B : Object} → isEquiv (A ≡ B) (A ≅ B) (id-to-iso A B)

  module _ {A B : Object} where
    Epimorphism : {X : Object } → (f : Arrow A B) → Set ℓ'
    Epimorphism {X} f = ( g₀ g₁ : Arrow B X ) → g₀ ∘ f ≡ g₁ ∘ f → g₀ ≡ g₁

    Monomorphism : {X : Object} → (f : Arrow A B) → Set ℓ'
    Monomorphism {X} f = ( g₀ g₁ : Arrow X A ) → f ∘ g₀ ≡ f ∘ g₁ → g₀ ≡ g₁

module _  {ℓ} {ℓ'} {Object : Set ℓ}
   {Arrow  : Object → Object → Set ℓ'}
   {𝟙      : {o : Object} → Arrow o o}
   {_⊕_ : { a b c : Object } → Arrow b c → Arrow a b → Arrow a c}
    where

  -- TODO, provable by using arrow-is-set and that isProp (isEquiv _ _ _)
  -- This lemma will be useful to prove the equality of two categories.
  IsCategory-is-prop : isProp (IsCategory Object Arrow 𝟙 _⊕_)
  IsCategory-is-prop = {!!}


record Category (ℓ ℓ' : Level) : Set (lsuc (ℓ' ⊔ ℓ)) where
  -- adding no-eta-equality can speed up type-checking.
  -- ONLY IF you define your categories with copatterns though.
  no-eta-equality
  field
    -- Need something like:
    -- Object : Σ (Set ℓ) isGroupoid
    Object : Set ℓ
    -- And:
    -- Arrow  : Object → Object → Σ (Set ℓ') isSet
    Arrow  : Object → Object → Set ℓ'
    𝟙      : {o : Object} → Arrow o o
    _∘_    : {A B C : Object} → Arrow B C → Arrow A B → Arrow A C
    {{isCategory}} : IsCategory Object Arrow 𝟙 _∘_
  infixl 10 _∘_
  domain : { a b : Object } → Arrow a b → Object
  domain {a = a} _ = a
  codomain : { a b : Object } → Arrow a b → Object
  codomain {b = b} _ = b

open Category

_[_,_] : ∀ {ℓ ℓ'} → (ℂ : Category ℓ ℓ') → (A : ℂ .Object) → (B : ℂ .Object) → Set ℓ'
_[_,_] = Arrow

_[_∘_] : ∀ {ℓ ℓ'} → (ℂ : Category ℓ ℓ') → {A B C : ℂ .Object} → (g : ℂ [ B , C ]) → (f : ℂ [ A , B ]) → ℂ [ A , C ]
_[_∘_] = _∘_

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') {A B obj : Object ℂ} where
  IsProduct : (π₁ : Arrow ℂ obj A) (π₂ : Arrow ℂ obj B) → Set (ℓ ⊔ ℓ')
  IsProduct π₁ π₂
    = ∀ {X : ℂ .Object} (x₁ : ℂ .Arrow X A) (x₂ : ℂ .Arrow X B)
    → ∃![ x ] (ℂ [ π₁ ∘ x ] ≡ x₁ × ℂ [ π₂ ∘ x ] ≡ x₂)

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

  arrowProduct : ∀ {X} → (π₁ : Arrow ℂ X A) (π₂ : Arrow ℂ X B)
    → Arrow ℂ X obj
  arrowProduct π₁ π₂ = fst (isProduct π₁ π₂)

record HasProducts {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  field
    product : ∀ (A B : ℂ .Object) → Product {ℂ = ℂ} A B

  open Product

  objectProduct : (A B : ℂ .Object) → ℂ .Object
  objectProduct A B = Product.obj (product A B)
  -- The product mentioned in awodey in Def 6.1 is not the regular product of arrows.
  -- It's a "parallel" product
  parallelProduct : {A A' B B' : ℂ .Object} → ℂ .Arrow A A' → ℂ .Arrow B B'
    → ℂ .Arrow (objectProduct A B) (objectProduct A' B')
  parallelProduct {A = A} {A' = A'} {B = B} {B' = B'} a b = arrowProduct (product A' B')
    (ℂ [ a ∘ (product A B) .proj₁ ])
    (ℂ [ b ∘ (product A B) .proj₂ ])

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  Opposite : Category ℓ ℓ'
  Opposite =
    record
      { Object = ℂ .Object
      ; Arrow = Function.flip (ℂ .Arrow)
      ; 𝟙 = ℂ .𝟙
      ; _∘_ = Function.flip (ℂ ._∘_)
      ; isCategory = record { assoc = sym assoc ; ident = swap ident
                            ; arrow-is-set = {!!}
                            ; univalent = {!!} }
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
  HomFromArrow _A = ℂ ._∘_

module _ {ℓ ℓ'} (ℂ : Category ℓ ℓ') {{hasProducts : HasProducts ℂ}} where
  open HasProducts hasProducts
  open Product hiding (obj)
  private
    _×p_ : (A B : ℂ .Object) → ℂ .Object
    _×p_ A B = Product.obj (product A B)

  module _ (B C : ℂ .Category.Object) where
    IsExponential : (Cᴮ : ℂ .Object) → ℂ .Arrow (Cᴮ ×p B) C → Set (ℓ ⊔ ℓ')
    IsExponential Cᴮ eval = ∀ (A : ℂ .Object) (f : ℂ .Arrow (A ×p B) C)
      → ∃![ f~ ] (ℂ [ eval ∘ parallelProduct f~ (ℂ .𝟙)] ≡ f)

    record Exponential : Set (ℓ ⊔ ℓ') where
      field
        -- obj ≡ Cᴮ
        obj : ℂ .Object
        eval : ℂ .Arrow ( obj ×p B ) C
        {{isExponential}} : IsExponential obj eval
      -- If I make this an instance-argument then the instance resolution
      -- algorithm goes into an infinite loop. Why?
      exponentialsHaveProducts : HasProducts ℂ
      exponentialsHaveProducts = hasProducts
      transpose : (A : ℂ .Object) → ℂ .Arrow (A ×p B) C → ℂ .Arrow A obj
      transpose A f = fst (isExponential A f)

record HasExponentials {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') {{_ : HasProducts ℂ}} : Set (ℓ ⊔ ℓ') where
  field
    exponent : (A B : ℂ .Object) → Exponential ℂ A B

record CartesianClosed {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  field
    {{hasProducts}}     : HasProducts ℂ
    {{hasExponentials}} : HasExponentials ℂ

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  unique = isContr

  IsInitial : ℂ .Object → Set (ℓa ⊔ ℓb)
  IsInitial I = {X : ℂ .Object} → unique (ℂ .Arrow I X)

  IsTerminal : ℂ .Object → Set (ℓa ⊔ ℓb)
  -- ∃![ ? ] ?
  IsTerminal T = {X : ℂ .Object} → unique (ℂ .Arrow X T)

  Initial : Set (ℓa ⊔ ℓb)
  Initial = Σ (ℂ .Object) IsInitial

  Terminal : Set (ℓa ⊔ ℓb)
  Terminal = Σ (ℂ .Object) IsTerminal
