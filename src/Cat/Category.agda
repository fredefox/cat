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
open import Cubical.NType.Properties using ( propIsEquiv )

open import Cat.Wishlist

∃! : ∀ {a b} {A : Set a}
  → (A → Set b) → Set (a ⊔ b)
∃! = ∃!≈ _≡_

∃!-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃!-syntax = ∃

syntax ∃!-syntax (λ x → B) = ∃![ x ] B

record RawCategory (ℓ ℓ' : Level) : Set (lsuc (ℓ' ⊔ ℓ)) where
  no-eta-equality
  field
    Object : Set ℓ
    Arrow  : Object → Object → Set ℓ'
    𝟙      : {o : Object} → Arrow o o
    _∘_    : {A B C : Object} → Arrow B C → Arrow A B → Arrow A C
  infixl 10 _∘_
  domain : { a b : Object } → Arrow a b → Object
  domain {a = a} _ = a
  codomain : { a b : Object } → Arrow a b → Object
  codomain {b = b} _ = b

-- Thierry: All projections must be `isProp`'s

-- According to definitions 9.1.1 and 9.1.6 in the HoTT book the
-- arrows of a category form a set (arrow-is-set), and there is an
-- equivalence between the equality of objects and isomorphisms
-- (univalent).
record IsCategory {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) : Set (lsuc (ℓa ⊔ ℓb)) where
  open RawCategory ℂ
  module Raw = RawCategory ℂ

  IsAssociative : Set (ℓa ⊔ ℓb)
  IsAssociative = ∀ {A B C D} {f : Arrow A B} {g : Arrow B C} {h : Arrow C D}
    → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

  IsIdentity : ({A : Object} → Arrow A A) → Set (ℓa ⊔ ℓb)
  IsIdentity id = {A B : Object} {f : Arrow A B}
    → f ∘ id ≡ f × id ∘ f ≡ f

  field
    assoc : IsAssociative
    ident : IsIdentity 𝟙
    arrowIsSet : ∀ {A B : Object} → isSet (Arrow A B)

  propIsAssociative : isProp IsAssociative
  propIsAssociative x y i = arrowIsSet _ _ x y i

  propIsIdentity : ∀ {f : ∀ {A} → Arrow A A} → isProp (IsIdentity f)
  propIsIdentity a b i
    = arrowIsSet _ _ (fst a) (fst b) i
    , arrowIsSet _ _ (snd a) (snd b) i

  propArrowIsSet : isProp (∀ {A B} → isSet (Arrow A B))
  propArrowIsSet a b i = isSetIsProp a b i

  IsInverseOf : ∀ {A B} → (Arrow A B) → (Arrow B A) → Set ℓb
  IsInverseOf = λ f g → g ∘ f ≡ 𝟙 × f ∘ g ≡ 𝟙

  propIsInverseOf : ∀ {A B f g} → isProp (IsInverseOf {A} {B} f g)
  propIsInverseOf x y = λ i →
    let
      h : fst x ≡ fst y
      h = arrowIsSet _ _ (fst x) (fst y)
      hh : snd x ≡ snd y
      hh = arrowIsSet _ _ (snd x) (snd y)
    in h i , hh i

  Isomorphism : ∀ {A B} → (f : Arrow A B) → Set ℓb
  Isomorphism {A} {B} f = Σ[ g ∈ Arrow B A ] IsInverseOf f g

  inverse : ∀ {A B} {f : Arrow A B} → Isomorphism f → Arrow B A
  inverse iso = fst iso

  _≅_ : (A B : Object) → Set ℓb
  _≅_ A B = Σ[ f ∈ Arrow A B ] (Isomorphism f)

  idIso : (A : Object) → A ≅ A
  idIso A = 𝟙 , (𝟙 , ident)

  id-to-iso : (A B : Object) → A ≡ B → A ≅ B
  id-to-iso A B eq = transp (\ i → A ≅ eq i) (idIso A)

  -- TODO: might want to implement isEquiv differently, there are 3
  -- equivalent formulations in the book.
  Univalent : Set (ℓa ⊔ ℓb)
  Univalent = {A B : Object} → isEquiv (A ≡ B) (A ≅ B) (id-to-iso A B)
  field
    univalent : Univalent

  module _ {A B : Object} where
    Epimorphism : {X : Object } → (f : Arrow A B) → Set ℓb
    Epimorphism {X} f = ( g₀ g₁ : Arrow B X ) → g₀ ∘ f ≡ g₁ ∘ f → g₀ ≡ g₁

    Monomorphism : {X : Object} → (f : Arrow A B) → Set ℓb
    Monomorphism {X} f = ( g₀ g₁ : Arrow X A ) → f ∘ g₀ ≡ f ∘ g₁ → g₀ ≡ g₁

  module _ {A B : Object} {f : Arrow A B} where
    isoIsProp : isProp (Isomorphism f)
    isoIsProp a@(g , η , ε) a'@(g' , η' , ε') =
      lemSig (λ g → propIsInverseOf) a a' geq
      where
        open Cubical.NType.Properties
        geq : g ≡ g'
        geq = begin
          g            ≡⟨ sym (fst ident) ⟩
          g ∘ 𝟙        ≡⟨ cong (λ φ → g ∘ φ) (sym ε') ⟩
          g ∘ (f ∘ g') ≡⟨ assoc ⟩
          (g ∘ f) ∘ g' ≡⟨ cong (λ φ → φ ∘ g') η ⟩
          𝟙 ∘ g'       ≡⟨ snd ident ⟩
          g'           ∎

module _ {ℓa ℓb : Level} {C : RawCategory ℓa ℓb} {ℂ : IsCategory C} where
  open IsCategory ℂ
  open import Cubical.NType
  open import Cubical.NType.Properties

  propUnivalent : isProp Univalent
  propUnivalent a b i = propPi (λ iso → propHasLevel ⟨-2⟩) a b i

module _ {ℓa} {ℓb} {ℂ : RawCategory ℓa ℓb} where
  -- TODO, provable by using  arrow-is-set and that isProp (isEquiv _ _ _)
  -- This lemma will be useful to prove the equality of two categories.
  IsCategory-is-prop : isProp (IsCategory ℂ)
  IsCategory-is-prop x y i = record
    -- Why choose `x`'s `propIsAssociative`?
    -- Well, probably it could be pulled out of the record.
    { assoc = x.propIsAssociative x.assoc y.assoc i
    ; ident = x.propIsIdentity x.ident y.ident i
    ; arrowIsSet = x.propArrowIsSet x.arrowIsSet y.arrowIsSet i
    ; univalent = eqUni i
    }
    where
      module x = IsCategory x
      module y = IsCategory y
      xuni : x.Univalent
      xuni = x.univalent
      yuni : y.Univalent
      yuni = y.univalent
      open RawCategory ℂ
      T :  I → Set (ℓa ⊔ ℓb)
      T i = {A B : Object} →
        isEquiv (A ≡ B) (A x.≅ B)
          (λ A≡B →
            transp
            (λ j →
            Σ-syntax (Arrow A (A≡B j))
            (λ f → Σ-syntax (Arrow (A≡B j) A) (λ g → g ∘ f ≡ 𝟙 × f ∘ g ≡ 𝟙)))
            ( 𝟙
            , 𝟙
            , x.propIsIdentity x.ident y.ident i
            )
          )
      open Cubical.NType.Properties
      test : (λ _ → x.Univalent) [ xuni ≡ xuni ]
      test = refl
      t = {!!}
      P : (uni : x.Univalent) → xuni ≡ uni → Set (ℓa ⊔ ℓb)
      P = {!!}
      eqUni : T [ xuni ≡ yuni ]
      eqUni = pathJprop {x = x.Univalent} P {!!} i


record Category (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  field
    raw : RawCategory ℓa ℓb
    {{isCategory}} : IsCategory raw

  private
    module ℂ = RawCategory raw

  Object : Set ℓa
  Object = ℂ.Object

  Arrow = ℂ.Arrow

  𝟙 = ℂ.𝟙

  _∘_ = ℂ._∘_

  _[_,_] : (A : Object) → (B : Object) → Set ℓb
  _[_,_] = ℂ.Arrow

  _[_∘_] : {A B C : Object} → (g : ℂ.Arrow B C) → (f : ℂ.Arrow A B) → ℂ.Arrow A C
  _[_∘_] = ℂ._∘_


module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    open Category ℂ

    OpRaw : RawCategory ℓa ℓb
    RawCategory.Object OpRaw = Object
    RawCategory.Arrow OpRaw = Function.flip Arrow
    RawCategory.𝟙 OpRaw = 𝟙
    RawCategory._∘_ OpRaw = Function.flip _∘_

    open IsCategory isCategory

    OpIsCategory : IsCategory OpRaw
    IsCategory.assoc OpIsCategory = sym assoc
    IsCategory.ident OpIsCategory = swap ident
    IsCategory.arrowIsSet OpIsCategory = arrowIsSet
    IsCategory.univalent OpIsCategory = {!!}

  Opposite : Category ℓa ℓb
  raw Opposite = OpRaw
  Category.isCategory Opposite = OpIsCategory

-- As demonstrated here a side-effect of having no-eta-equality on constructors
-- means that we need to pick things apart to show that things are indeed
-- definitionally equal. I.e; a thing that would normally be provable in one
-- line now takes more than 20!!
module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} where
  private
    open RawCategory
    module C = Category ℂ
    rawOp : Category.raw (Opposite (Opposite ℂ)) ≡ Category.raw ℂ
    Object (rawOp _) = C.Object
    Arrow (rawOp _) = C.Arrow
    𝟙 (rawOp _) = C.𝟙
    _∘_ (rawOp _) = C._∘_
    open Category
    open IsCategory
    module IsCat = IsCategory (ℂ .isCategory)
    rawIsCat : (i : I) → IsCategory (rawOp i)
    assoc (rawIsCat i) = IsCat.assoc
    ident (rawIsCat i) = IsCat.ident
    arrowIsSet (rawIsCat i) = IsCat.arrowIsSet
    univalent (rawIsCat i) = IsCat.univalent

  Opposite-is-involution : Opposite (Opposite ℂ) ≡ ℂ
  raw (Opposite-is-involution i) = rawOp i
  isCategory (Opposite-is-involution i) = rawIsCat i

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Category
  unique = isContr

  IsInitial : Object ℂ → Set (ℓa ⊔ ℓb)
  IsInitial I = {X : Object ℂ} → unique (ℂ [ I , X ])

  IsTerminal : Object ℂ → Set (ℓa ⊔ ℓb)
  -- ∃![ ? ] ?
  IsTerminal T = {X : Object ℂ} → unique (ℂ [ X , T ])

  Initial : Set (ℓa ⊔ ℓb)
  Initial = Σ (Object ℂ) IsInitial

  Terminal : Set (ℓa ⊔ ℓb)
  Terminal = Σ (Object ℂ) IsTerminal
