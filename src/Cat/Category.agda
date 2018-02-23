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

record RawCategory (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  no-eta-equality
  field
    Object : Set ℓa
    Arrow  : Object → Object → Set ℓb
    𝟙      : {A : Object} → Arrow A A
    _∘_    : {A B C : Object} → Arrow B C → Arrow A B → Arrow A C

  infixl 10 _∘_

  domain : { a b : Object } → Arrow a b → Object
  domain {a = a} _ = a

  codomain : { a b : Object } → Arrow a b → Object
  codomain {b = b} _ = b

  IsAssociative : Set (ℓa ⊔ ℓb)
  IsAssociative = ∀ {A B C D} {f : Arrow A B} {g : Arrow B C} {h : Arrow C D}
    → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

  IsIdentity : ({A : Object} → Arrow A A) → Set (ℓa ⊔ ℓb)
  IsIdentity id = {A B : Object} {f : Arrow A B}
    → f ∘ id ≡ f × id ∘ f ≡ f

  ArrowsAreSets : Set (ℓa ⊔ ℓb)
  ArrowsAreSets = ∀ {A B : Object} → isSet (Arrow A B)

  IsInverseOf : ∀ {A B} → (Arrow A B) → (Arrow B A) → Set ℓb
  IsInverseOf = λ f g → g ∘ f ≡ 𝟙 × f ∘ g ≡ 𝟙

  Isomorphism : ∀ {A B} → (f : Arrow A B) → Set ℓb
  Isomorphism {A} {B} f = Σ[ g ∈ Arrow B A ] IsInverseOf f g

  _≅_ : (A B : Object) → Set ℓb
  _≅_ A B = Σ[ f ∈ Arrow A B ] (Isomorphism f)

  module _ {A B : Object} where
    Epimorphism : {X : Object } → (f : Arrow A B) → Set ℓb
    Epimorphism {X} f = ( g₀ g₁ : Arrow B X ) → g₀ ∘ f ≡ g₁ ∘ f → g₀ ≡ g₁

    Monomorphism : {X : Object} → (f : Arrow A B) → Set ℓb
    Monomorphism {X} f = ( g₀ g₁ : Arrow X A ) → f ∘ g₀ ≡ f ∘ g₁ → g₀ ≡ g₁

  IsInitial  : Object → Set (ℓa ⊔ ℓb)
  IsInitial  I = {X : Object} → isContr (Arrow I X)

  IsTerminal : Object → Set (ℓa ⊔ ℓb)
  IsTerminal T = {X : Object} → isContr (Arrow X T)

  Initial  : Set (ℓa ⊔ ℓb)
  Initial  = Σ Object IsInitial

  Terminal : Set (ℓa ⊔ ℓb)
  Terminal = Σ Object IsTerminal

-- Univalence is indexed by a raw category as well as an identity proof.
module Univalence {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) where
  open RawCategory ℂ
  module _ (isIdentity : IsIdentity 𝟙) where
    idIso : (A : Object) → A ≅ A
    idIso A = 𝟙 , (𝟙 , isIdentity)

    -- Lemma 9.1.4 in [HoTT]
    id-to-iso : (A B : Object) → A ≡ B → A ≅ B
    id-to-iso A B eq = transp (\ i → A ≅ eq i) (idIso A)

    -- TODO: might want to implement isEquiv
    -- differently, there are 3
    -- equivalent formulations in the book.
    Univalent : Set (ℓa ⊔ ℓb)
    Univalent = {A B : Object} → isEquiv (A ≡ B) (A ≅ B) (id-to-iso A B)

record IsCategory {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) : Set (lsuc (ℓa ⊔ ℓb)) where
  open RawCategory ℂ
  open Univalence ℂ public
  field
    isAssociative : IsAssociative
    isIdentity    : IsIdentity 𝟙
    arrowsAreSets : ArrowsAreSets
    univalent     : Univalent isIdentity

-- `IsCategory` is a mere proposition.
module _ {ℓa ℓb : Level} {C : RawCategory ℓa ℓb} where
  open RawCategory C
  module _ (ℂ : IsCategory C) where
    open IsCategory ℂ
    open import Cubical.NType
    open import Cubical.NType.Properties

    propIsAssociative : isProp IsAssociative
    propIsAssociative x y i = arrowsAreSets _ _ x y i

    propIsIdentity : ∀ {f : ∀ {A} → Arrow A A} → isProp (IsIdentity f)
    propIsIdentity a b i
      = arrowsAreSets _ _ (fst a) (fst b) i
      , arrowsAreSets _ _ (snd a) (snd b) i

    propArrowIsSet : isProp (∀ {A B} → isSet (Arrow A B))
    propArrowIsSet a b i = isSetIsProp a b i

    propIsInverseOf : ∀ {A B f g} → isProp (IsInverseOf {A} {B} f g)
    propIsInverseOf x y = λ i →
      let
        h : fst x ≡ fst y
        h = arrowsAreSets _ _ (fst x) (fst y)
        hh : snd x ≡ snd y
        hh = arrowsAreSets _ _ (snd x) (snd y)
      in h i , hh i

    module _ {A B : Object} {f : Arrow A B} where
      isoIsProp : isProp (Isomorphism f)
      isoIsProp a@(g , η , ε) a'@(g' , η' , ε') =
        lemSig (λ g → propIsInverseOf) a a' geq
          where
            open Cubical.NType.Properties
            geq : g ≡ g'
            geq = begin
              g            ≡⟨ sym (fst isIdentity) ⟩
              g ∘ 𝟙        ≡⟨ cong (λ φ → g ∘ φ) (sym ε') ⟩
              g ∘ (f ∘ g') ≡⟨ isAssociative ⟩
              (g ∘ f) ∘ g' ≡⟨ cong (λ φ → φ ∘ g') η ⟩
              𝟙 ∘ g'       ≡⟨ snd isIdentity ⟩
              g'           ∎

    propUnivalent : isProp (Univalent isIdentity)
    propUnivalent a b i = propPi (λ iso → propHasLevel ⟨-2⟩) a b i

  private
    module _ (x y : IsCategory C) where
      module IC = IsCategory
      module X = IsCategory x
      module Y = IsCategory y
      open Univalence C
      -- In a few places I use the result of propositionality of the various
      -- projections of `IsCategory` - I've arbitrarily chosed to use this
      -- result from `x : IsCategory C`. I don't know which (if any) possibly
      -- adverse effects this may have.
      isIdentity : (λ _ → IsIdentity 𝟙) [ X.isIdentity ≡ Y.isIdentity ]
      isIdentity = propIsIdentity x X.isIdentity Y.isIdentity
      done : x ≡ y
      U : ∀ {a : IsIdentity 𝟙}
        → (λ _ → IsIdentity 𝟙) [ X.isIdentity ≡ a ]
        → (b : Univalent a)
        → Set _
      U eqwal bbb =
        (λ i → Univalent (eqwal i))
        [ X.univalent ≡ bbb ]
      P : (y : IsIdentity 𝟙)
        → (λ _ → IsIdentity 𝟙) [ X.isIdentity ≡ y ] → Set _
      P y eq = ∀ (b' : Univalent y) → U eq b'
      helper : ∀ (b' : Univalent X.isIdentity)
        → (λ _ → Univalent X.isIdentity) [ X.univalent ≡ b' ]
      helper univ = propUnivalent x X.univalent univ
      foo = pathJ P helper Y.isIdentity isIdentity
      eqUni : U isIdentity Y.univalent
      eqUni = foo Y.univalent
      IC.isAssociative      (done i) = propIsAssociative x X.isAssociative Y.isAssociative i
      IC.isIdentity      (done i) = isIdentity i
      IC.arrowsAreSets (done i) = propArrowIsSet x X.arrowsAreSets Y.arrowsAreSets i
      IC.univalent  (done i) = eqUni i

  propIsCategory : isProp (IsCategory C)
  propIsCategory = done

record Category (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  field
    raw : RawCategory ℓa ℓb
    {{isCategory}} : IsCategory raw

  open RawCategory raw public
  open IsCategory isCategory public

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Category ℂ
  _[_,_] : (A : Object) → (B : Object) → Set ℓb
  _[_,_] = Arrow

  _[_∘_] : {A B C : Object} → (g : Arrow B C) → (f : Arrow A B) → Arrow A C
  _[_∘_] = _∘_

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    open Category ℂ

    OpRaw : RawCategory ℓa ℓb
    RawCategory.Object OpRaw = Object
    RawCategory.Arrow OpRaw = Function.flip Arrow
    RawCategory.𝟙 OpRaw = 𝟙
    RawCategory._∘_ OpRaw = Function.flip _∘_

    OpIsCategory : IsCategory OpRaw
    IsCategory.isAssociative OpIsCategory = sym isAssociative
    IsCategory.isIdentity OpIsCategory = swap isIdentity
    IsCategory.arrowsAreSets OpIsCategory = arrowsAreSets
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
    isAssociative (rawIsCat i) = IsCat.isAssociative
    isIdentity (rawIsCat i) = IsCat.isIdentity
    arrowsAreSets (rawIsCat i) = IsCat.arrowsAreSets
    univalent (rawIsCat i) = IsCat.univalent

  Opposite-is-involution : Opposite (Opposite ℂ) ≡ ℂ
  raw (Opposite-is-involution i) = rawOp i
  isCategory (Opposite-is-involution i) = rawIsCat i
