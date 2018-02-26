-- | Univalent categories
--
-- This module defines:
--
-- Categories
-- ==========
--
-- Types
-- ------
--
-- Object, Arrow
--
-- Data
-- ----
-- 𝟙; the identity arrow
-- _∘_; function composition
--
-- Laws
-- ----
--
-- associativity, identity, arrows form sets, univalence.
--
-- Lemmas
-- ------
--
-- Propositionality for all laws about the category.
--
-- TODO: An equality principle for categories that focuses on the pure data-part.
--
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

-----------------
-- * Utilities --
-----------------

-- | Unique existensials.
∃! : ∀ {a b} {A : Set a}
  → (A → Set b) → Set (a ⊔ b)
∃! = ∃!≈ _≡_

∃!-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃!-syntax = ∃

syntax ∃!-syntax (λ x → B) = ∃![ x ] B

-----------------
-- * Categories --
-----------------

-- | Raw categories
--
-- This record desribes the data that a category consist of as well as some laws
-- about these. The laws defined are the types the propositions - not the
-- witnesses to them!
record RawCategory (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  no-eta-equality
  field
    Object : Set ℓa
    Arrow  : Object → Object → Set ℓb
    𝟙      : {A : Object} → Arrow A A
    _∘_    : {A B C : Object} → Arrow B C → Arrow A B → Arrow A C

  infixl 10 _∘_

  -- | Operations on data

  domain : { a b : Object } → Arrow a b → Object
  domain {a = a} _ = a

  codomain : { a b : Object } → Arrow a b → Object
  codomain {b = b} _ = b

  _>>>_ : {A B C : Object} → (Arrow A B) → (Arrow B C) → Arrow A C
  f >>> g = g ∘ f

  -- | Laws about the data

  -- TODO: It seems counter-intuitive that the normal-form is on the
  -- right-hand-side.
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

    Univalent : Set (ℓa ⊔ ℓb)
    Univalent = {A B : Object} → isEquiv (A ≡ B) (A ≅ B) (id-to-iso A B)

-- | The mere proposition of being a category.
--
-- Also defines a few lemmas:
--
--     iso-is-epi  : Isomorphism f → Epimorphism {X = X} f
--     iso-is-mono : Isomorphism f → Monomorphism {X = X} f
--
record IsCategory {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) : Set (lsuc (ℓa ⊔ ℓb)) where
  open RawCategory ℂ public
  open Univalence ℂ public
  field
    isAssociative : IsAssociative
    isIdentity    : IsIdentity 𝟙
    arrowsAreSets : ArrowsAreSets
    univalent     : Univalent isIdentity

  -- Some common lemmas about categories.
  module _ {A B : Object} {X : Object} (f : Arrow A B) where
    iso-is-epi : Isomorphism f → Epimorphism {X = X} f
    iso-is-epi (f- , left-inv , right-inv) g₀ g₁ eq = begin
      g₀              ≡⟨ sym (fst isIdentity) ⟩
      g₀ ∘ 𝟙          ≡⟨ cong (_∘_ g₀) (sym right-inv) ⟩
      g₀ ∘ (f ∘ f-)   ≡⟨ isAssociative ⟩
      (g₀ ∘ f) ∘ f-   ≡⟨ cong (λ φ → φ ∘ f-) eq ⟩
      (g₁ ∘ f) ∘ f-   ≡⟨ sym isAssociative ⟩
      g₁ ∘ (f ∘ f-)   ≡⟨ cong (_∘_ g₁) right-inv ⟩
      g₁ ∘ 𝟙          ≡⟨ fst isIdentity ⟩
      g₁              ∎

    iso-is-mono : Isomorphism f → Monomorphism {X = X} f
    iso-is-mono (f- , (left-inv , right-inv)) g₀ g₁ eq =
      begin
      g₀            ≡⟨ sym (snd isIdentity) ⟩
      𝟙 ∘ g₀        ≡⟨ cong (λ φ → φ ∘ g₀) (sym left-inv) ⟩
      (f- ∘ f) ∘ g₀ ≡⟨ sym isAssociative ⟩
      f- ∘ (f ∘ g₀) ≡⟨ cong (_∘_ f-) eq ⟩
      f- ∘ (f ∘ g₁) ≡⟨ isAssociative ⟩
      (f- ∘ f) ∘ g₁ ≡⟨ cong (λ φ → φ ∘ g₁) left-inv ⟩
      𝟙 ∘ g₁        ≡⟨ snd isIdentity ⟩
      g₁            ∎

    iso-is-epi-mono : Isomorphism f → Epimorphism {X = X} f × Monomorphism {X = X} f
    iso-is-epi-mono iso = iso-is-epi iso , iso-is-mono iso

-- | Propositionality of being a category
--
-- Proves that all projections of `IsCategory` are mere propositions as well as
-- `IsCategory` itself being a mere proposition.
module _ {ℓa ℓb : Level} {C : RawCategory ℓa ℓb} where
  open RawCategory C
  module _ (ℂ : IsCategory C) where
    open IsCategory ℂ using (isAssociative ; arrowsAreSets ; isIdentity ; Univalent)
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

-- | Univalent categories
--
-- Just bundles up the data with witnesses inhabting the propositions.
record Category (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  field
    raw : RawCategory ℓa ℓb
    {{isCategory}} : IsCategory raw

  open IsCategory isCategory public

-- | Syntax for arrows- and composition in a given category.
module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Category ℂ
  _[_,_] : (A : Object) → (B : Object) → Set ℓb
  _[_,_] = Arrow

  _[_∘_] : {A B C : Object} → (g : Arrow B C) → (f : Arrow A B) → Arrow A C
  _[_∘_] = _∘_

-- | The opposite category
--
-- The opposite category is the category where the direction of the arrows are
-- flipped.
module Opposite {ℓa ℓb : Level} where
  module _ (ℂ : Category ℓa ℓb) where
    open Category ℂ
    private
      opRaw : RawCategory ℓa ℓb
      RawCategory.Object opRaw = Object
      RawCategory.Arrow  opRaw = Function.flip Arrow
      RawCategory.𝟙      opRaw = 𝟙
      RawCategory._∘_    opRaw = Function.flip _∘_

      opIsCategory : IsCategory opRaw
      IsCategory.isAssociative opIsCategory = sym isAssociative
      IsCategory.isIdentity    opIsCategory = swap isIdentity
      IsCategory.arrowsAreSets opIsCategory = arrowsAreSets
      IsCategory.univalent     opIsCategory = {!!}

    opposite : Category ℓa ℓb
    raw opposite = opRaw
    Category.isCategory opposite = opIsCategory

  -- As demonstrated here a side-effect of having no-eta-equality on constructors
  -- means that we need to pick things apart to show that things are indeed
  -- definitionally equal. I.e; a thing that would normally be provable in one
  -- line now takes 13!! Admittedly it's a simple proof.
  module _ {ℂ : Category ℓa ℓb} where
    open Category ℂ
    private
      -- Since they really are definitionally equal we just need to pick apart
      -- the data-type.
      rawInv : Category.raw (opposite (opposite ℂ)) ≡ raw
      RawCategory.Object   (rawInv _) = Object
      RawCategory.Arrow    (rawInv _) = Arrow
      RawCategory.𝟙        (rawInv _) = 𝟙
      RawCategory._∘_      (rawInv _) = _∘_

    -- TODO: Define and use Monad≡
    oppositeIsInvolution : opposite (opposite ℂ) ≡ ℂ
    Category.raw        (oppositeIsInvolution i) = rawInv i
    Category.isCategory (oppositeIsInvolution x) = {!!}

open Opposite public
