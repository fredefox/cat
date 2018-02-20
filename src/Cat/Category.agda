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

-- Thierry: All projections must be `isProp`'s

-- According to definitions 9.1.1 and 9.1.6 in the HoTT book the
-- arrows of a category form a set (arrow-is-set), and there is an
-- equivalence between the equality of objects and isomorphisms
-- (univalent).
record IsCategory {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) : Set (lsuc (ℓa ⊔ ℓb)) where
  open RawCategory ℂ
  module Raw = RawCategory ℂ
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

  propIsInverseOf : ∀ {A B f g} → isProp (IsInverseOf {A} {B} f g)
  propIsInverseOf x y = λ i →
    let
      h : fst x ≡ fst y
      h = arrowIsSet _ _ (fst x) (fst y)
      hh : snd x ≡ snd y
      hh = arrowIsSet _ _ (snd x) (snd y)
    in h i , hh i

  idIso : (A : Object) → A ≅ A
  idIso A = 𝟙 , (𝟙 , ident)

  id-to-iso : (A B : Object) → A ≡ B → A ≅ B
  id-to-iso A B eq = transp (\ i → A ≅ eq i) (idIso A)

  -- TODO: might want to implement isEquiv
  -- differently, there are 3
  -- equivalent formulations in the book.
  Univalent : Set (ℓa ⊔ ℓb)
  Univalent = {A B : Object} → isEquiv (A ≡ B) (A ≅ B) (id-to-iso A B)
  field
    univalent : Univalent

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
  open RawCategory ℂ
  private
    module _ (x y : IsCategory ℂ) where
      module IC = IsCategory
      module X = IsCategory x
      module Y = IsCategory y
      -- ident : X.ident {?} ≡ Y.ident
      ident : (λ _ → IsIdentity 𝟙) [ X.ident ≡ Y.ident ]
      ident = X.propIsIdentity X.ident Y.ident
      -- A version of univalence indexed by the identity proof.
      -- Not of course that since it's defined where `RawCategory ℂ` has been opened
      -- this is specialized to that category.
      Univ : IsIdentity 𝟙 → Set _
      Univ idnt = {A B : Y.Raw.Object} →
        isEquiv (A ≡ B) (A ≅ B)
        (λ eq → transp (λ j → A ≅ eq j) (𝟙 , 𝟙 , idnt))
      done : x ≡ y
      U : ∀ {a : IsIdentity 𝟙} → (λ _ → IsIdentity 𝟙) [ X.ident ≡ a ] → (b : Univ a) → Set _
      U eqwal bbb = (λ i → Univ (eqwal i)) [ X.univalent ≡ bbb ]
      eqUni : U ident Y.univalent
      eqUni = {!!}
      IC.assoc      (done i) = X.propIsAssociative X.assoc Y.assoc i
      IC.ident      (done i) = ident i
      IC.arrowIsSet (done i) = X.propArrowIsSet X.arrowIsSet Y.arrowIsSet i
      IC.univalent  (done i) = eqUni i

  propIsCategory : isProp (IsCategory ℂ)
  propIsCategory = done

record Category (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  field
    raw : RawCategory ℓa ℓb
    {{isCategory}} : IsCategory raw

  open RawCategory raw public

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
