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
-- identity; the identity arrow
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
{-# OPTIONS --allow-unsolved-metas --cubical #-}

module Cat.Category where

open import Cat.Prelude
open import Cat.Equivalence as Equivalence renaming (_≅_ to _≈_ ; Isomorphism to TypeIsomorphism) hiding (preorder≅)

import Function

------------------
-- * Categories --
------------------

-- | Raw categories
--
-- This record desribes the data that a category consist of as well as some laws
-- about these. The laws defined are the types the propositions - not the
-- witnesses to them!
record RawCategory (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  no-eta-equality
  field
    Object   : Set ℓa
    Arrow    : Object → Object → Set ℓb
    identity : {A : Object} → Arrow A A
    _∘_      : {A B C : Object} → Arrow B C → Arrow A B → Arrow A C

  infixl 10 _∘_ _>>>_

  -- | Operations on data

  domain : {a b : Object} → Arrow a b → Object
  domain {a} _ = a

  codomain : {a b : Object} → Arrow a b → Object
  codomain {b = b} _ = b

  _>>>_ : {A B C : Object} → (Arrow A B) → (Arrow B C) → Arrow A C
  f >>> g = g ∘ f

  -- | Laws about the data

  -- FIXME It seems counter-intuitive that the normal-form is on the
  -- right-hand-side.
  IsAssociative : Set (ℓa ⊔ ℓb)
  IsAssociative = ∀ {A B C D} {f : Arrow A B} {g : Arrow B C} {h : Arrow C D}
    → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

  IsIdentity : ({A : Object} → Arrow A A) → Set (ℓa ⊔ ℓb)
  IsIdentity id = {A B : Object} {f : Arrow A B}
    → id ∘ f ≡ f × f ∘ id ≡ f

  ArrowsAreSets : Set (ℓa ⊔ ℓb)
  ArrowsAreSets = ∀ {A B : Object} → isSet (Arrow A B)

  IsInverseOf : ∀ {A B} → (Arrow A B) → (Arrow B A) → Set ℓb
  IsInverseOf = λ f g → g ∘ f ≡ identity × f ∘ g ≡ identity

  Isomorphism : ∀ {A B} → (f : Arrow A B) → Set ℓb
  Isomorphism {A} {B} f = Σ[ g ∈ Arrow B A ] IsInverseOf f g

  _≅_ : (A B : Object) → Set ℓb
  _≅_ A B = Σ[ f ∈ Arrow A B ] (Isomorphism f)

  module _ {A B : Object} where
    Epimorphism : {X : Object } → (f : Arrow A B) → Set ℓb
    Epimorphism {X} f = (g₀ g₁ : Arrow B X) → g₀ ∘ f ≡ g₁ ∘ f → g₀ ≡ g₁

    Monomorphism : {X : Object} → (f : Arrow A B) → Set ℓb
    Monomorphism {X} f = (g₀ g₁ : Arrow X A) → f ∘ g₀ ≡ f ∘ g₁ → g₀ ≡ g₁

  IsInitial  : Object → Set (ℓa ⊔ ℓb)
  IsInitial  I = {X : Object} → isContr (Arrow I X)

  IsTerminal : Object → Set (ℓa ⊔ ℓb)
  IsTerminal T = {X : Object} → isContr (Arrow X T)

  Initial  : Set (ℓa ⊔ ℓb)
  Initial  = Σ Object IsInitial

  Terminal : Set (ℓa ⊔ ℓb)
  Terminal = Σ Object IsTerminal

  -- | Univalence is indexed by a raw category as well as an identity proof.
  module Univalence (isIdentity : IsIdentity identity) where
    -- | The identity isomorphism
    idIso : (A : Object) → A ≅ A
    idIso A = identity , identity , isIdentity

    -- | Extract an isomorphism from an equality
    --
    -- [HoTT §9.1.4]
    idToIso : (A B : Object) → A ≡ B → A ≅ B
    idToIso A B eq = transp (\ i → A ≅ eq i) (idIso A)

    Univalent : Set (ℓa ⊔ ℓb)
    Univalent = {A B : Object} → isEquiv (A ≡ B) (A ≅ B) (idToIso A B)

    import Cat.Equivalence as E
    open E public using () renaming (Isomorphism to TypeIsomorphism)

    univalenceFromIsomorphism : {A B : Object}
      → TypeIsomorphism (idToIso A B) → isEquiv (A ≡ B) (A ≅ B) (idToIso A B)
    univalenceFromIsomorphism = fromIso _ _

    -- A perhaps more readable version of univalence:
    Univalent≃ = {A B : Object} → (A ≡ B) ≃ (A ≅ B)

    -- | Equivalent formulation of univalence.
    Univalent[Contr] : Set _
    Univalent[Contr] = ∀ A → isContr (Σ[ X ∈ Object ] A ≅ X)

    -- From: Thierry Coquand <Thierry.Coquand@cse.gu.se>
    -- Date: Wed, Mar 21, 2018 at 3:12 PM
    --
    -- This is not so straight-forward so you can assume it
    postulate from[Contr] : Univalent[Contr] → Univalent

    propUnivalent : isProp Univalent
    propUnivalent a b i = propPi (λ iso → propIsContr) a b i

module _ {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) where
  record IsPreCategory : Set (lsuc (ℓa ⊔ ℓb)) where
    open RawCategory ℂ public
    field
      isAssociative : IsAssociative
      isIdentity    : IsIdentity identity
      arrowsAreSets : ArrowsAreSets
    open Univalence isIdentity public

    leftIdentity : {A B : Object} {f : Arrow A B} → identity ∘ f ≡ f
    leftIdentity {A} {B} {f} = fst (isIdentity {A = A} {B} {f})

    rightIdentity : {A B : Object} {f : Arrow A B} → f ∘ identity ≡ f
    rightIdentity {A} {B} {f} = snd (isIdentity {A = A} {B} {f})

    ------------
    -- Lemmas --
    ------------

    -- | Relation between iso- epi- and mono- morphisms.
    module _ {A B : Object} {X : Object} (f : Arrow A B) where
      iso→epi : Isomorphism f → Epimorphism {X = X} f
      iso→epi (f- , left-inv , right-inv) g₀ g₁ eq = begin
        g₀              ≡⟨ sym rightIdentity ⟩
        g₀ ∘ identity   ≡⟨ cong (_∘_ g₀) (sym right-inv) ⟩
        g₀ ∘ (f ∘ f-)   ≡⟨ isAssociative ⟩
        (g₀ ∘ f) ∘ f-   ≡⟨ cong (λ φ → φ ∘ f-) eq ⟩
        (g₁ ∘ f) ∘ f-   ≡⟨ sym isAssociative ⟩
        g₁ ∘ (f ∘ f-)   ≡⟨ cong (_∘_ g₁) right-inv ⟩
        g₁ ∘ identity   ≡⟨ rightIdentity ⟩
        g₁              ∎

      iso→mono : Isomorphism f → Monomorphism {X = X} f
      iso→mono (f- , left-inv , right-inv) g₀ g₁ eq =
        begin
        g₀            ≡⟨ sym leftIdentity ⟩
        identity ∘ g₀ ≡⟨ cong (λ φ → φ ∘ g₀) (sym left-inv) ⟩
        (f- ∘ f) ∘ g₀ ≡⟨ sym isAssociative ⟩
        f- ∘ (f ∘ g₀) ≡⟨ cong (_∘_ f-) eq ⟩
        f- ∘ (f ∘ g₁) ≡⟨ isAssociative ⟩
        (f- ∘ f) ∘ g₁ ≡⟨ cong (λ φ → φ ∘ g₁) left-inv ⟩
        identity ∘ g₁ ≡⟨ leftIdentity ⟩
        g₁            ∎

      iso→epi×mono : Isomorphism f → Epimorphism {X = X} f × Monomorphism {X = X} f
      iso→epi×mono iso = iso→epi iso , iso→mono iso

    propIsAssociative : isProp IsAssociative
    propIsAssociative = propPiImpl (λ _ → propPiImpl (λ _ → propPiImpl (λ _ → propPiImpl (λ _ → propPiImpl (λ _ → propPiImpl (λ _ → propPiImpl λ _ → arrowsAreSets _ _))))))

    propIsIdentity : ∀ {f : ∀ {A} → Arrow A A} → isProp (IsIdentity f)
    propIsIdentity {id} = propPiImpl (λ _ → propPiImpl λ _ → propPiImpl (λ f →
      propSig (arrowsAreSets (id ∘ f) f) λ _ → arrowsAreSets (f ∘ id) f))

    propArrowIsSet : isProp (∀ {A B} → isSet (Arrow A B))
    propArrowIsSet = propPiImpl λ _ → propPiImpl (λ _ → isSetIsProp)

    propIsInverseOf : ∀ {A B f g} → isProp (IsInverseOf {A} {B} f g)
    propIsInverseOf = propSig (arrowsAreSets _ _) (λ _ → arrowsAreSets _ _)

    module _ {A B : Object} {f : Arrow A B} where
      isoIsProp : isProp (Isomorphism f)
      isoIsProp a@(g , η , ε) a'@(g' , η' , ε') =
        lemSig (λ g → propIsInverseOf) a a' geq
          where
            geq : g ≡ g'
            geq = begin
              g             ≡⟨ sym rightIdentity ⟩
              g ∘ identity  ≡⟨ cong (λ φ → g ∘ φ) (sym ε') ⟩
              g ∘ (f ∘ g')  ≡⟨ isAssociative ⟩
              (g ∘ f) ∘ g'  ≡⟨ cong (λ φ → φ ∘ g') η ⟩
              identity ∘ g' ≡⟨ leftIdentity ⟩
              g'            ∎

    propIsInitial : ∀ I → isProp (IsInitial I)
    propIsInitial I x y i {X} = res X i
      where
      module _ (X : Object) where
        open Σ (x {X}) renaming (fst to fx ; snd to cx)
        open Σ (y {X}) renaming (fst to fy ; snd to cy)
        fp : fx ≡ fy
        fp = cx fy
        prop : (x : Arrow I X) → isProp (∀ f → x ≡ f)
        prop x = propPi (λ y → arrowsAreSets x y)
        cp : (λ i → ∀ f → fp i ≡ f) [ cx ≡ cy ]
        cp = lemPropF prop fp
        res : (fx , cx) ≡ (fy , cy)
        res i = fp i , cp i

    propIsTerminal : ∀ T → isProp (IsTerminal T)
    propIsTerminal T x y i {X} = res X i
      where
      module _ (X : Object) where
        open Σ (x {X}) renaming (fst to fx ; snd to cx)
        open Σ (y {X}) renaming (fst to fy ; snd to cy)
        fp : fx ≡ fy
        fp = cx fy
        prop : (x : Arrow X T) → isProp (∀ f → x ≡ f)
        prop x = propPi (λ y → arrowsAreSets x y)
        cp : (λ i → ∀ f → fp i ≡ f) [ cx ≡ cy ]
        cp = lemPropF prop fp
        res : (fx , cx) ≡ (fy , cy)
        res i = fp i , cp i

    module _ where
      private
        trans≅ : Transitive _≅_
        trans≅ (f , f~ , f-inv) (g , g~ , g-inv)
          = g ∘ f
          , f~ ∘ g~
          , ( begin
              (f~ ∘ g~) ∘ (g ∘ f) ≡⟨ isAssociative ⟩
              (f~ ∘ g~) ∘ g ∘ f ≡⟨ cong (λ φ → φ ∘ f) (sym isAssociative) ⟩
              f~ ∘ (g~ ∘ g) ∘ f ≡⟨ cong (λ φ → f~ ∘ φ ∘ f) (fst g-inv) ⟩
              f~ ∘ identity ∘ f ≡⟨ cong (λ φ → φ ∘ f) rightIdentity ⟩
              f~ ∘ f           ≡⟨ fst f-inv ⟩
              identity ∎
            )
          , ( begin
              g ∘ f ∘ (f~ ∘ g~) ≡⟨ isAssociative ⟩
              g ∘ f ∘ f~ ∘ g~ ≡⟨ cong (λ φ → φ ∘ g~) (sym isAssociative) ⟩
              g ∘ (f ∘ f~) ∘ g~ ≡⟨ cong (λ φ → g ∘ φ ∘ g~) (snd f-inv) ⟩
              g ∘ identity ∘ g~ ≡⟨ cong (λ φ → φ ∘ g~) rightIdentity ⟩
              g ∘ g~ ≡⟨ snd g-inv ⟩
              identity ∎
            )
        isPreorder : IsPreorder _≅_
        isPreorder = record { isEquivalence = equalityIsEquivalence ; reflexive = idToIso _ _ ; trans = trans≅ }

      preorder≅ : Preorder _ _ _
      preorder≅ = record { Carrier = Object ; _≈_ = _≡_ ; _∼_ = _≅_ ; isPreorder = isPreorder }

  record PreCategory : Set (lsuc (ℓa ⊔ ℓb)) where
    field
      isPreCategory  : IsPreCategory
    open IsPreCategory isPreCategory public

  -- Definition 9.6.1 in [HoTT]
  record StrictCategory : Set (lsuc (ℓa ⊔ ℓb)) where
    field
      preCategory : PreCategory
    open PreCategory preCategory
    field
      objectsAreSets : isSet Object

  record IsCategory : Set (lsuc (ℓa ⊔ ℓb)) where
    field
      isPreCategory : IsPreCategory
    open IsPreCategory isPreCategory public
    field
      univalent : Univalent

    -- | The formulation of univalence expressed with _≃_ is trivially admissable -
    -- just "forget" the equivalence.
    univalent≃ : Univalent≃
    univalent≃ = _ , univalent

    module _ {A B : Object} where
      iso-to-id : (A ≅ B) → (A ≡ B)
      iso-to-id = fst (toIso _ _ univalent)

    -- | All projections are propositions.
    module Propositionality where
      -- | Terminal objects are propositional - a.k.a uniqueness of terminal
      -- | objects.
      --
      -- Having two terminal objects induces an isomorphism between them - and
      -- because of univalence this is equivalent to equality.
      propTerminal : isProp Terminal
      propTerminal Xt Yt = res
        where
        open Σ Xt renaming (fst to X ; snd to Xit)
        open Σ Yt renaming (fst to Y ; snd to Yit)
        open Σ (Xit {Y}) renaming (fst to Y→X) using ()
        open Σ (Yit {X}) renaming (fst to X→Y) using ()
        -- Need to show `left` and `right`, what we know is that the arrows are
        -- unique. Well, I know that if I compose these two arrows they must give
        -- the identity, since also the identity is the unique such arrow (by X
        -- and Y both being terminal objects.)
        Xprop : isProp (Arrow X X)
        Xprop f g = trans (sym (snd Xit f)) (snd Xit g)
        Yprop : isProp (Arrow Y Y)
        Yprop f g = trans (sym (snd Yit f)) (snd Yit g)
        left : Y→X ∘ X→Y ≡ identity
        left = Xprop _ _
        right : X→Y ∘ Y→X ≡ identity
        right = Yprop _ _
        iso : X ≅ Y
        iso = X→Y , Y→X , left , right
        fromIso' : X ≅ Y → X ≡ Y
        fromIso' = fst (toIso (X ≡ Y) (X ≅ Y) univalent)
        p0 : X ≡ Y
        p0 = fromIso' iso
        p1 : (λ i → IsTerminal (p0 i)) [ Xit ≡ Yit ]
        p1 = lemPropF propIsTerminal p0
        res : Xt ≡ Yt
        res i = p0 i , p1 i

      -- Merely the dual of the above statement.

      propInitial : isProp Initial
      propInitial Xi Yi = res
        where
        open Σ Xi renaming (fst to X ; snd to Xii)
        open Σ Yi renaming (fst to Y ; snd to Yii)
        open Σ (Xii {Y}) renaming (fst to Y→X) using ()
        open Σ (Yii {X}) renaming (fst to X→Y) using ()
        -- Need to show `left` and `right`, what we know is that the arrows are
        -- unique. Well, I know that if I compose these two arrows they must give
        -- the identity, since also the identity is the unique such arrow (by X
        -- and Y both being terminal objects.)
        Xprop : isProp (Arrow X X)
        Xprop f g = trans (sym (snd Xii f)) (snd Xii g)
        Yprop : isProp (Arrow Y Y)
        Yprop f g = trans (sym (snd Yii f)) (snd Yii g)
        left : Y→X ∘ X→Y ≡ identity
        left = Yprop _ _
        right : X→Y ∘ Y→X ≡ identity
        right = Xprop _ _
        iso : X ≅ Y
        iso = Y→X , X→Y , right , left
        fromIso' : X ≅ Y → X ≡ Y
        fromIso' = fst (toIso (X ≡ Y) (X ≅ Y) univalent)
        p0 : X ≡ Y
        p0 = fromIso' iso
        p1 : (λ i → IsInitial (p0 i)) [ Xii ≡ Yii ]
        p1 = lemPropF propIsInitial p0
        res : Xi ≡ Yi
        res i = p0 i , p1 i

module _ {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) where
  open RawCategory ℂ
  open Univalence
  private
    module _ (x y : IsPreCategory ℂ) where
      module x = IsPreCategory x
      module y = IsPreCategory y
      -- In a few places I use the result of propositionality of the various
      -- projections of `IsCategory` - Here I arbitrarily chose to use this
      -- result from `x : IsCategory C`. I don't know which (if any) possibly
      -- adverse effects this may have.
      -- module Prop = X.Propositionality

      propIsPreCategory : x ≡ y
      IsPreCategory.isAssociative (propIsPreCategory i)
        = x.propIsAssociative x.isAssociative y.isAssociative i
      IsPreCategory.isIdentity    (propIsPreCategory i)
        = x.propIsIdentity x.isIdentity y.isIdentity i
      IsPreCategory.arrowsAreSets (propIsPreCategory i)
        = x.propArrowIsSet x.arrowsAreSets y.arrowsAreSets i

    module _ (x y : IsCategory ℂ) where
      module X = IsCategory x
      module Y = IsCategory y
      -- In a few places I use the result of propositionality of the various
      -- projections of `IsCategory` - Here I arbitrarily chose to use this
      -- result from `x : IsCategory C`. I don't know which (if any) possibly
      -- adverse effects this may have.
      module Prop = X.Propositionality

      isIdentity= : (λ _ → IsIdentity identity) [ X.isIdentity ≡ Y.isIdentity ]
      isIdentity= = X.propIsIdentity X.isIdentity Y.isIdentity

      isPreCategory= : X.isPreCategory ≡ Y.isPreCategory
      isPreCategory= = propIsPreCategory X.isPreCategory Y.isPreCategory

      private
        p = cong IsPreCategory.isIdentity isPreCategory=

      univalent= : (λ i → Univalent (p i))
        [ X.univalent ≡ Y.univalent ]
      univalent= = lemPropF
        {A = IsIdentity identity}
        {B = Univalent}
        propUnivalent
        {a0 = X.isIdentity}
        {a1 = Y.isIdentity}
        p

      done : x ≡ y
      IsCategory.isPreCategory (done i) = isPreCategory= i
      IsCategory.univalent     (done i) = univalent= i

  propIsCategory : isProp (IsCategory ℂ)
  propIsCategory = done


-- | Univalent categories
--
-- Just bundles up the data with witnesses inhabiting the propositions.

-- Question: Should I remove the type `Category`?
record Category (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
  field
    raw            : RawCategory ℓa ℓb
    {{isCategory}} : IsCategory raw

  open IsCategory isCategory public

-- The fact that being a category is a mere proposition gives rise to this
-- equality principle for categories.
module _ {ℓa ℓb : Level} {ℂ 𝔻 : Category ℓa ℓb} where
  private
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻

  module _ (rawEq : ℂ.raw ≡ 𝔻.raw) where
    private
      isCategoryEq : (λ i → IsCategory (rawEq i)) [ ℂ.isCategory ≡ 𝔻.isCategory ]
      isCategoryEq = lemPropF {A = RawCategory _ _} {B = IsCategory} propIsCategory rawEq

    Category≡ : ℂ ≡ 𝔻
    Category.raw (Category≡ i) = rawEq i
    Category.isCategory (Category≡ i) = isCategoryEq i

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
    private
      module _ where
        module ℂ = Category ℂ
        opRaw : RawCategory ℓa ℓb
        RawCategory.Object   opRaw = ℂ.Object
        RawCategory.Arrow    opRaw = Function.flip ℂ.Arrow
        RawCategory.identity opRaw = ℂ.identity
        RawCategory._∘_      opRaw = ℂ._>>>_

        open RawCategory opRaw

        isPreCategory : IsPreCategory opRaw
        IsPreCategory.isAssociative isPreCategory = sym ℂ.isAssociative
        IsPreCategory.isIdentity    isPreCategory = swap ℂ.isIdentity
        IsPreCategory.arrowsAreSets isPreCategory = ℂ.arrowsAreSets

      open IsPreCategory isPreCategory

      module _ {A B : ℂ.Object} where
        k : Equivalence.Isomorphism (ℂ.idToIso A B)
        k = toIso _ _ ℂ.univalent
        open Σ k renaming (fst to f ; snd to inv)
        open AreInverses inv

        _⊙_ = Function._∘_
        infixr 9 _⊙_

        -- f    : A ℂ.≅ B → A ≡ B
        flipDem : A ≅ B → A ℂ.≅ B
        flipDem (f , g , inv) = g , f , inv

        flopDem : A ℂ.≅ B → A ≅ B
        flopDem (f , g , inv) = g , f , inv

        -- Shouldn't be necessary to use `arrowsAreSets` here, but we have it,
        -- so why not?
        lem : (p : A ≡ B) → idToIso A B p ≡ flopDem (ℂ.idToIso A B p)
        lem p i = l≡r i
          where
          l = idToIso A B p
          r = flopDem (ℂ.idToIso A B p)
          open Σ l renaming (fst to l-obv ; snd to l-areInv)
          open Σ l-areInv renaming (fst to l-invs ; snd to l-iso)
          open Σ l-iso renaming (fst to l-l ; snd to l-r)
          open Σ r renaming (fst to r-obv ; snd to r-areInv)
          open Σ r-areInv renaming (fst to r-invs ; snd to r-iso)
          open Σ r-iso renaming (fst to r-l ; snd to r-r)
          l-obv≡r-obv : l-obv ≡ r-obv
          l-obv≡r-obv = refl
          l-invs≡r-invs : l-invs ≡ r-invs
          l-invs≡r-invs = refl
          l-l≡r-l : l-l ≡ r-l
          l-l≡r-l = ℂ.arrowsAreSets _ _ l-l r-l
          l-r≡r-r : l-r ≡ r-r
          l-r≡r-r = ℂ.arrowsAreSets _ _ l-r r-r
          l≡r : l ≡ r
          l≡r i = l-obv≡r-obv i , l-invs≡r-invs i , l-l≡r-l i , l-r≡r-r i

        ff : A ≅ B → A ≡ B
        ff = f ⊙ flipDem

        -- inv : AreInverses (ℂ.idToIso A B) f
        invv : AreInverses (idToIso A B) ff
        -- recto-verso : ℂ.idToIso A B ∘ f ≡ idFun (A ℂ.≅ B)
        invv = record
          { verso-recto = funExt (λ x → begin
            (ff ⊙ idToIso A B) x                       ≡⟨⟩
            (f  ⊙ flipDem ⊙ idToIso A B) x             ≡⟨ cong (λ φ → φ x) (cong (λ φ → f ⊙ flipDem ⊙ φ) (funExt lem)) ⟩
            (f  ⊙ flipDem ⊙ flopDem ⊙ ℂ.idToIso A B) x ≡⟨⟩
            (f  ⊙ ℂ.idToIso A B) x                     ≡⟨ (λ i → verso-recto i x) ⟩
            x ∎)
          ; recto-verso = funExt (λ x → begin
            (idToIso A B ⊙ f ⊙ flipDem) x             ≡⟨ cong (λ φ → φ x) (cong (λ φ → φ ⊙ f ⊙ flipDem) (funExt lem)) ⟩
            (flopDem ⊙ ℂ.idToIso A B ⊙ f ⊙ flipDem) x ≡⟨ cong (λ φ → φ x) (cong (λ φ → flopDem ⊙ φ ⊙ flipDem) recto-verso) ⟩
            (flopDem ⊙ flipDem) x                       ≡⟨⟩
            x ∎)
          }

        h : Equivalence.Isomorphism (idToIso A B)
        h = ff , invv
        univalent : isEquiv (A ≡ B) (A ≅ B)
          (Univalence.idToIso (swap ℂ.isIdentity) A B)
        univalent = fromIso _ _ h

      isCategory : IsCategory opRaw
      IsCategory.isPreCategory isCategory = isPreCategory
      IsCategory.univalent     isCategory = univalent

    opposite : Category ℓa ℓb
    Category.raw        opposite = opRaw
    Category.isCategory opposite = isCategory

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
      RawCategory.identity (rawInv _) = identity
      RawCategory._∘_      (rawInv _) = _∘_

    oppositeIsInvolution : opposite (opposite ℂ) ≡ ℂ
    oppositeIsInvolution = Category≡ rawInv

open Opposite public
