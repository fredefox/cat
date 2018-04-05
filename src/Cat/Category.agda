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
    id-to-iso : (A B : Object) → A ≡ B → A ≅ B
    id-to-iso A B eq = transp (\ i → A ≅ eq i) (idIso A)

    Univalent : Set (ℓa ⊔ ℓb)
    Univalent = {A B : Object} → isEquiv (A ≡ B) (A ≅ B) (id-to-iso A B)

    -- A perhaps more readable version of univalence:
    Univalent≃ = {A B : Object} → (A ≡ B) ≃ (A ≅ B)

    -- | Equivalent formulation of univalence.
    Univalent[Contr] : Set _
    Univalent[Contr] = ∀ A → isContr (Σ[ X ∈ Object ] A ≅ X)

    private
      module _ (A : Object)
          -- It may be that we need something weaker than this, in that there
          -- may be some other lemmas available to us.
          -- For instance, `need0` should be available to us when we prove `need1`.
          (need0 : (s : Σ Object (A ≅_)) → (open Σ s renaming (fst to Y) using ()) → A ≡ Y)
          (need2 : (iso : A ≅ A)
            → (open Σ iso   renaming (fst to f  ; snd to iso-f))
            → (open Σ iso-f renaming (fst to f~ ; snd to areInv))
            → (identity , identity) ≡ (f , f~)
          ) where

        c : Σ Object (A ≅_)
        c = A , idIso A

        module _ (y : Σ Object (A ≅_)) where
          open Σ y renaming (fst to Y ; snd to isoY)
          q : A ≡ Y
          q = need0 y

          -- Some error with primComp
          isoAY : A ≅ Y
          isoAY = {!id-to-iso A Y q!}

          lem : PathP (λ i → A ≅ q i) (idIso A) isoY
          lem = d* isoAY
            where
            D  : (Y : Object) → (A ≡ Y) → Set _
            D Y p = (A≅Y : A ≅ Y) → PathP (λ i → A ≅ p i) (idIso A) A≅Y
            d  : D A refl
            d A≅Y i = a0 i , a1 i , a2 i
              where
              open Σ A≅Y   renaming (fst to f  ; snd to iso-f)
              open Σ iso-f renaming (fst to f~ ; snd to areInv)
              aaa : (identity , identity) ≡ (f , f~)
              aaa = need2 A≅Y
              a0 : identity ≡ f
              a0 i = fst (aaa i)
              a1 : identity ≡ f~
              a1 i = snd (aaa i)
              -- we do have this!
              -- I just need to rearrange the proofs a bit.
              postulate
                prop : ∀ {A B} (fg : Arrow A B × Arrow B A) → isProp (IsInverseOf (fst fg) (snd fg))
              a2 : PathP (λ i → IsInverseOf (a0 i) (a1 i)) isIdentity areInv
              a2 = lemPropF prop aaa
            d* : D Y q
            d* = pathJ D d Y q

          p : (A , idIso A) ≡ (Y , isoY)
          p i = q i , lem i

        univ-lem : isContr (Σ Object (A ≅_))
        univ-lem = c , p

    univalence-lemma
      : (∀ {A} → (s : Σ Object (_≅_ A)) → A ≡ fst s)
      → (∀ {A} → (iso : A ≅ A) → (identity , identity) ≡ (fst iso , fst (snd iso)))
      → Univalent[Contr]
    univalence-lemma s u A = univ-lem A s u

    -- From: Thierry Coquand <Thierry.Coquand@cse.gu.se>
    -- Date: Wed, Mar 21, 2018 at 3:12 PM
    --
    -- This is not so straight-forward so you can assume it
    postulate from[Contr] : Univalent[Contr] → Univalent

-- | The mere proposition of being a category.
--
-- Also defines a few lemmas:
--
--     iso-is-epi  : Isomorphism f → Epimorphism {X = X} f
--     iso-is-mono : Isomorphism f → Monomorphism {X = X} f
--
-- Sans `univalent` this would be what is referred to as a pre-category in
-- [HoTT].
record IsCategory {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) : Set (lsuc (ℓa ⊔ ℓb)) where
  open RawCategory ℂ public
  field
    isAssociative : IsAssociative
    isIdentity    : IsIdentity identity
    arrowsAreSets : ArrowsAreSets
  open Univalence isIdentity public
  field
    univalent     : Univalent

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

  -- | The formulation of univalence expressed with _≃_ is trivially admissable -
  -- just "forget" the equivalence.
  univalent≃ : Univalent≃
  univalent≃ = _ , univalent

  module _ {A B : Object} where
    open import Cat.Equivalence using (module Equiv≃)

    iso-to-id : (A ≅ B) → (A ≡ B)
    iso-to-id = fst (Equiv≃.toIso _ _ univalent)

  -- | All projections are propositions.
  module Propositionality where
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
            geq : g ≡ g'
            geq = begin
              g             ≡⟨ sym rightIdentity ⟩
              g ∘ identity  ≡⟨ cong (λ φ → g ∘ φ) (sym ε') ⟩
              g ∘ (f ∘ g')  ≡⟨ isAssociative ⟩
              (g ∘ f) ∘ g'  ≡⟨ cong (λ φ → φ ∘ g') η ⟩
              identity ∘ g' ≡⟨ leftIdentity ⟩
              g'            ∎

    propUnivalent : isProp Univalent
    propUnivalent a b i = propPi (λ iso → propIsContr) a b i

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
      open import Cat.Equivalence hiding (_≅_)
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
      fromIso : X ≅ Y → X ≡ Y
      fromIso = fst (Equiv≃.toIso (X ≡ Y) (X ≅ Y) univalent)
      p0 : X ≡ Y
      p0 = fromIso iso
      p1 : (λ i → IsTerminal (p0 i)) [ Xit ≡ Yit ]
      p1 = lemPropF propIsTerminal p0
      res : Xt ≡ Yt
      res i = p0 i , p1 i

    -- Merely the dual of the above statement.
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

    propInitial : isProp Initial
    propInitial Xi Yi = res
      where
      open Σ Xi renaming (fst to X ; snd to Xii)
      open Σ Yi renaming (fst to Y ; snd to Yii)
      open Σ (Xii {Y}) renaming (fst to Y→X) using ()
      open Σ (Yii {X}) renaming (fst to X→Y) using ()
      open import Cat.Equivalence hiding (_≅_)
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
      fromIso : X ≅ Y → X ≡ Y
      fromIso = fst (Equiv≃.toIso (X ≡ Y) (X ≅ Y) univalent)
      p0 : X ≡ Y
      p0 = fromIso iso
      p1 : (λ i → IsInitial (p0 i)) [ Xii ≡ Yii ]
      p1 = lemPropF propIsInitial p0
      res : Xi ≡ Yi
      res i = p0 i , p1 i

-- | Propositionality of being a category
module _ {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) where
  open RawCategory ℂ
  open Univalence
  private
    module _ (x y : IsCategory ℂ) where
      module X = IsCategory x
      module Y = IsCategory y
      -- In a few places I use the result of propositionality of the various
      -- projections of `IsCategory` - Here I arbitrarily chose to use this
      -- result from `x : IsCategory C`. I don't know which (if any) possibly
      -- adverse effects this may have.
      module Prop = X.Propositionality

      isIdentity : (λ _ → IsIdentity identity) [ X.isIdentity ≡ Y.isIdentity ]
      isIdentity = Prop.propIsIdentity X.isIdentity Y.isIdentity

      U : ∀ {a : IsIdentity identity}
        → (λ _ → IsIdentity identity) [ X.isIdentity ≡ a ]
        → (b : Univalent a)
        → Set _
      U eqwal univ =
        (λ i → Univalent (eqwal i))
        [ X.univalent ≡ univ ]
      P : (y : IsIdentity identity)
        → (λ _ → IsIdentity identity) [ X.isIdentity ≡ y ] → Set _
      P y eq = ∀ (univ : Univalent y) → U eq univ
      p : ∀ (b' : Univalent X.isIdentity)
        → (λ _ → Univalent X.isIdentity) [ X.univalent ≡ b' ]
      p univ = Prop.propUnivalent X.univalent univ
      helper : P Y.isIdentity isIdentity
      helper = pathJ P p Y.isIdentity isIdentity
      eqUni : U isIdentity Y.univalent
      eqUni = helper Y.univalent
      done : x ≡ y
      IsCategory.isAssociative (done i) = Prop.propIsAssociative X.isAssociative Y.isAssociative i
      IsCategory.isIdentity    (done i) = isIdentity i
      IsCategory.arrowsAreSets (done i) = Prop.propArrowIsSet X.arrowsAreSets Y.arrowsAreSets i
      IsCategory.univalent     (done i) = eqUni i

  propIsCategory : isProp (IsCategory ℂ)
  propIsCategory = done

-- | Univalent categories
--
-- Just bundles up the data with witnesses inhabiting the propositions.
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
      isCategoryEq = lemPropF propIsCategory rawEq

    Category≡ : ℂ ≡ 𝔻
    Category≡ i = record
      { raw        = rawEq i
      ; isCategory = isCategoryEq i
      }

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
      module ℂ = Category ℂ
      opRaw : RawCategory ℓa ℓb
      RawCategory.Object   opRaw = ℂ.Object
      RawCategory.Arrow    opRaw = Function.flip ℂ.Arrow
      RawCategory.identity opRaw = ℂ.identity
      RawCategory._∘_      opRaw = Function.flip ℂ._∘_

      open RawCategory opRaw

      isIdentity : IsIdentity identity
      isIdentity = swap ℂ.isIdentity

      open Univalence isIdentity

      module _ {A B : ℂ.Object} where
        open import Cat.Equivalence as Equivalence hiding (_≅_)
        k : Equivalence.Isomorphism (ℂ.id-to-iso A B)
        k = Equiv≃.toIso _ _ ℂ.univalent
        open Σ k renaming (fst to f ; snd to inv)
        open AreInverses inv

        _⊙_ = Function._∘_
        infixr 9 _⊙_

        -- f    : A ℂ.≅ B → A ≡ B
        flipDem : A ≅ B → A ℂ.≅ B
        flipDem (f , g , inv) = g , f , inv

        flopDem : A ℂ.≅ B → A ≅ B
        flopDem (f , g , inv) = g , f , inv

        flipInv : ∀ {x} → (flipDem ⊙ flopDem) x ≡ x
        flipInv = refl

        -- Shouldn't be necessary to use `arrowsAreSets` here, but we have it,
        -- so why not?
        lem : (p : A ≡ B) → id-to-iso A B p ≡ flopDem (ℂ.id-to-iso A B p)
        lem p i = l≡r i
          where
          l = id-to-iso A B p
          r = flopDem (ℂ.id-to-iso A B p)
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

        -- inv : AreInverses (ℂ.id-to-iso A B) f
        invv : AreInverses (id-to-iso A B) ff
        -- recto-verso : ℂ.id-to-iso A B ∘ f ≡ idFun (A ℂ.≅ B)
        invv = record
          { verso-recto = funExt (λ x → begin
            (ff ⊙ id-to-iso A B) x                       ≡⟨⟩
            (f  ⊙ flipDem ⊙ id-to-iso A B) x             ≡⟨ cong (λ φ → φ x) (cong (λ φ → f ⊙ flipDem ⊙ φ) (funExt lem)) ⟩
            (f  ⊙ flipDem ⊙ flopDem ⊙ ℂ.id-to-iso A B) x ≡⟨⟩
            (f  ⊙ ℂ.id-to-iso A B) x                     ≡⟨ (λ i → verso-recto i x) ⟩
            x ∎)
          ; recto-verso = funExt (λ x → begin
            (id-to-iso A B ⊙ f ⊙ flipDem) x             ≡⟨ cong (λ φ → φ x) (cong (λ φ → φ ⊙ f ⊙ flipDem) (funExt lem)) ⟩
            (flopDem ⊙ ℂ.id-to-iso A B ⊙ f ⊙ flipDem) x ≡⟨ cong (λ φ → φ x) (cong (λ φ → flopDem ⊙ φ ⊙ flipDem) recto-verso) ⟩
            (flopDem ⊙ flipDem) x                       ≡⟨⟩
            x ∎)
          }

        h : Equivalence.Isomorphism (id-to-iso A B)
        h = ff , invv
        univalent : isEquiv (A ≡ B) (A ≅ B)
          (Univalence.id-to-iso (swap ℂ.isIdentity) A B)
        univalent = Equiv≃.fromIso _ _ h

      isCategory : IsCategory opRaw
      IsCategory.isAssociative isCategory = sym ℂ.isAssociative
      IsCategory.isIdentity    isCategory = isIdentity
      IsCategory.arrowsAreSets isCategory = ℂ.arrowsAreSets
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
