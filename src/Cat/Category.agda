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
-- _<<<_; function composition
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
{-# OPTIONS --cubical #-}

module Cat.Category where

open import Cat.Prelude
open import Cat.Equivalence hiding (Isomorphism)

TypeIsomorphism = Cat.Equivalence.Isomorphism

------------------
-- * Categories --
------------------

-- | Raw categories
--
-- This record desribes the data that a category consist of as well as some laws
-- about these. The laws defined are the types the propositions - not the
-- witnesses to them!
record RawCategory (ℓa ℓb : Level) : Set (lsuc (ℓa ⊔ ℓb)) where
--  no-eta-equality
  field
    Object   : Set ℓa
    Arrow    : Object → Object → Set ℓb
    identity : {A : Object} → Arrow A A
    _<<<_    : {A B C : Object} → Arrow B C → Arrow A B → Arrow A C

  -- infixr 8 _<<<_
  -- infixl 8 _>>>_
  infixl 10 _<<<_ _>>>_

  -- | Reverse arrow composition
  _>>>_ : {A B C : Object} → (Arrow A B) → (Arrow B C) → Arrow A C
  f >>> g = g <<< f

  -- | Laws about the data

  -- FIXME It seems counter-intuitive that the normal-form is on the
  -- right-hand-side.
  IsAssociative : Set (ℓa ⊔ ℓb)
  IsAssociative = ∀ {A B C D} {f : Arrow A B} {g : Arrow B C} {h : Arrow C D}
    → h <<< (g <<< f) ≡ (h <<< g) <<< f

  IsIdentity : ({A : Object} → Arrow A A) → Set (ℓa ⊔ ℓb)
  IsIdentity id = {A B : Object} {f : Arrow A B}
    → (id <<< f ≡ f) × (f <<< id ≡ f)

  ArrowsAreSets : Set (ℓa ⊔ ℓb)
  ArrowsAreSets = ∀ {A B : Object} → isSet (Arrow A B)

  IsInverseOf : ∀ {A B} → (Arrow A B) → (Arrow B A) → Set ℓb
  IsInverseOf = λ f g → (g <<< f ≡ identity) × (f <<< g ≡ identity)

  Isomorphism : ∀ {A B} → (f : Arrow A B) → Set ℓb
  Isomorphism {A} {B} f = Σ[ g ∈ Arrow B A ] IsInverseOf f g

  _≊_ : (A B : Object) → Set ℓb
  _≊_ A B = Σ[ f ∈ Arrow A B ] (Isomorphism f)

  module _ {A B : Object} where
    Epimorphism : (f : Arrow A B) → Set _
    Epimorphism f = ∀ {X} → (g₀ g₁ : Arrow B X) → g₀ <<< f ≡ g₁ <<< f → g₀ ≡ g₁

    Monomorphism : (f : Arrow A B) → Set _
    Monomorphism f = ∀ {X} → (g₀ g₁ : Arrow X A) → f <<< g₀ ≡ f <<< g₁ → g₀ ≡ g₁

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
    idIso : (A : Object) → A ≊ A
    idIso A = identity , identity , isIdentity

    -- | Extract an isomorphism from an equality
    --
    -- [HoTT §9.1.4]
    idToIso : (A B : Object) → A ≡ B → A ≊ B
    idToIso A B eq = subst (λ X → A ≊ X) eq (idIso A)

    Univalent : Set (ℓa ⊔ ℓb)
    Univalent = {A B : Object} → isEquiv (idToIso A B)

    univalenceFromIsomorphism : {A B : Object}
      → TypeIsomorphism (idToIso A B) → isEquiv (idToIso A B)
    univalenceFromIsomorphism = fromIso _ _

    -- A perhaps more readable version of univalence:
    Univalent≃ = {A B : Object} → (A ≡ B) ≃ (A ≊ B)
    Univalent≅ = {A B : Object} → (A ≡ B) ≅ (A ≊ B)

    private
      -- | Equivalent formulation of univalence.
      Univalent[Contr] : Set _
      Univalent[Contr] = ∀ A → isContr (Σ[ X ∈ Object ] A ≊ X)

      from[Contr] : Univalent[Contr] → Univalent
      from[Contr] = isContrToUniv _ _

    univalenceFrom≃ : Univalent≃ → Univalent
    univalenceFrom≃ = from[Contr] ∘ step
      where
      module _ (f : Univalent≃) (A : Object) where
        lem : Σ Object (A ≡_) ≃ Σ Object (A ≊_)
        lem = equivSig λ _ → f

        aux : isContr (Σ Object (A ≡_))
        aux = (A , refl) , (λ y → contrSingl (snd y))

        step : isContr (Σ Object (A ≊_))
        step = equivPreservesNType 0 lem aux

    univalenceFrom≅ : Univalent≅ → Univalent
    univalenceFrom≅ x = univalenceFrom≃ $ fromIsomorphism _ _ x

    propUnivalent : isProp Univalent
    propUnivalent = propPiImpl (propPiImpl (propIsEquiv _))

module _ {ℓa ℓb : Level} (ℂ : RawCategory ℓa ℓb) where
  record IsPreCategory : Set (lsuc (ℓa ⊔ ℓb)) where
    open RawCategory ℂ public
    field
      isAssociative : IsAssociative
      isIdentity    : IsIdentity identity
      arrowsAreSets : ArrowsAreSets
    open Univalence isIdentity public

    leftIdentity : {A B : Object} {f : Arrow A B} → identity <<< f ≡ f
    leftIdentity {A} {B} {f} = fst (isIdentity {A = A} {B} {f})

    rightIdentity : {A B : Object} {f : Arrow A B} → f <<< identity ≡ f
    rightIdentity {A} {B} {f} = snd (isIdentity {A = A} {B} {f})

    ------------
    -- Lemmas --
    ------------

    -- | Relation between iso- epi- and mono- morphisms.
    module _ {A B : Object} {X : Object} (f : Arrow A B) where
      iso→epi : Isomorphism f → Epimorphism f
      iso→epi (f- , left-inv , right-inv) g₀ g₁ eq = begin
        g₀                  ≡⟨ sym rightIdentity ⟩
        g₀ <<< identity     ≡⟨ cong (_<<<_ g₀) (sym right-inv) ⟩
        g₀ <<< (f <<< f-)   ≡⟨ isAssociative ⟩
        (g₀ <<< f) <<< f-   ≡⟨ cong (λ φ → φ <<< f-) eq ⟩
        (g₁ <<< f) <<< f-   ≡⟨ sym isAssociative ⟩
        g₁ <<< (f <<< f-)   ≡⟨ cong (_<<<_ g₁) right-inv ⟩
        g₁ <<< identity     ≡⟨ rightIdentity ⟩
        g₁                  ∎

      iso→mono : Isomorphism f → Monomorphism f
      iso→mono (f- , left-inv , right-inv) g₀ g₁ eq =
        begin
        g₀                ≡⟨ sym leftIdentity ⟩
        identity <<< g₀   ≡⟨ cong (λ φ → φ <<< g₀) (sym left-inv) ⟩
        (f- <<< f) <<< g₀ ≡⟨ sym isAssociative ⟩
        f- <<< (f <<< g₀) ≡⟨ cong (_<<<_ f-) eq ⟩
        f- <<< (f <<< g₁) ≡⟨ isAssociative ⟩
        (f- <<< f) <<< g₁ ≡⟨ cong (λ φ → φ <<< g₁) left-inv ⟩
        identity <<< g₁   ≡⟨ leftIdentity ⟩
        g₁                ∎

      iso→epi×mono : Isomorphism f → Epimorphism f × Monomorphism f
      iso→epi×mono iso = iso→epi iso , iso→mono iso

    propIsAssociative : isProp IsAssociative
    propIsAssociative = propPiImpl (propPiImpl (propPiImpl (propPiImpl (propPiImpl (propPiImpl (propPiImpl (arrowsAreSets _ _)))))))

    propIsIdentity : ∀ {f : ∀ {A} → Arrow A A} → isProp (IsIdentity f)
    propIsIdentity {id} = propPiImpl (propPiImpl (propPiImpl (λ {f} →
      propSig (arrowsAreSets (id <<< f) f) λ _ → arrowsAreSets (f <<< id) f)))

    propArrowIsSet : isProp (∀ {A B} → isSet (Arrow A B))
    propArrowIsSet = propPiImpl (propPiImpl isSetIsProp)

    propIsInverseOf : ∀ {A B f g} → isProp (IsInverseOf {A} {B} f g)
    propIsInverseOf = propSig (arrowsAreSets _ _) (λ _ → arrowsAreSets _ _)

    module _ {A B : Object} where
      propIsomorphism : (f : Arrow A B) → isProp (Isomorphism f)
      propIsomorphism f a@(g , η , ε) a'@(g' , η' , ε') =
        lemSig (λ g → propIsInverseOf) geq
          where
            geq : g ≡ g'
            geq = begin
              g                 ≡⟨ sym rightIdentity ⟩
              g <<< identity    ≡⟨ cong (λ φ → g <<< φ) (sym ε') ⟩
              g <<< (f <<< g')  ≡⟨ isAssociative ⟩
              (g <<< f) <<< g'  ≡⟨ cong (λ φ → φ <<< g') η ⟩
              identity <<< g'   ≡⟨ leftIdentity ⟩
              g'                ∎

      isoEq : {a b : A ≊ B} → fst a ≡ fst b → a ≡ b
      isoEq = lemSig propIsomorphism

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
        cp = lemPropF prop _ _ fp
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
        cp = lemPropF prop _ _ fp
        res : (fx , cx) ≡ (fy , cy)
        res i = fp i , cp i

    module _ where
      private
        trans≊ : Transitive _≊_
        trans≊ (f , f~ , f-inv) (g , g~ , g-inv)
          = g <<< f
          , f~ <<< g~
          , ( begin
              (f~ <<< g~) <<< (g <<< f) ≡⟨ isAssociative ⟩
              (f~ <<< g~) <<< g <<< f   ≡⟨ cong (λ φ → φ <<< f) (sym isAssociative) ⟩
              f~ <<< (g~ <<< g) <<< f   ≡⟨ cong (λ φ → f~ <<< φ <<< f) (fst g-inv) ⟩
              f~ <<< identity <<< f     ≡⟨ cong (λ φ → φ <<< f) rightIdentity ⟩
              f~ <<< f                  ≡⟨ fst f-inv ⟩
              identity                  ∎
            )
          , ( begin
              g <<< f <<< (f~ <<< g~) ≡⟨ isAssociative ⟩
              g <<< f <<< f~ <<< g~   ≡⟨ cong (λ φ → φ <<< g~) (sym isAssociative) ⟩
              g <<< (f <<< f~) <<< g~ ≡⟨ cong (λ φ → g <<< φ <<< g~) (snd f-inv) ⟩
              g <<< identity <<< g~   ≡⟨ cong (λ φ → φ <<< g~) rightIdentity ⟩
              g <<< g~                ≡⟨ snd g-inv ⟩
              identity                ∎
            )
        isPreorder : IsPreorder _≊_
        isPreorder = record { isEquivalence = equalityIsEquivalence ; reflexive = idToIso _ _ ; trans = trans≊ }

      preorder≊ : Preorder _ _ _
      preorder≊ = record { Carrier = Object ; _≈_ = _≡_ ; _∼_ = _≊_ ; isPreorder = isPreorder }

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
      private
        iso : TypeIsomorphism (idToIso A B)
        iso = toIso _ _ univalent

      isoToId : (A ≊ B) → (A ≡ B)
      isoToId = fst iso

      asTypeIso : TypeIsomorphism (idToIso A B)
      asTypeIso = toIso _ _ univalent

      -- FIXME Rename
      inverse-from-to-iso' : AreInverses (idToIso A B) isoToId
      inverse-from-to-iso' = snd iso

    module _ {a b : Object} (f : Arrow a b) where
      module _ {a' : Object} (p : a ≡ a') where
        private
          p~ : Arrow a' a
          p~ = fst (snd (idToIso _ _ p))

          D : ∀ a'' → a ≡ a'' → Set _
          D a'' p' = coe (cong (λ x → Arrow x b) p') f ≡ f <<< (fst (snd (idToIso _ _ p')))

        9-1-9-left  : coe (cong (λ x → Arrow x b) p) f ≡ f <<< p~
        9-1-9-left  = pathJ D (begin
          coe refl f ≡⟨ coe-neutral _ ⟩
          f ≡⟨ sym rightIdentity ⟩
          f <<< identity ≡⟨ cong (f <<<_) (sym (coe-neutral _)) ⟩
          f <<< _ ≡⟨⟩ _ ∎) p

      module _ {b' : Object} (p : b ≡ b') where
        private
          p* : Arrow b  b'
          p* = fst (idToIso _ _ p)

          D : ∀ b'' → b ≡ b'' → Set _
          D b'' p' = coe (cong (λ x → Arrow a x) p') f ≡ fst (idToIso _ _ p') <<< f

        9-1-9-right : coe (cong (λ x → Arrow a x) p) f ≡ p* <<< f
        9-1-9-right = pathJ D (begin
          coe refl f ≡⟨ coe-neutral _ ⟩
          f ≡⟨ sym leftIdentity ⟩
          identity <<< f ≡⟨ cong (_<<< f) (sym (coe-neutral _)) ⟩
          _ <<< f ∎) p

    -- lemma 9.1.9 in hott
    module _ {a a' b b' : Object}
      (p : a ≡ a') (q : b ≡ b') (f : Arrow a b)
      where
      private
        q* : Arrow b  b'
        q* = fst (idToIso _ _ q)
        q~ : Arrow b' b
        q~ = fst (snd (idToIso _ _ q))
        p* : Arrow a  a'
        p* = fst (idToIso _ _ p)
        p~ : Arrow a' a
        p~ = fst (snd (idToIso _ _ p))
        pq : Arrow a b ≡ Arrow a' b'
        pq i = Arrow (p i) (q i)

        U : ∀ b'' → b ≡ b'' → Set _
        U b'' q' = coe (λ i → Arrow a (q' i)) f ≡ fst (idToIso _ _ q') <<< f <<< (fst (snd (idToIso _ _ refl)))
        u : coe (λ i → Arrow a b) f ≡ fst (idToIso _ _ refl) <<< f <<< (fst (snd (idToIso _ _ refl)))
        u = begin
          coe refl f     ≡⟨ coe-neutral _ ⟩
          f              ≡⟨ sym leftIdentity ⟩
          identity <<< f ≡⟨ sym rightIdentity ⟩
          identity <<< f <<< identity ≡⟨ cong (λ φ → identity <<< f <<< φ) lem ⟩
          identity <<< f <<< (fst (snd (idToIso _ _ refl))) ≡⟨ cong (λ φ → φ <<< f <<< (fst (snd (idToIso _ _ refl)))) lem ⟩
          fst (idToIso _ _ refl) <<< f <<< (fst (snd (idToIso _ _ refl))) ∎
          where
          lem : ∀ {x} → PathP (λ _ → Arrow x x) identity (fst (idToIso x x refl))
          lem = sym (coe-neutral _)

        D : ∀ a'' → a ≡ a'' → Set _
        D a'' p' = coe (λ i → Arrow (p' i) (q i)) f ≡ fst (idToIso b b' q) <<< f <<< (fst (snd (idToIso _ _ p')))

        d : coe (λ i → Arrow a (q i)) f ≡ fst (idToIso b b' q) <<< f <<< (fst (snd (idToIso _ _ refl)))
        d = pathJ U u q

      9-1-9 : coe pq f ≡ q* <<< f <<< p~
      9-1-9 = pathJ D d p

      9-1-9' : coe pq f <<< p* ≡ q* <<< f
      9-1-9' = begin
        coe pq f <<< p* ≡⟨ cong (_<<< p*) 9-1-9 ⟩
        q* <<< f <<< p~ <<< p* ≡⟨ sym isAssociative ⟩
        q* <<< f <<< (p~ <<< p*) ≡⟨ cong (λ φ → q* <<< f <<< φ) lem ⟩
        q* <<< f <<< identity ≡⟨ rightIdentity ⟩
        q* <<< f ∎
        where
        lem : p~ <<< p* ≡ identity
        lem = fst (snd (snd (idToIso _ _ p)))

    module _ {A B X : Object} (iso : A ≊ B) where
      private
        p : A ≡ B
        p = isoToId iso
        p-dom : Arrow A X ≡ Arrow B X
        p-dom = cong (λ x → Arrow x X) p
        p-cod : Arrow X A ≡ Arrow X B
        p-cod = cong (λ x → Arrow X x) p
        lem : ∀ {A B} {x : A ≊ B} → idToIso A B (isoToId x) ≡ x
        lem {x = x} i = snd inverse-from-to-iso' i x

      open Σ iso renaming (fst to ι) using ()
      open Σ (snd iso) renaming (fst to ι~ ; snd to inv)

      coe-dom : {f : Arrow A X} → coe p-dom f ≡ f <<< ι~
      coe-dom {f} = begin
        coe p-dom f ≡⟨ 9-1-9-left f p ⟩
        f <<< fst (snd (idToIso _ _ (isoToId iso))) ≡⟨⟩
        f <<< fst (snd (idToIso _ _ p)) ≡⟨ cong (f <<<_) (cong (fst ∘ snd) lem) ⟩
        f <<< ι~ ∎

      coe-cod : {f : Arrow X A} → coe p-cod f ≡ ι <<< f
      coe-cod {f} = begin
        coe p-cod f
          ≡⟨ 9-1-9-right f p ⟩
        fst (idToIso _ _ p) <<< f
          ≡⟨ cong (λ φ → φ <<< f) (cong fst lem) ⟩
        ι <<< f ∎

      module _ {f : Arrow A X} {g : Arrow B X} (q : PathP (λ i → p-dom i) f g) where
        domain-twist : g ≡ f <<< ι~
        domain-twist = begin
          g            ≡⟨ sym (coe-lem q) ⟩
          coe p-dom f  ≡⟨ coe-dom ⟩
          f <<< ι~      ∎

        -- This can probably also just be obtained from the above my taking the
        -- symmetric isomorphism.
        domain-twist-sym : f ≡ g <<< ι
        domain-twist-sym = begin
          f ≡⟨ sym rightIdentity ⟩
          f <<< identity ≡⟨ cong (f <<<_) (sym (fst inv)) ⟩
          f <<< (ι~ <<< ι) ≡⟨ isAssociative ⟩
          f <<< ι~ <<< ι ≡⟨ cong (_<<< ι) (sym domain-twist) ⟩
          g <<< ι ∎

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
        left : Y→X <<< X→Y ≡ identity
        left = Xprop _ _
        right : X→Y <<< Y→X ≡ identity
        right = Yprop _ _
        iso : X ≊ Y
        iso = X→Y , Y→X , left , right
        p0 : X ≡ Y
        p0 = isoToId iso
        p1 : (λ i → IsTerminal (p0 i)) [ Xit ≡ Yit ]
        p1 = lemPropF propIsTerminal _ _ p0
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
        left : Y→X <<< X→Y ≡ identity
        left = Yprop _ _
        right : X→Y <<< Y→X ≡ identity
        right = Xprop _ _
        iso : X ≊ Y
        iso = Y→X , X→Y , right , left
        res : Xi ≡ Yi
        res = lemSig propIsInitial (isoToId iso)

    groupoidObject : isGrpd Object
    groupoidObject A B = res
      where
      open import Data.Nat using (_≤_ ; ≤′-refl ; ≤′-step)
      setIso : ∀ x → isSet (Isomorphism x)
      setIso x = propSet (propIsomorphism x)
      step : isSet (A ≊ B)
      step = setSig arrowsAreSets setIso
      res : isSet (A ≡ B)
      res = equivPreservesNType
        {A = A ≊ B} {B = A ≡ B} 2
        (invEquiv (univalent≃ {A = A} {B}))
        step

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
        {x = X.isIdentity}
        {y = Y.isIdentity}
        _
        _
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
      isCategoryEq = lemPropF {A = RawCategory _ _} {B = IsCategory} propIsCategory _ _ rawEq

    Category≡ : ℂ ≡ 𝔻
    Category.raw (Category≡ i) = rawEq i
    Category.isCategory (Category≡ i) = isCategoryEq i

-- | Syntax for arrows- and composition in a given category.
module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Category ℂ
  _[_,_] : (A : Object) → (B : Object) → Set ℓb
  _[_,_] = Arrow

  _[_∘_] : {A B C : Object} → (g : Arrow B C) → (f : Arrow A B) → Arrow A C
  _[_∘_] = _<<<_
