-- | The category of homotopy sets
{-# OPTIONS --allow-unsolved-metas --cubical --caching #-}
module Cat.Categories.Sets where

open import Cat.Prelude as P hiding (_≃_)

open import Function using (_∘_ ; _∘′_)

open import Cubical.Univalence using (univalence ; con ; _≃_ ; idtoeqv ; ua)

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.Product
open import Cat.Wishlist
open import Cat.Equivalence as Eqv using (AreInverses ; module Equiv≃ ; module NoEta)

open NoEta

module Equivalence = Equivalence′

_⊙_ : {ℓa ℓb ℓc : Level} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} → (A ≃ B) → (B ≃ C) → A ≃ C
eqA ⊙ eqB = Equivalence.compose eqA eqB

sym≃ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → A ≃ B → B ≃ A
sym≃ = Equivalence.symmetry

infixl 10 _⊙_

module _ (ℓ : Level) where
  private
    SetsRaw : RawCategory (lsuc ℓ) ℓ
    RawCategory.Object   SetsRaw = hSet ℓ
    RawCategory.Arrow    SetsRaw (T , _) (U , _) = T → U
    RawCategory.identity SetsRaw = Function.id
    RawCategory._∘_      SetsRaw = Function._∘′_

    module _ where
      private
        open RawCategory SetsRaw hiding (_∘_)

        isIdentity : IsIdentity Function.id
        fst isIdentity = funExt λ _ → refl
        snd isIdentity = funExt λ _ → refl

        arrowsAreSets : ArrowsAreSets
        arrowsAreSets {B = (_ , s)} = setPi λ _ → s

      isPreCat : IsPreCategory SetsRaw
      IsPreCategory.isAssociative isPreCat         = refl
      IsPreCategory.isIdentity    isPreCat {A} {B} = isIdentity    {A} {B}
      IsPreCategory.arrowsAreSets isPreCat {A} {B} = arrowsAreSets {A} {B}

    open IsPreCategory isPreCat hiding (_∘_)

    isIso = Eqv.Isomorphism
    module _ {hA hB : hSet ℓ} where
      open Σ hA renaming (fst to A ; snd to sA)
      open Σ hB renaming (fst to B ; snd to sB)
      lem1 : (f : A → B) → isSet A → isSet B → isProp (isIso f)
      lem1 f sA sB = res
        where
        module _ (x y : isIso f) where
          module x = Σ x renaming (fst to inverse ; snd to areInverses)
          module y = Σ y renaming (fst to inverse ; snd to areInverses)
          module xA = AreInverses x.areInverses
          module yA = AreInverses y.areInverses
          -- I had a lot of difficulty using the corresponding proof where
          -- AreInverses is defined. This is sadly a bit anti-modular. The
          -- reason for my troubles is probably related to the type of objects
          -- being hSet's rather than sets.
          p : ∀ {f} g → isProp (AreInverses {A = A} {B} f g)
          p {f} g xx yy i = record
            { verso-recto = ve-re
            ; recto-verso = re-ve
            }
            where
            module xxA = AreInverses xx
            module yyA = AreInverses yy
            ve-re : g ∘ f ≡ Function.id
            ve-re = arrowsAreSets {A = hA} {B = hA} _ _ xxA.verso-recto yyA.verso-recto i
            re-ve : f ∘ g ≡ Function.id
            re-ve = arrowsAreSets {A = hB} {B = hB} _ _ xxA.recto-verso yyA.recto-verso i
          1eq : x.inverse ≡ y.inverse
          1eq = begin
            x.inverse                   ≡⟨⟩
            x.inverse ∘ Function.id     ≡⟨ cong (λ φ → x.inverse ∘ φ) (sym yA.recto-verso) ⟩
            x.inverse ∘ (f ∘ y.inverse) ≡⟨⟩
            (x.inverse ∘ f) ∘ y.inverse ≡⟨ cong (λ φ → φ ∘ y.inverse) xA.verso-recto ⟩
            Function.id ∘ y.inverse     ≡⟨⟩
            y.inverse                   ∎
          2eq : (λ i → AreInverses f (1eq i)) [ x.areInverses ≡ y.areInverses ]
          2eq = lemPropF p 1eq
          res : x ≡ y
          res i = 1eq i , 2eq i
    module _ {ℓa ℓb : Level} {A : Set ℓa} {P : A → Set ℓb} where
      lem2 : ((x : A) → isProp (P x)) → (p q : Σ A P)
        → (p ≡ q) ≃ (fst p ≡ fst q)
      lem2 pA p q = fromIsomorphism iso
        where
        f : ∀ {p q} → p ≡ q → fst p ≡ fst q
        f e i = fst (e i)
        g : ∀ {p q} → fst p ≡ fst q → p ≡ q
        g {p} {q} = lemSig pA p q
        ve-re : (e : p ≡ q) → (g ∘ f) e ≡ e
        ve-re = pathJ (\ q (e : p ≡ q) → (g ∘ f) e ≡ e)
                  (\ i j → p .fst , propSet (pA (p .fst)) (p .snd) (p .snd) (λ i → (g {p} {p} ∘ f) (λ i₁ → p) i .snd) (λ i → p .snd) i j ) q
        re-ve : (e : fst p ≡ fst q) → (f {p} {q} ∘ g {p} {q}) e ≡ e
        re-ve e = refl
        inv : AreInverses (f {p} {q}) (g {p} {q})
        inv = record
          { verso-recto = funExt ve-re
          ; recto-verso = funExt re-ve
          }
        iso : (p ≡ q) Eqv.≅ (fst p ≡ fst q)
        iso = f , g , inv

      lem3 : ∀ {ℓc} {Q : A → Set (ℓc ⊔ ℓb)}
        → ((a : A) → P a ≃ Q a) → Σ A P ≃ Σ A Q
      lem3 {Q = Q} eA = res
        where
        f : Σ A P → Σ A Q
        f (a , pA) = a , _≃_.eqv (eA a) pA
        g : Σ A Q → Σ A P
        g (a , qA) = a , g' qA
          where
          k : Eqv.Isomorphism _
          k = Equiv≃.toIso _ _ (_≃_.isEqv (eA a))
          open Σ k renaming (fst to g')
        ve-re : (x : Σ A P) → (g ∘ f) x ≡ x
        ve-re x i = fst x , eq i
          where
          eq : snd ((g ∘ f) x) ≡ snd x
          eq = begin
            snd ((g ∘ f) x) ≡⟨⟩
            snd (g (f (a , pA))) ≡⟨⟩
            g' (_≃_.eqv (eA a) pA) ≡⟨ lem ⟩
            pA ∎
            where
            open Σ x renaming (fst to a ; snd to pA)
            k : Eqv.Isomorphism _
            k = Equiv≃.toIso _ _ (_≃_.isEqv (eA a))
            open Σ k renaming (fst to g' ; snd to inv)
            module A = AreInverses inv
            -- anti-funExt
            lem : (g' ∘ (_≃_.eqv (eA a))) pA ≡ pA
            lem i = A.verso-recto i pA
        re-ve : (x : Σ A Q) → (f ∘ g) x ≡ x
        re-ve x i = fst x , eq i
          where
          open Σ x renaming (fst to a ; snd to qA)
          eq = begin
            snd ((f ∘ g) x)                 ≡⟨⟩
            _≃_.eqv (eA a) (g' qA)            ≡⟨ (λ i → A.recto-verso i qA) ⟩
            qA                                ∎
            where
            k : Eqv.Isomorphism _
            k = Equiv≃.toIso _ _ (_≃_.isEqv (eA a))
            open Σ k renaming (fst to g' ; snd to inv)
            module A = AreInverses inv
        inv : AreInverses f g
        inv = record
          { verso-recto = funExt ve-re
          ; recto-verso = funExt re-ve
          }
        iso : Σ A P Eqv.≅ Σ A Q
        iso = f , g , inv
        res : Σ A P ≃ Σ A Q
        res = fromIsomorphism iso

    module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
      lem4 : isSet A → isSet B → (f : A → B)
        → isEquiv A B f ≃ isIso f
      lem4 sA sB f =
        let
          obv : isEquiv A B f → isIso f
          obv = Equiv≃.toIso A B
          inv : isIso f → isEquiv A B f
          inv = Equiv≃.fromIso A B
          re-ve : (x : isEquiv A B f) → (inv ∘ obv) x ≡ x
          re-ve = Equiv≃.inverse-from-to-iso A B
          ve-re : (x : isIso f)       → (obv ∘ inv) x ≡ x
          ve-re = Equiv≃.inverse-to-from-iso A B sA sB
          iso : isEquiv A B f Eqv.≅ isIso f
          iso = obv , inv ,
            record
              { verso-recto = funExt re-ve
              ; recto-verso = funExt ve-re
              }
        in fromIsomorphism iso

    module _ {hA hB : Object} where
      open Σ hA renaming (fst to A ; snd to sA)
      open Σ hB renaming (fst to B ; snd to sB)

      -- lem3 and the equivalence from lem4
      step0 : Σ (A → B) isIso ≃ Σ (A → B) (isEquiv A B)
      step0 = lem3 {ℓc = lzero} (λ f → sym≃ (lem4 sA sB f))

      -- univalence
      step1 : Σ (A → B) (isEquiv A B) ≃ (A ≡ B)
      step1 = hh ⊙ h
        where
          h : (A ≃ B) ≃ (A ≡ B)
          h = sym≃ (univalence {A = A} {B})
          obv : Σ (A → B) (isEquiv A B) → A ≃ B
          obv = Eqv.deEta
          inv : A ≃ B → Σ (A → B) (isEquiv A B)
          inv = Eqv.doEta
          re-ve : (x : _) → (inv ∘ obv) x ≡ x
          re-ve x = refl
          -- Because _≃_ does not have eta equality!
          ve-re : (x : _) → (obv ∘ inv) x ≡ x
          ve-re (con eqv isEqv) i = con eqv isEqv
          areInv : AreInverses obv inv
          areInv = record { verso-recto = funExt re-ve ; recto-verso = funExt ve-re }
          eqv : Σ (A → B) (isEquiv A B) Eqv.≅ (A ≃ B)
          eqv = obv , inv , areInv
          hh : Σ (A → B) (isEquiv A B) ≃ (A ≃ B)
          hh = fromIsomorphism eqv

      -- lem2 with propIsSet
      step2 : (A ≡ B) ≃ (hA ≡ hB)
      step2 = sym≃ (lem2 (λ A → isSetIsProp) hA hB)

      -- Go from an isomorphism on sets to an isomorphism on homotopic sets
      trivial? : (hA ≅ hB) ≃ (A Eqv.≅ B)
      trivial? = sym≃ (fromIsomorphism res)
        where
        fwd : Σ (A → B) isIso → hA ≅ hB
        fwd (f , g , inv) = f , g , inv.toPair
          where
          module inv = AreInverses inv
        bwd : hA ≅ hB → Σ (A → B) isIso
        bwd (f , g , x , y) = f , g , record { verso-recto = x ; recto-verso = y }
        res : Σ (A → B) isIso Eqv.≅ (hA ≅ hB)
        res = fwd , bwd , record { verso-recto = refl ; recto-verso = refl }

      conclusion : (hA ≅ hB) ≃ (hA ≡ hB)
      conclusion = trivial? ⊙ step0 ⊙ step1 ⊙ step2

      univ≃ : (hA ≅ hB) ≃ (hA ≡ hB)
      univ≃ = trivial? ⊙ step0 ⊙ step1 ⊙ step2

    module _ (hA : Object) where
      open Σ hA renaming (fst to A)

      eq1 : (Σ[ hB ∈ Object ] hA ≅ hB) ≡ (Σ[ hB ∈ Object ] hA ≡ hB)
      eq1 = ua (lem3 (\ hB → univ≃))

      univalent[Contr] : isContr (Σ[ hB ∈ Object ] hA ≅ hB)
      univalent[Contr] = subst {P = isContr} (sym eq1) tres
        where
        module _ (y : Σ[ hB ∈ Object ] hA ≡ hB) where
          open Σ y renaming (fst to hB ; snd to hA≡hB)
          qres : (hA , refl) ≡ (hB , hA≡hB)
          qres = contrSingl hA≡hB

        tres : isContr (Σ[ hB ∈ Object ] hA ≡ hB)
        tres = (hA , refl) , qres

    univalent : Univalent
    univalent = from[Contr] univalent[Contr]

    SetsIsCategory : IsCategory SetsRaw
    IsCategory.isPreCategory SetsIsCategory = isPreCat
    IsCategory.univalent     SetsIsCategory = univalent

  𝓢𝓮𝓽 Sets : Category (lsuc ℓ) ℓ
  Category.raw 𝓢𝓮𝓽 = SetsRaw
  Category.isCategory 𝓢𝓮𝓽 = SetsIsCategory
  Sets = 𝓢𝓮𝓽

module _ {ℓ : Level} where
  private
    𝓢 = 𝓢𝓮𝓽 ℓ
    open Category 𝓢
    open import Cubical.Sigma

    module _ (hA hB : Object) where
      open Σ hA renaming (fst to A ; snd to sA)
      open Σ hB renaming (fst to B ; snd to sB)

      private
        productObject : Object
        productObject = (A × B) , sigPresSet sA λ _ → sB

        module _ {X A B : Set ℓ} (f : X → A) (g : X → B) where
          _&&&_ : (X → A × B)
          _&&&_ x = f x , g x

        module _ (hX : Object) where
          open Σ hX renaming (fst to X)
          module _ (f : X → A ) (g : X → B) where
            ump : fst Function.∘′ (f &&& g) ≡ f × snd Function.∘′ (f &&& g) ≡ g
            fst ump = refl
            snd ump = refl

        rawProduct : RawProduct 𝓢 hA hB
        RawProduct.object rawProduct = productObject
        RawProduct.fst    rawProduct = fst
        RawProduct.snd    rawProduct = snd

        isProduct : IsProduct 𝓢 _ _ rawProduct
        IsProduct.ump isProduct {X = hX} f g
          = f &&& g , ump hX f g , λ eq → funExt (umpUniq eq)
          where
          open Σ hX renaming (fst to X) using ()
          module _ {y : X → A × B} (eq : fst Function.∘′ y ≡ f × snd Function.∘′ y ≡ g) (x : X) where
            p1 : fst ((f &&& g) x) ≡ fst (y x)
            p1 = begin
              fst ((f &&& g) x) ≡⟨⟩
              f x ≡⟨ (λ i → sym (fst eq) i x) ⟩
              fst (y x) ∎
            p2 : snd ((f &&& g) x) ≡ snd (y x)
            p2 = λ i → sym (snd eq) i x
            umpUniq : (f &&& g) x ≡ y x
            umpUniq i = p1 i , p2 i

      product : Product 𝓢 hA hB
      Product.raw       product = rawProduct
      Product.isProduct product = isProduct

  instance
    SetsHasProducts : HasProducts 𝓢
    SetsHasProducts = record { product = product }

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Category ℂ

  -- Covariant Presheaf
  Representable : Set (ℓa ⊔ lsuc ℓb)
  Representable = Functor ℂ (𝓢𝓮𝓽 ℓb)

  -- Contravariant Presheaf
  Presheaf : Set (ℓa ⊔ lsuc ℓb)
  Presheaf = Functor (opposite ℂ) (𝓢𝓮𝓽 ℓb)

  -- The "co-yoneda" embedding.
  representable : Category.Object ℂ → Representable
  representable A = record
    { raw = record
      { omap = λ B → ℂ [ A , B ] , arrowsAreSets
      ; fmap = ℂ [_∘_]
      }
    ; isFunctor = record
      { isIdentity     = funExt λ _ → leftIdentity
      ; isDistributive = funExt λ x → sym isAssociative
      }
    }

  -- Alternate name: `yoneda`
  presheaf : Category.Object (opposite ℂ) → Presheaf
  presheaf B = record
    { raw = record
      { omap = λ A → ℂ [ A , B ] , arrowsAreSets
      ; fmap = λ f g → ℂ [ g ∘ f ]
    }
    ; isFunctor = record
      { isIdentity     = funExt λ x → rightIdentity
      ; isDistributive = funExt λ x → isAssociative
      }
    }
