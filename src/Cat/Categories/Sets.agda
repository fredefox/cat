-- | The category of homotopy sets
{-# OPTIONS --allow-unsolved-metas --cubical --caching #-}
module Cat.Categories.Sets where

open import Cat.Prelude as P

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.Product
open import Cat.Wishlist
open import Cat.Equivalence renaming (_≅_ to _≈_)

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
    RawCategory.identity SetsRaw = idFun _
    RawCategory._<<<_    SetsRaw = _∘′_

    module _ where
      private
        open RawCategory SetsRaw hiding (_<<<_)

        isIdentity : IsIdentity (idFun _)
        fst isIdentity = funExt λ _ → refl
        snd isIdentity = funExt λ _ → refl

        arrowsAreSets : ArrowsAreSets
        arrowsAreSets {B = (_ , s)} = setPi λ _ → s

      isPreCat : IsPreCategory SetsRaw
      IsPreCategory.isAssociative isPreCat         = refl
      IsPreCategory.isIdentity    isPreCat {A} {B} = isIdentity    {A} {B}
      IsPreCategory.arrowsAreSets isPreCat {A} {B} = arrowsAreSets {A} {B}

    open IsPreCategory isPreCat hiding (_<<<_)

    isIso = TypeIsomorphism
    module _ {hA hB : hSet ℓ} where
      open Σ hA renaming (fst to A ; snd to sA)
      open Σ hB renaming (fst to B ; snd to sB)
      lem1 : (f : A → B) → isSet A → isSet B → isProp (isIso f)
      lem1 f sA sB = res
        where
        module _ (x y : isIso f) where
          module x = Σ x renaming (fst to inverse ; snd to areInverses)
          module y = Σ y renaming (fst to inverse ; snd to areInverses)
          -- I had a lot of difficulty using the corresponding proof where
          -- AreInverses is defined. This is sadly a bit anti-modular. The
          -- reason for my troubles is probably related to the type of objects
          -- being hSet's rather than sets.
          p : ∀ {f} g → isProp (AreInverses {A = A} {B} f g)
          p {f} g xx yy i = ve-re , re-ve
            where
            ve-re : g ∘ f ≡ idFun _
            ve-re = arrowsAreSets {A = hA} {B = hA} _ _ (fst xx) (fst yy) i
            re-ve : f ∘ g ≡ idFun _
            re-ve = arrowsAreSets {A = hB} {B = hB} _ _ (snd xx) (snd yy) i
          1eq : x.inverse ≡ y.inverse
          1eq = begin
            x.inverse                   ≡⟨⟩
            x.inverse ∘ idFun _         ≡⟨ cong (λ φ → x.inverse ∘ φ) (sym (snd y.areInverses)) ⟩
            x.inverse ∘ (f ∘ y.inverse) ≡⟨⟩
            (x.inverse ∘ f) ∘ y.inverse ≡⟨ cong (λ φ → φ ∘ y.inverse) (fst x.areInverses) ⟩
            idFun _ ∘ y.inverse         ≡⟨⟩
            y.inverse                   ∎
          2eq : (λ i → AreInverses f (1eq i)) [ x.areInverses ≡ y.areInverses ]
          2eq = lemPropF p 1eq
          res : x ≡ y
          res i = 1eq i , 2eq i
    module _ {ℓa ℓb : Level} {A : Set ℓa} {P : A → Set ℓb} where
      lem2 : ((x : A) → isProp (P x)) → (p q : Σ A P)
        → (p ≡ q) ≃ (fst p ≡ fst q)
      lem2 pA p q = fromIsomorphism _ _ iso
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
        inv = funExt ve-re , funExt re-ve
        iso : (p ≡ q) ≈ (fst p ≡ fst q)
        iso = f , g , inv

    module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
      lem4 : isSet A → isSet B → (f : A → B)
        → isEquiv A B f ≃ isIso f
      lem4 sA sB f =
        let
          obv : isEquiv A B f → isIso f
          obv = toIso A B
          inv : isIso f → isEquiv A B f
          inv = fromIso A B
          re-ve : (x : isEquiv A B f) → (inv ∘ obv) x ≡ x
          re-ve = inverse-from-to-iso A B
          ve-re : (x : isIso f)       → (obv ∘ inv) x ≡ x
          ve-re = inverse-to-from-iso A B sA sB
          iso : isEquiv A B f ≈ isIso f
          iso = obv , inv , funExt re-ve , funExt ve-re
        in fromIsomorphism _ _ iso

    module _ {hA hB : Object} where
      open Σ hA renaming (fst to A ; snd to sA)
      open Σ hB renaming (fst to B ; snd to sB)

      -- lem3 and the equivalence from lem4
      step0 : Σ (A → B) (isEquiv A B) ≃ Σ (A → B) isIso
      step0 = equivSig (lem4 sA sB)

      -- lem2 with propIsSet
      step2 : (hA ≡ hB) ≃ (A ≡ B)
      step2 = lem2 (λ A → isSetIsProp) hA hB

      univ≃ : (hA ≡ hB) ≃ (hA ≅ hB)
      univ≃ = step2 ⊙ univalence ⊙ step0

    univalent : Univalent
    univalent = univalenceFrom≃ univ≃

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
            ump : fst ∘′ (f &&& g) ≡ f × snd ∘′ (f &&& g) ≡ g
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
          module _ {y : X → A × B} (eq : fst ∘′ y ≡ f × snd ∘′ y ≡ g) (x : X) where
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
