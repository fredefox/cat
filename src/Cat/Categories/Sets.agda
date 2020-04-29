-- | The category of homotopy sets
{-# OPTIONS --cubical --caching #-}
module Cat.Categories.Sets where

open import Cat.Prelude as P
open import Cat.Equivalence
open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.Product
open import Cat.Categories.Opposite

_⊙_ : {ℓa ℓb ℓc : Level} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} → (A ≃ B) → (B ≃ C) → A ≃ C
eqA ⊙ eqB = compEquiv eqA eqB

sym≃ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → A ≃ B → B ≃ A
sym≃ = invEquiv

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

    open IsPreCategory isPreCat
    module _ {hA hB : Object} where
      open Σ hA renaming (fst to A ; snd to sA)
      open Σ hB renaming (fst to B ; snd to sB)

      univ≃ : (hA ≡ hB) ≃ (hA ≊ hB)
      univ≃
        = equivSigProp (λ A → isSetIsProp)
        ⊙ univalence
        ⊙ equivSig {B = isEquiv} {B' = TypeIsomorphism} (equiv≃iso sA sB)

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
        productObject = (A × B) , setSig sA λ _ → sB

        module _ {X A B : Set ℓ} (f : X → A) (g : X → B) where
          _&&&_ : (X → A × B)
          _&&&_ x = f x , g x

        module _ (hX : Object) where
          open Σ hX renaming (fst to X)
          module _ (f : X → A ) (g : X → B) where
            ump : (fst ∘ (f &&& g) ≡ f) × (snd ∘ (f &&& g) ≡ g)
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
          module _ {y : X → A × B} (eq : (fst ∘ y ≡ f) × (snd ∘ y ≡ g)) (x : X) where
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
