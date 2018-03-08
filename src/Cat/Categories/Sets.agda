{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Sets where

open import Cubical
open import Agda.Primitive
open import Data.Product
import Function

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.Product

module _ (ℓ : Level) where
  private
    open RawCategory
    open IsCategory
    open import Cubical.Univalence
    open import Cubical.NType.Properties
    open import Cubical.Universe

    SetsRaw : RawCategory (lsuc ℓ) ℓ
    Object SetsRaw = hSet
    Arrow SetsRaw (T , _) (U , _) = T → U
    𝟙 SetsRaw = Function.id
    _∘_ SetsRaw = Function._∘′_

    SetsIsCategory : IsCategory SetsRaw
    isAssociative SetsIsCategory = refl
    proj₁ (isIdentity SetsIsCategory) = funExt λ _ → refl
    proj₂ (isIdentity SetsIsCategory) = funExt λ _ → refl
    arrowsAreSets SetsIsCategory {B = (_ , s)} = setPi λ _ → s
    univalent SetsIsCategory = {!!}

  𝓢𝓮𝓽 Sets : Category (lsuc ℓ) ℓ
  Category.raw 𝓢𝓮𝓽 = SetsRaw
  Category.isCategory 𝓢𝓮𝓽 = SetsIsCategory
  Sets = 𝓢𝓮𝓽

module _ {ℓ : Level} where
  private
    𝓢 = 𝓢𝓮𝓽 ℓ
    open Category 𝓢
    open import Cubical.Sigma

    module _ (0A 0B : Object) where
      private
        A : Set ℓ
        A = proj₁ 0A
        sA : isSet A
        sA = proj₂ 0A
        B : Set ℓ
        B = proj₁ 0B
        sB : isSet B
        sB = proj₂ 0B
        0A×0B : Object
        0A×0B = (A × B) , sigPresSet sA λ _ → sB

        module _ {X A B : Set ℓ} (f : X → A) (g : X → B) where
          _&&&_ : (X → A × B)
          _&&&_ x = f x , g x
        module _ {0X : Object} where
          X = proj₁ 0X
          module _ (f : X → A ) (g : X → B) where
            lem : proj₁ Function.∘′ (f &&& g) ≡ f × proj₂ Function.∘′ (f &&& g) ≡ g
            proj₁ lem = refl
            proj₂ lem = refl

        rawProduct : RawProduct 𝓢 0A 0B
        RawProduct.object rawProduct = 0A×0B
        RawProduct.proj₁  rawProduct = Data.Product.proj₁
        RawProduct.proj₂  rawProduct = Data.Product.proj₂

        isProduct : IsProduct 𝓢 _ _ rawProduct
        IsProduct.isProduct isProduct {X = X} f g
          = (f &&& g) , lem {0X = X} f g

      product : Product 𝓢 0A 0B
      Product.raw       product = rawProduct
      Product.isProduct product = isProduct

  instance
    SetsHasProducts : HasProducts 𝓢
    SetsHasProducts = record { product = product }

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  -- Covariant Presheaf
  Representable : Set (ℓa ⊔ lsuc ℓb)
  Representable = Functor ℂ (𝓢𝓮𝓽 ℓb)

  -- Contravariant Presheaf
  Presheaf : Set (ℓa ⊔ lsuc ℓb)
  Presheaf = Functor (opposite ℂ) (𝓢𝓮𝓽 ℓb)

  open Category ℂ

  -- The "co-yoneda" embedding.
  representable : Category.Object ℂ → Representable
  representable A = record
    { raw = record
      { omap = λ B → ℂ [ A , B ] , arrowsAreSets
      ; fmap = ℂ [_∘_]
      }
    ; isFunctor = record
      { isIdentity = funExt λ _ → proj₂ isIdentity
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
      { isIdentity = funExt λ x → proj₁ isIdentity
      ; isDistributive = funExt λ x → isAssociative
      }
    }
