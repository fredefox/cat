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
    Object SetsRaw = Cubical.Universe.0-Set
    Arrow SetsRaw (T , _) (U , _) = T → U
    𝟙 SetsRaw = Function.id
    _∘_ SetsRaw = Function._∘′_

    setIsSet : (A : Set ℓ) → isSet A
    setIsSet A x y p q = {!ua!}

    SetsIsCategory : IsCategory SetsRaw
    assoc SetsIsCategory = refl
    proj₁ (ident SetsIsCategory) = funExt λ _ → refl
    proj₂ (ident SetsIsCategory) = funExt λ _ → refl
    arrowIsSet SetsIsCategory {B = (_ , s)} = setPi λ _ → s
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
        instance
          isProduct : IsProduct 𝓢 {0A} {0B} {0A×0B} proj₁ proj₂
          isProduct {X = X} f g = (f &&& g) , lem {0X = X} f g

      product : Product {ℂ = 𝓢} 0A 0B
      product = record
        { obj = 0A×0B
        ; proj₁ = Data.Product.proj₁
        ; proj₂ = Data.Product.proj₂
        ; isProduct = λ { {X} → isProduct {X = X}}
        }

  instance
    SetsHasProducts : HasProducts 𝓢
    SetsHasProducts = record { product = product }

module _ {ℓa ℓb : Level} where
  module _ (ℂ : Category ℓa ℓb) where
    -- Covariant Presheaf
    Representable : Set (ℓa ⊔ lsuc ℓb)
    Representable = Functor ℂ (𝓢𝓮𝓽 ℓb)

    -- Contravariant Presheaf
    Presheaf : Set (ℓa ⊔ lsuc ℓb)
    Presheaf = Functor (Opposite ℂ) (𝓢𝓮𝓽 ℓb)

  -- The "co-yoneda" embedding.
  representable : {ℂ : Category ℓa ℓb} → Category.Object ℂ → Representable ℂ
  representable {ℂ = ℂ} A = record
    { raw = record
      { func* = λ B → ℂ [ A , B ] , arrowIsSet
      ; func→ = ℂ [_∘_]
      }
    ; isFunctor = record
      { ident = funExt λ _ → proj₂ ident
      ; distrib = funExt λ x → sym assoc
      }
    }
    where
      open Category ℂ

  -- Alternate name: `yoneda`
  presheaf : {ℂ : Category ℓa ℓb} → Category.Object (Opposite ℂ) → Presheaf ℂ
  presheaf {ℂ = ℂ} B = record
    { raw = record
      { func* = λ A → ℂ [ A , B ] , arrowIsSet
      ; func→ = λ f g → ℂ [ g ∘ f ]
    }
    ; isFunctor = record
      { ident = funExt λ x → proj₁ ident
      ; distrib = funExt λ x → assoc
      }
    }
    where
      open Category ℂ
