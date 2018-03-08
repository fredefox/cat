-- | The category of homotopy sets
{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Sets where

open import Agda.Primitive
open import Data.Product
import Function

open import Cubical hiding (inverse ; _≃_ {- ; obverse ; recto-verso ; verso-recto -} )
open import Cubical.Univalence using (_≃_ ; ua)
open import Cubical.GradLemma

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.Product
open import Cat.Wishlist

module _ (ℓ : Level) where
  private
    open import Cubical.Univalence
    open import Cubical.NType.Properties
    open import Cubical.Universe

    SetsRaw : RawCategory (lsuc ℓ) ℓ
    RawCategory.Object SetsRaw = hSet
    RawCategory.Arrow  SetsRaw (T , _) (U , _) = T → U
    RawCategory.𝟙      SetsRaw = Function.id
    RawCategory._∘_    SetsRaw = Function._∘′_

    open RawCategory SetsRaw
    open Univalence  SetsRaw

    isIdentity : IsIdentity Function.id
    proj₁ isIdentity = funExt λ _ → refl
    proj₂ isIdentity = funExt λ _ → refl

    arrowsAreSets : ArrowsAreSets
    arrowsAreSets {B = (_ , s)} = setPi λ _ → s

    module _ {hA hB : Object} where
      private
        A = proj₁ hA
        isSetA : isSet A
        isSetA = proj₂ hA
        B = proj₁ hB
        isSetB : isSet B
        isSetB = proj₂ hB

        toIsomorphism : A ≃ B → hA ≅ hB
        toIsomorphism e = obverse , inverse , verso-recto , recto-verso
          where
          open _≃_ e

        fromIsomorphism : hA ≅ hB → A ≃ B
        fromIsomorphism iso = con obverse (gradLemma obverse inverse recto-verso verso-recto)
          where
          obverse : A → B
          obverse = proj₁ iso
          inverse : B → A
          inverse = proj₁ (proj₂ iso)
          -- FIXME IsInverseOf should change name to AreInverses and the
          -- ordering should be swapped.
          areInverses : IsInverseOf {A = hA} {hB} obverse inverse
          areInverses = proj₂ (proj₂ iso)
          verso-recto : ∀ a → (inverse Function.∘ obverse) a ≡ a
          verso-recto a i = proj₁ areInverses i a
          recto-verso : ∀ b → (obverse Function.∘ inverse) b ≡ b
          recto-verso b i = proj₂ areInverses i b

      univalent : isEquiv (hA ≡ hB) (hA ≅ hB) (id-to-iso (λ {A} {B} → isIdentity {A} {B}) hA hB)
      univalent = gradLemma obverse inverse verso-recto recto-verso
        where
        obverse : hA ≡ hB → hA ≅ hB
        obverse eq = {!res!}
          where
          -- Problem: How do I extract this equality from `eq`?
          eqq : A ≡ B
          eqq = {!!}
          eq' : A ≃ B
          eq' = fromEquality eqq
          -- Problem: Why does this not satisfy the goal?
          res : hA ≅ hB
          res = toIsomorphism eq'

        inverse : hA ≅ hB → hA ≡ hB
        inverse iso = res
          where
          eq : A ≡ B
          eq = ua (fromIsomorphism iso)

          -- Use the fact that being an h-level level is a mere proposition.
          -- This is almost provable using `Wishlist.isSetIsProp` - although
          -- this creates homogenous paths.
          isSetEq : (λ i → isSet (eq i)) [ isSetA ≡ isSetB ]
          isSetEq = {!!}

          res : hA ≡ hB
          proj₁ (res i) = eq i
          proj₂ (res i) = isSetEq i

        -- FIXME Either the name of inverse/obverse is flipped or
        -- recto-verso/verso-recto is flipped.
        recto-verso : ∀ y → (inverse Function.∘ obverse) y ≡ y
        recto-verso x = {!!}
        verso-recto : ∀ x → (obverse Function.∘ inverse) x ≡ x
        verso-recto x = {!!}

    SetsIsCategory : IsCategory SetsRaw
    IsCategory.isAssociative SetsIsCategory = refl
    IsCategory.isIdentity    SetsIsCategory {A} {B} = isIdentity    {A} {B}
    IsCategory.arrowsAreSets SetsIsCategory {A} {B} = arrowsAreSets {A} {B}
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
