{-# OPTIONS --allow-unsolved-metas --cubical --caching #-}
module Cat.Categories.Fun where

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor
import Cat.Category.NaturalTransformation
  as NaturalTransformation

module Fun {ℓc ℓc' ℓd ℓd' : Level} (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  open NaturalTransformation ℂ 𝔻 public hiding (module Properties)
  private
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻

    module _ where
      -- Functor categories. Objects are functors, arrows are natural transformations.
      raw : RawCategory (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
      RawCategory.Object   raw = Functor ℂ 𝔻
      RawCategory.Arrow    raw = NaturalTransformation
      RawCategory.identity raw {F} = identity F
      RawCategory._<<<_    raw {F} {G} {H} = NT[_∘_] {F} {G} {H}

    module _ where
      open RawCategory raw hiding (identity)
      open NaturalTransformation.Properties ℂ 𝔻

      isPreCategory : IsPreCategory raw
      IsPreCategory.isAssociative isPreCategory {A} {B} {C} {D} = isAssociative {A} {B} {C} {D}
      IsPreCategory.isIdentity    isPreCategory {A} {B} = isIdentity {A} {B}
      IsPreCategory.arrowsAreSets isPreCategory {F} {G} = naturalTransformationIsSet {F} {G}

    open IsPreCategory isPreCategory hiding (identity)

    -- There used to be some work-in-progress on this theorem, please go back to
    -- this point in time to see it:
    --
    -- commit 6b7d66b7fc936fe3674b2fd9fa790bd0e3fec12f
    -- Author: Frederik Hanghøj Iversen <fhi.1990@gmail.com>
    -- Date:   Fri Apr 13 15:26:46 2018 +0200
    postulate univalent : Univalent

    isCategory : IsCategory raw
    IsCategory.isPreCategory isCategory = isPreCategory
    IsCategory.univalent     isCategory = univalent

  Fun : Category (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  Category.raw        Fun = raw
  Category.isCategory Fun = isCategory

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    open import Cat.Categories.Sets
    open NaturalTransformation (opposite ℂ) (𝓢𝓮𝓽 ℓ')
    module K = Fun (opposite ℂ) (𝓢𝓮𝓽 ℓ')
    module F = Category K.Fun

    -- Restrict the functors to Presheafs.
    raw : RawCategory (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
    raw = record
      { Object = Presheaf ℂ
      ; Arrow = NaturalTransformation
      ; identity = λ {F} → identity F
      ; _<<<_ = λ {F G H} → NT[_∘_] {F = F} {G = G} {H = H}
      }

  --   isCategory : IsCategory raw
  --   isCategory = record
  --     { isAssociative =
  --       λ{ {A} {B} {C} {D} {f} {g} {h}
  --       → F.isAssociative {A} {B} {C} {D} {f} {g} {h}
  --       }
  --     ; isIdentity =
  --       λ{ {A} {B} {f}
  --       → F.isIdentity {A} {B} {f}
  --       }
  --     ; arrowsAreSets =
  --       λ{ {A} {B}
  --       → F.arrowsAreSets {A} {B}
  --       }
  --     ; univalent =
  --       λ{ {A} {B}
  --       → F.univalent {A} {B}
  --       }
  --     }

  -- Presh : Category (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  -- Category.raw        Presh = raw
  -- Category.isCategory Presh = isCategory
