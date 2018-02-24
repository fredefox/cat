{-# OPTIONS --cubical #-}
module Cat.Category.Monad where

open import Agda.Primitive

open import Data.Product

open import Cubical

open import Cat.Category
open import Cat.Category.Functor as F
open import Cat.Category.NaturalTransformation
open import Cat.Categories.Fun

-- "A monad in the monoidal form" [vlad]
module Monoidal {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    ℓ = ℓa ⊔ ℓb

  open Category ℂ hiding (IsAssociative)
  open NaturalTransformation ℂ ℂ
  record RawMonad : Set ℓ where
    field
      R : Functor ℂ ℂ
      -- pure
      ηNat : NaturalTransformation F.identity R
      -- (>=>)
      μNat : NaturalTransformation F[ R ∘ R ] R

    module R  = Functor R
    module RR = Functor F[ R ∘ R ]
    private
      module _ {X : Object} where
        -- module IdRX = Functor (F.identity {C = RX})

        η : Transformation F.identity R
        η = proj₁ ηNat
        ηX  : ℂ [ X                    , R.func* X ]
        ηX = η X
        RηX : ℂ [ R.func* X            , R.func* (R.func* X) ] -- ℂ [ R.func* X , {!R.func* (R.func* X))!} ]
        RηX = R.func→ ηX
        ηRX = η (R.func* X)
        IdRX : Arrow (R.func* X) (R.func* X)
        IdRX = 𝟙 {R.func* X}

        μ : Transformation F[ R ∘ R ] R
        μ = proj₁ μNat
        μX  : ℂ [ RR.func* X           , R.func* X ]
        μX = μ X
        RμX : ℂ [ R.func* (RR.func* X) , RR.func* X ]
        RμX = R.func→ μX
        μRX : ℂ [ RR.func* (R.func* X) , R.func* (R.func* X) ]
        μRX = μ (R.func* X)

        IsAssociative' : Set _
        IsAssociative' = ℂ [ μX ∘ RμX ] ≡ ℂ [ μX ∘ μRX ]
        IsInverse' : Set _
        IsInverse'
          = ℂ [ μX ∘ ηRX ] ≡ IdRX
          × ℂ [ μX ∘ RηX ] ≡ IdRX

    -- We don't want the objects to be indexes of the type, but rather just
    -- universally quantify over *all* objects of the category.
    IsAssociative = {X : Object} → IsAssociative' {X}
    IsInverse = {X : Object} → IsInverse' {X}

  record IsMonad (raw : RawMonad) : Set ℓ where
    open RawMonad raw public
    field
      isAssociative : IsAssociative
      isInverse : IsInverse
