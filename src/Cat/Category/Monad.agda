{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Cat.Category.Monad where

open import Agda.Primitive

open import Data.Product

open import Cubical

open import Cat.Category
open import Cat.Category.Functor as F
open import Cat.Category.NaturalTransformation
open import Cat.Categories.Fun

-- "A monad in the monoidal form" [voe]
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

    η : Transformation F.identity R
    η = proj₁ ηNat
    μ : Transformation F[ R ∘ R ] R
    μ = proj₁ μNat

    private
      module R  = Functor R
      module RR = Functor F[ R ∘ R ]
      module _ {X : Object} where
        -- module IdRX = Functor (F.identity {C = RX})
        ηX  : ℂ [ X                    , R.func* X ]
        ηX = η X
        RηX : ℂ [ R.func* X            , R.func* (R.func* X) ] -- ℂ [ R.func* X , {!R.func* (R.func* X))!} ]
        RηX = R.func→ ηX
        ηRX = η (R.func* X)
        IdRX : Arrow (R.func* X) (R.func* X)
        IdRX = 𝟙 {R.func* X}

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

  record Monad : Set ℓ where
    field
      raw : RawMonad
      isMonad : IsMonad raw
    open IsMonad isMonad public

-- "A monad in the Kleisli form" [voe]
module Kleisli {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    ℓ = ℓa ⊔ ℓb

  open Category ℂ hiding (IsIdentity)
  record RawMonad : Set ℓ where
    field
      RR : Object → Object
      -- Note name-change from [voe]
      ζ : {X : Object} → ℂ [ X , RR X ]
      rr : {X Y : Object} → ℂ [ X , RR Y ] → ℂ [ RR X , RR Y ]
    -- Name suggestions are welcome!
    IsIdentity     = {X : Object}
      → rr ζ ≡ 𝟙 {RR X}
    IsNatural      = {X Y : Object}   (f : ℂ [ X , RR Y ])
      → (ℂ [ rr f ∘ ζ ]) ≡ f
    IsDistributive = {X Y Z : Object} (g : ℂ [ Y , RR Z ]) (f : ℂ [ X , RR Y ])
      → ℂ [ rr g ∘ rr f ] ≡ rr (ℂ [ rr g ∘ f ])

  record IsMonad (raw : RawMonad) : Set ℓ where
    open RawMonad raw public
    field
      isIdentity     : IsIdentity
      isNatural      : IsNatural
      isDistributive : IsDistributive

  record Monad : Set ℓ where
    field
      raw : RawMonad
      isMonad : IsMonad raw
    open IsMonad isMonad public

-- Problem 2.3
module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} where
  private
    open Category ℂ using (Object ; Arrow ; 𝟙)
    open Functor using (func* ; func→)
    module M = Monoidal ℂ
    module K = Kleisli ℂ

    module _ (m : M.RawMonad) where
      private
        open M.RawMonad m
        module Kraw = K.RawMonad

      RR : Object → Object
      RR = func* R

      R→ : {A B : Object} → ℂ [ A , B ] → ℂ [ RR A , RR B ]
      R→ = func→ R

      ζ : {X : Object} → ℂ [ X , RR X ]
      ζ = {!!}

      rr : {X Y : Object} → ℂ [ X , RR Y ] → ℂ [ RR X , RR Y ]
      -- Order is different now!
      rr {X} {Y} f = ℂ [ f ∘ {!!} ]
        where
          μY : ℂ [ func* F[ R ∘ R ] Y , func* R Y ]
          μY = μ Y
          ζY : ℂ [ Y , RR Y ]
          ζY = ζ {Y}

      forthRaw : K.RawMonad
      Kraw.RR forthRaw = RR
      Kraw.ζ  forthRaw = ζ
      Kraw.rr forthRaw = rr

    module _ {raw : M.RawMonad} (m : M.IsMonad raw) where
      open M.IsMonad m
      module Kraw = K.RawMonad (forthRaw raw)
      module Kis = K.IsMonad
      isIdentity : Kraw.IsIdentity
      isIdentity = {!!}

      isNatural : Kraw.IsNatural
      isNatural = {!!}

      isDistributive : Kraw.IsDistributive
      isDistributive = {!!}

      forthIsMonad : K.IsMonad (forthRaw raw)
      Kis.isIdentity forthIsMonad = isIdentity
      Kis.isNatural forthIsMonad = isNatural
      Kis.isDistributive forthIsMonad = isDistributive

    forth : M.Monad → K.Monad
    Kleisli.Monad.raw     (forth m) = forthRaw (M.Monad.raw m)
    Kleisli.Monad.isMonad (forth m) = forthIsMonad (M.Monad.isMonad m)

    eqv : isEquiv M.Monad K.Monad forth
    eqv = {!!}

  Monoidal≃Kleisli : M.Monad ≃ K.Monad
  Monoidal≃Kleisli = forth , eqv
