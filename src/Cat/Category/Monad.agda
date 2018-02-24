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
        IsAssociative' : Set _
        IsAssociative' = μ X ∘ R.func→ (μ X) ≡ μ X ∘ μ (R.func* X)
        IsInverse' : Set _
        IsInverse'
          = μ X ∘ η (R.func* X) ≡ 𝟙
          × μ X ∘ R.func→ (η X) ≡ 𝟙

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
    -- Note the correspondance with Haskell:
    --
    --     RR ~ m
    --     ζ  ~ pure
    --     rr ~ flip (>>=)
    --
    -- Where those things have these types:
    --
    --     m : 𝓤 → 𝓤
    --     pure : x → m x
    --     flip (>>=) :: (a → m b) → m a → m b
    --
    pure : {X : Object} → ℂ [ X , RR X ]
    pure = ζ
    -- Why is (>>=) not implementable?
    --
    -- (>>=) : m a -> (a -> m b) -> m b
    -- (>=>) : (a -> m b) -> (b -> m c) -> a -> m c
    _>=>_ : {A B C : Object} → ℂ [ A , RR B ] → ℂ [ B , RR C ] → ℂ [ A , RR C ]
    f >=> g = ℂ [ rr g ∘ f ]

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
    open Category ℂ using (Object ; Arrow ; 𝟙 ; _∘_)
    open Functor using (func* ; func→)
    module M = Monoidal ℂ
    module K = Kleisli ℂ

    -- Note similarity with locally defined things in Kleisly.RawMonad!!
    module _ (m : M.RawMonad) where
      private
        open M.RawMonad m
        module Kraw = K.RawMonad

        RR : Object → Object
        RR = func* R

        R→ : {A B : Object} → ℂ [ A , B ] → ℂ [ RR A , RR B ]
        R→ = func→ R

        ζ : {X : Object} → ℂ [ X , RR X ]
        ζ {X} = η X

        rr : {X Y : Object} → ℂ [ X , RR Y ] → ℂ [ RR X , RR Y ]
        rr {X} {Y} f = ℂ [ μ Y ∘ func→ R f ]

      forthRaw : K.RawMonad
      Kraw.RR forthRaw = RR
      Kraw.ζ  forthRaw = ζ
      Kraw.rr forthRaw = rr

    module _ {raw : M.RawMonad} (m : M.IsMonad raw) where
      open M.IsMonad m
      open K.RawMonad (forthRaw raw)
      module Kis = K.IsMonad

      isIdentity : IsIdentity
      isIdentity {X} = begin
        rr ζ                      ≡⟨⟩
        rr (η X)                  ≡⟨⟩
        ℂ [ μ X ∘ func→ R (η X) ] ≡⟨ proj₂ isInverse ⟩
        𝟙 ∎

      module R = Functor R
      isNatural : IsNatural
      isNatural {X} {Y} f = begin
        rr f ∘ ζ                  ≡⟨⟩
        rr f ∘ η X                ≡⟨⟩
        μ Y ∘ R.func→ f ∘ η X     ≡⟨ sym ℂ.isAssociative ⟩
        μ Y ∘ (R.func→ f ∘ η X)   ≡⟨ cong (λ φ → μ Y ∘ φ) (sym (ηN f)) ⟩
        μ Y ∘ (η (R.func* Y) ∘ f) ≡⟨ ℂ.isAssociative ⟩
        μ Y ∘ η (R.func* Y) ∘ f   ≡⟨ cong (λ φ → φ ∘ f) (proj₁ isInverse) ⟩
        𝟙 ∘ f                     ≡⟨ proj₂ ℂ.isIdentity ⟩
        f ∎
        where
          module ℂ = Category ℂ
          open NaturalTransformation
          ηN : Natural ℂ ℂ F.identity R η
          ηN = proj₂ ηNat

      isDistributive : IsDistributive
      isDistributive = {!!}

      forthIsMonad : K.IsMonad (forthRaw raw)
      Kis.isIdentity forthIsMonad = isIdentity
      Kis.isNatural forthIsMonad = isNatural
      Kis.isDistributive forthIsMonad = isDistributive

    forth : M.Monad → K.Monad
    Kleisli.Monad.raw     (forth m) = forthRaw (M.Monad.raw m)
    Kleisli.Monad.isMonad (forth m) = forthIsMonad (M.Monad.isMonad m)

    back : K.Monad → M.Monad
    back = {!!}

    fortheq : (m : K.Monad) → forth (back m) ≡ m
    fortheq = {!!}

    backeq : (m : M.Monad) → back (forth m) ≡ m
    backeq = {!!}

    open import Cubical.GradLemma
    eqv : isEquiv M.Monad K.Monad forth
    eqv = gradLemma forth back fortheq backeq

  Monoidal≃Kleisli : M.Monad ≃ K.Monad
  Monoidal≃Kleisli = forth , eqv
