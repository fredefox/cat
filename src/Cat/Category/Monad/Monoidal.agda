{---
Monoidal formulation of monads
 ---}
{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Agda.Primitive

open import Data.Product

open import Cubical
open import Cubical.NType.Properties using (lemPropF ; lemSig ;  lemSigP)
open import Cubical.GradLemma        using (gradLemma)

open import Cat.Category
open import Cat.Category.Functor as F
open import Cat.Category.NaturalTransformation
open import Cat.Categories.Fun

module Cat.Category.Monad.Monoidal {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where

-- "A monad in the monoidal form" [voe]
private
  ℓ = ℓa ⊔ ℓb

open Category ℂ using (Object ; Arrow ; 𝟙 ; _∘_)
open NaturalTransformation ℂ ℂ
record RawMonad : Set ℓ where
  field
    R      : EndoFunctor ℂ
    pureNT : NaturalTransformation F.identity R
    joinNT : NaturalTransformation F[ R ∘ R ] R

  -- Note that `pureT` and `joinT` differs from their definition in the
  -- kleisli formulation only by having an explicit parameter.
  pureT : Transformation F.identity R
  pureT = proj₁ pureNT
  pureN : Natural F.identity R pureT
  pureN = proj₂ pureNT

  joinT : Transformation F[ R ∘ R ] R
  joinT = proj₁ joinNT
  joinN : Natural F[ R ∘ R ] R joinT
  joinN = proj₂ joinNT

  Romap = Functor.omap R
  Rfmap = Functor.fmap R

  bind : {X Y : Object} → ℂ [ X , Romap Y ] → ℂ [ Romap X , Romap Y ]
  bind {X} {Y} f = joinT Y ∘ Rfmap f

  IsAssociative : Set _
  IsAssociative = {X : Object}
    → joinT X ∘ Rfmap (joinT X) ≡ joinT X ∘ joinT (Romap X)
  IsInverse : Set _
  IsInverse = {X : Object}
    → joinT X ∘ pureT (Romap X) ≡ 𝟙
    × joinT X ∘ Rfmap (pureT X) ≡ 𝟙
  IsNatural = ∀ {X Y} f → joinT Y ∘ Rfmap f ∘ pureT X ≡ f
  IsDistributive = ∀ {X Y Z} (g : Arrow Y (Romap Z)) (f : Arrow X (Romap Y))
    → joinT Z ∘ Rfmap g ∘ (joinT Y ∘ Rfmap f)
    ≡ joinT Z ∘ Rfmap (joinT Z ∘ Rfmap g ∘ f)

record IsMonad (raw : RawMonad) : Set ℓ where
  open RawMonad raw public
  field
    isAssociative : IsAssociative
    isInverse     : IsInverse

  private
    module R = Functor R
    module ℂ = Category ℂ

  isNatural : IsNatural
  isNatural {X} {Y} f = begin
    joinT Y ∘ R.fmap f ∘ pureT X     ≡⟨ sym ℂ.isAssociative ⟩
    joinT Y ∘ (R.fmap f ∘ pureT X)   ≡⟨ cong (λ φ → joinT Y ∘ φ) (sym (pureN f)) ⟩
    joinT Y ∘ (pureT (R.omap Y) ∘ f) ≡⟨ ℂ.isAssociative ⟩
    joinT Y ∘ pureT (R.omap Y) ∘ f   ≡⟨ cong (λ φ → φ ∘ f) (proj₁ isInverse) ⟩
    𝟙 ∘ f                            ≡⟨ ℂ.leftIdentity ⟩
    f                                ∎

  isDistributive : IsDistributive
  isDistributive {X} {Y} {Z} g f = sym aux
    where
    module R² = Functor F[ R ∘ R ]
    distrib3 : ∀ {A B C D} {a : Arrow C D} {b : Arrow B C} {c : Arrow A B}
      → R.fmap (a ∘ b ∘ c)
      ≡ R.fmap a ∘ R.fmap b ∘ R.fmap c
    distrib3 {a = a} {b} {c} = begin
      R.fmap (a ∘ b ∘ c)               ≡⟨ R.isDistributive ⟩
      R.fmap (a ∘ b) ∘ R.fmap c       ≡⟨ cong (_∘ _) R.isDistributive ⟩
      R.fmap a ∘ R.fmap b ∘ R.fmap c ∎
    aux = begin
      joinT Z ∘ R.fmap (joinT Z ∘ R.fmap g ∘ f)
        ≡⟨ cong (λ φ → joinT Z ∘ φ) distrib3 ⟩
      joinT Z ∘ (R.fmap (joinT Z) ∘ R.fmap (R.fmap g) ∘ R.fmap f)
        ≡⟨⟩
      joinT Z ∘ (R.fmap (joinT Z) ∘ R².fmap g ∘ R.fmap f)
        ≡⟨ cong (_∘_ (joinT Z)) (sym ℂ.isAssociative) ⟩
      joinT Z ∘ (R.fmap (joinT Z) ∘ (R².fmap g ∘ R.fmap f))
        ≡⟨ ℂ.isAssociative ⟩
      (joinT Z ∘ R.fmap (joinT Z)) ∘ (R².fmap g ∘ R.fmap f)
        ≡⟨ cong (λ φ → φ ∘ (R².fmap g ∘ R.fmap f)) isAssociative ⟩
      (joinT Z ∘ joinT (R.omap Z)) ∘ (R².fmap g ∘ R.fmap f)
        ≡⟨ ℂ.isAssociative ⟩
      joinT Z ∘ joinT (R.omap Z) ∘ R².fmap g ∘ R.fmap f
        ≡⟨⟩
      ((joinT Z ∘ joinT (R.omap Z)) ∘ R².fmap g) ∘ R.fmap f
        ≡⟨ cong (_∘ R.fmap f) (sym ℂ.isAssociative) ⟩
      (joinT Z ∘ (joinT (R.omap Z) ∘ R².fmap g)) ∘ R.fmap f
        ≡⟨ cong (λ φ → φ ∘ R.fmap f) (cong (_∘_ (joinT Z)) (joinN g)) ⟩
      (joinT Z ∘ (R.fmap g ∘ joinT Y)) ∘ R.fmap f
        ≡⟨ cong (_∘ R.fmap f) ℂ.isAssociative ⟩
      joinT Z ∘ R.fmap g ∘ joinT Y ∘ R.fmap f
        ≡⟨ sym (Category.isAssociative ℂ) ⟩
      joinT Z ∘ R.fmap g ∘ (joinT Y ∘ R.fmap f)
        ∎

record Monad : Set ℓ where
  field
    raw     : RawMonad
    isMonad : IsMonad raw
  open IsMonad isMonad public

private
  module _ {m : RawMonad} where
    open RawMonad m
    propIsAssociative : isProp IsAssociative
    propIsAssociative x y i {X}
      = Category.arrowsAreSets ℂ _ _ (x {X}) (y {X}) i
    propIsInverse : isProp IsInverse
    propIsInverse x y i {X} = e1 i , e2 i
      where
      xX = x {X}
      yX = y {X}
      e1 = Category.arrowsAreSets ℂ _ _ (proj₁ xX) (proj₁ yX)
      e2 = Category.arrowsAreSets ℂ _ _ (proj₂ xX) (proj₂ yX)

  open IsMonad
  propIsMonad : (raw : _) → isProp (IsMonad raw)
  IsMonad.isAssociative (propIsMonad raw a b i) j
    = propIsAssociative {raw}
      (isAssociative a) (isAssociative b) i j
  IsMonad.isInverse     (propIsMonad raw a b i)
    = propIsInverse {raw}
      (isInverse a) (isInverse b) i

module _ {m n : Monad} (eq : Monad.raw m ≡ Monad.raw n) where
  private
    eqIsMonad : (λ i → IsMonad (eq i)) [ Monad.isMonad m ≡ Monad.isMonad n ]
    eqIsMonad = lemPropF propIsMonad eq

  Monad≡ : m ≡ n
  Monad.raw     (Monad≡ i) = eq i
  Monad.isMonad (Monad≡ i) = eqIsMonad i
