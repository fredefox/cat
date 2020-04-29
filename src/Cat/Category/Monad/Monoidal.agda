{---
Monoidal formulation of monads
 ---}
{-# OPTIONS --cubical #-}
open import Agda.Primitive

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor as F
open import Cat.Categories.Fun

module Cat.Category.Monad.Monoidal {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where

-- "A monad in the monoidal form" [voe]
private
  ℓ = ℓa ⊔ ℓb

open Category ℂ using (Object ; Arrow ; identity ; _<<<_)
open import Cat.Category.NaturalTransformation ℂ ℂ
  using (NaturalTransformation ; Transformation ; Natural ; NaturalTransformation≡)

record RawMonad : Set ℓ where
  field
    R      : EndoFunctor ℂ
    pureNT : NaturalTransformation Functors.identity R
    joinNT : NaturalTransformation F[ R ∘ R ] R

  Romap = Functor.omap R
  fmap = Functor.fmap R

  -- Note that `pureT` and `joinT` differs from their definition in the
  -- kleisli formulation only by having an explicit parameter.
  pureT : Transformation Functors.identity R
  pureT = fst pureNT

  pure : {X : Object} → ℂ [ X , Romap X ]
  pure = pureT _

  pureN : Natural Functors.identity R pureT
  pureN = snd pureNT

  joinT : Transformation F[ R ∘ R ] R
  joinT = fst joinNT
  join : {X : Object} → ℂ [ Romap (Romap X) , Romap X ]
  join = joinT _
  joinN : Natural F[ R ∘ R ] R joinT
  joinN = snd joinNT

  bind : {X Y : Object} → ℂ [ X , Romap Y ] → ℂ [ Romap X , Romap Y ]
  bind {X} {Y} f = join <<< fmap f

  IsAssociative : Set _
  IsAssociative = {X : Object}
    -- R and join commute
    → joinT X <<< fmap join ≡ join <<< join
  IsInverse : Set _
  IsInverse = {X : Object}
    -- Talks about R's action on objects
    → (join <<< pure      ≡ identity {Romap X})
    -- Talks about R's action on arrows
    × (join <<< fmap pure ≡ identity {Romap X})
  IsNatural = ∀ {X Y} (f : Arrow X (Romap Y))
    → join <<< fmap f <<< pure ≡ f
  IsDistributive = ∀ {X Y Z} (g : Arrow Y (Romap Z)) (f : Arrow X (Romap Y))
    → join <<< fmap g <<< (join <<< fmap f)
    ≡ join <<< fmap (join <<< fmap g <<< f)

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
    join <<< fmap f <<< pure     ≡⟨ sym ℂ.isAssociative ⟩
    join <<< (fmap f <<< pure)   ≡⟨ cong (λ φ → join <<< φ) (sym (pureN f)) ⟩
    join <<< (pure <<< f)        ≡⟨ ℂ.isAssociative ⟩
    join <<< pure <<< f          ≡⟨ cong (λ φ → φ <<< f) (fst isInverse) ⟩
    identity <<< f               ≡⟨ ℂ.leftIdentity ⟩
    f                            ∎

  isDistributive : IsDistributive
  isDistributive {X} {Y} {Z} g f = begin
       join <<< fmap g <<< (join <<< fmap f)
       ≡⟨ Category.isAssociative ℂ ⟩
       join <<< fmap g <<< join <<< fmap f
       ≡⟨ cong (_<<< fmap f) (sym ℂ.isAssociative) ⟩
       (join <<< (fmap g <<< join)) <<< fmap f
       ≡⟨ cong (λ φ → φ <<< fmap f) (cong (_<<<_ join) (sym (joinN g))) ⟩
       (join <<< (join <<< R².fmap g)) <<< fmap f
       ≡⟨ cong (_<<< fmap f) ℂ.isAssociative ⟩
       ((join <<< join) <<< R².fmap g) <<< fmap f
       ≡⟨⟩
       join <<< join <<< R².fmap g <<< fmap f
       ≡⟨ sym ℂ.isAssociative ⟩
       (join <<< join) <<< (R².fmap g <<< fmap f)
       ≡⟨ cong (λ φ → φ <<< (R².fmap g <<< fmap f)) (sym isAssociative) ⟩
       (join <<< fmap join) <<< (R².fmap g <<< fmap f)
       ≡⟨ sym ℂ.isAssociative ⟩
       join <<< (fmap join <<< (R².fmap g <<< fmap f))
       ≡⟨ cong (_<<<_ join) ℂ.isAssociative ⟩
       join <<< (fmap join <<< R².fmap g <<< fmap f)
       ≡⟨⟩
       join <<< (fmap join <<< fmap (fmap g) <<< fmap f)
       ≡⟨ cong (λ φ → join <<< φ) (sym distrib3) ⟩
       join <<< fmap (join <<< fmap g <<< f)
       ∎
    where
    module R² = Functor F[ R ∘ R ]
    distrib3 : ∀ {A B C D} {a : Arrow C D} {b : Arrow B C} {c : Arrow A B}
      → R.fmap (a <<< b <<< c)
      ≡ R.fmap a <<< R.fmap b <<< R.fmap c
    distrib3 {a = a} {b} {c} = begin
      R.fmap (a <<< b <<< c)              ≡⟨ R.isDistributive ⟩
      R.fmap (a <<< b) <<< R.fmap c       ≡⟨ cong (_<<< _) R.isDistributive ⟩
      R.fmap a <<< R.fmap b <<< R.fmap c  ∎

record Monad : Set ℓ where
  no-eta-equality
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
      e1 = Category.arrowsAreSets ℂ _ _ (fst xX) (fst yX)
      e2 = Category.arrowsAreSets ℂ _ _ (snd xX) (snd yX)

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
    eqIsMonad = lemPropF propIsMonad _ _ eq

  Monad≡ : m ≡ n
  Monad.raw     (Monad≡ i) = eq i
  Monad.isMonad (Monad≡ i) = eqIsMonad i
