{---
Monads

This module presents two formulations of monads:

  * The standard monoidal presentation
  * Kleisli's presentation

The first one defines a monad in terms of an endofunctor and two natural
transformations. The second defines it in terms of a function on objects and a
pair of arrows.

These two formulations are proven to be equivalent:

    Monoidal.Monad ≃ Kleisli.Monad

The monoidal representation is exposed by default from this module.
 ---}

{-# OPTIONS --cubical #-}
module Cat.Category.Monad where

open import Cat.Prelude
open import Cat.Category
open import Cat.Category.Functor as F
import Cat.Category.NaturalTransformation
import Cat.Category.Monad.Monoidal
import Cat.Category.Monad.Kleisli
open import Cat.Categories.Fun

-- | The monoidal- and kleisli presentation of monads are equivalent.
module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Cat.Category.NaturalTransformation ℂ ℂ using (NaturalTransformation ; propIsNatural)
  private
    module ℂ = Category ℂ
    open ℂ using (Object ; Arrow ; identity ; _<<<_ ; _>>>_)

    module Monoidal = Cat.Category.Monad.Monoidal ℂ
    module Kleisli  = Cat.Category.Monad.Kleisli ℂ

    module _ (m : Monoidal.RawMonad) where
      open Monoidal.RawMonad m

      toKleisliRaw : Kleisli.RawMonad
      Kleisli.RawMonad.omap toKleisliRaw = Romap
      Kleisli.RawMonad.pure toKleisliRaw = pure
      Kleisli.RawMonad.bind toKleisliRaw = bind

    module _ {raw : Monoidal.RawMonad} (m : Monoidal.IsMonad raw) where
      open Monoidal.IsMonad m

      open Kleisli.RawMonad (toKleisliRaw raw) using (_>=>_)
      toKleisliIsMonad : Kleisli.IsMonad (toKleisliRaw raw)
      Kleisli.IsMonad.isIdentity     toKleisliIsMonad = begin
        bind pure ≡⟨⟩
        join <<< (fmap pure) ≡⟨ snd isInverse ⟩
        identity ∎
      Kleisli.IsMonad.isNatural      toKleisliIsMonad f = begin
        pure >=> f ≡⟨⟩
        pure >>> bind f ≡⟨⟩
        bind f <<< pure ≡⟨⟩
        (join <<< fmap f) <<< pure ≡⟨ isNatural f ⟩
        f ∎
      Kleisli.IsMonad.isDistributive toKleisliIsMonad f g = begin
        bind g >>> bind f ≡⟨⟩
        (join <<< fmap f) <<< (join <<< fmap g) ≡⟨ isDistributive f g ⟩
        join <<< fmap (join <<< fmap f <<< g) ≡⟨⟩
        bind (g >=> f) ∎
      -- Kleisli.IsMonad.isDistributive toKleisliIsMonad = isDistributive

    toKleisli : Monoidal.Monad → Kleisli.Monad
    Kleisli.Monad.raw     (toKleisli m) = toKleisliRaw     (Monoidal.Monad.raw     m)
    Kleisli.Monad.isMonad (toKleisli m) = toKleisliIsMonad (Monoidal.Monad.isMonad m)

    module _ (m : Kleisli.Monad) where
      open Kleisli.Monad m

      toMonoidalRaw : Monoidal.RawMonad
      Monoidal.RawMonad.R      toMonoidalRaw = R
      Monoidal.RawMonad.pureNT toMonoidalRaw = pureNT
      Monoidal.RawMonad.joinNT toMonoidalRaw = joinNT

      open Monoidal.RawMonad toMonoidalRaw renaming
        ( join to join*
        ; pure to pure*
        ; bind to bind*
        ; fmap to fmap*
        ) using ()

      toMonoidalIsMonad : Monoidal.IsMonad toMonoidalRaw
      Monoidal.IsMonad.isAssociative toMonoidalIsMonad = begin
        join* <<< fmap join* ≡⟨⟩
        join  <<< fmap join    ≡⟨ isNaturalForeign ⟩
        join  <<< join         ∎
      Monoidal.IsMonad.isInverse toMonoidalIsMonad {X} = inv-l , inv-r
        where
        inv-l = begin
          join <<< pure                ≡⟨ fst isInverse ⟩
          identity                     ∎
        inv-r = begin
          join* <<< fmap* pure*        ≡⟨⟩
          join <<< fmap pure           ≡⟨ snd isInverse ⟩
          identity                     ∎

    toMonoidal : Kleisli.Monad → Monoidal.Monad
    Monoidal.Monad.raw     (toMonoidal m) = toMonoidalRaw     m
    Monoidal.Monad.isMonad (toMonoidal m) = toMonoidalIsMonad m

    module _ (m : Kleisli.Monad) where
      private
        open Kleisli.Monad m
        bindEq : ∀ {X Y}
          → Kleisli.RawMonad.bind (toKleisliRaw (toMonoidalRaw m)) {X} {Y}
          ≡ bind
        bindEq {X} {Y} = funExt lem
          where
          lem : (f : Arrow X (omap Y))
            → bind (f >>> pure) >>> bind identity
            ≡ bind f
          lem f = begin
            join <<< fmap f
              ≡⟨⟩
            bind (f >>> pure) >>> bind identity
              ≡⟨ isDistributive _ _ ⟩
            bind ((f >>> pure) >=> identity)
              ≡⟨⟩
            bind ((f >>> pure) >>> bind identity)
              ≡⟨ cong bind ℂ.isAssociative ⟩
            bind (f >>> (pure >>> bind identity))
              ≡⟨⟩
            bind (f >>> (pure >=> identity))
              ≡⟨ cong (λ φ → bind (f >>> φ)) (isNatural _) ⟩
            bind (f >>> identity)
              ≡⟨ cong bind ℂ.leftIdentity ⟩
            bind f ∎

      toKleisliRawEq : toKleisliRaw (toMonoidalRaw m) ≡ Kleisli.Monad.raw m
      Kleisli.RawMonad.omap  (toKleisliRawEq i) = (begin
          Kleisli.RawMonad.omap (toKleisliRaw (toMonoidalRaw m)) ≡⟨⟩
          Monoidal.RawMonad.Romap (toMonoidalRaw m) ≡⟨⟩
          omap ∎
        ) i
      Kleisli.RawMonad.pure  (toKleisliRawEq i) = (begin
          Kleisli.RawMonad.pure  (toKleisliRaw (toMonoidalRaw m)) ≡⟨⟩
          Monoidal.RawMonad.pure (toMonoidalRaw m)               ≡⟨⟩
          pure ∎
        ) i
      Kleisli.RawMonad.bind  (toKleisliRawEq i) = bindEq i

    toKleislieq : (m : Kleisli.Monad) → toKleisli (toMonoidal m) ≡ m
    toKleislieq m = Kleisli.Monad≡ (toKleisliRawEq m)

    module _ (m : Monoidal.Monad) where
      private
        open Monoidal.Monad m
        -- module KM = Kleisli.Monad (toKleisli m)
        open Kleisli.Monad (toKleisli m) renaming
          ( bind to bind* ; omap to omap* ; join to join*
          ; fmap to fmap* ; pure to pure* ; R to R*)
          using ()
        module R = Functor R
        omapEq : omap* ≡ Romap
        omapEq = refl

        bindEq : ∀ {X Y} {f : Arrow X (Romap Y)} → bind* f ≡ bind f
        bindEq {X} {Y} {f} = begin
          bind* f         ≡⟨⟩
          join <<< fmap f ≡⟨⟩
          bind f          ∎

        joinEq : ∀ {X} → join* ≡ joinT X
        joinEq {X} = begin
          join*                  ≡⟨⟩
          bind* identity         ≡⟨⟩
          bind identity          ≡⟨⟩
          join <<< fmap identity ≡⟨ cong (λ φ → _ <<< φ) R.isIdentity ⟩
          join <<< identity      ≡⟨ ℂ.rightIdentity ⟩
          join                   ∎

        fmapEq : ∀ {A B} → fmap* {A} {B} ≡ fmap
        fmapEq {A} {B} = funExt (λ f → begin
          fmap* f                          ≡⟨⟩
          bind* (f >>> pure*)              ≡⟨⟩
          bind (f >>> pure)                ≡⟨⟩
          fmap (f >>> pure) >>> join       ≡⟨⟩
          fmap (f >>> pure) >>> join       ≡⟨ cong (λ φ → φ >>> joinT B) R.isDistributive ⟩
          fmap f >>> fmap pure >>> join    ≡⟨ ℂ.isAssociative ⟩
          join <<< fmap pure <<< fmap f    ≡⟨ cong (λ φ → φ <<< fmap f) (snd isInverse) ⟩
          identity <<< fmap f              ≡⟨ ℂ.leftIdentity ⟩
          fmap f                           ∎
          )

        rawEq : Functor.raw R* ≡ Functor.raw R
        RawFunctor.omap (rawEq i) = omapEq i
        RawFunctor.fmap (rawEq i) = fmapEq i

      Req : Monoidal.RawMonad.R (toMonoidalRaw (toKleisli m)) ≡ R
      Req = Functor≡ rawEq

      pureTEq : Monoidal.RawMonad.pureT (toMonoidalRaw (toKleisli m)) ≡ pureT
      pureTEq = refl

      pureNTEq : (λ i → NaturalTransformation Functors.identity (Req i))
        [ Monoidal.RawMonad.pureNT (toMonoidalRaw (toKleisli m)) ≡ pureNT ]
      pureNTEq = lemSigP (λ i → propIsNatural Functors.identity (Req i)) _ _ pureTEq

      joinTEq : Monoidal.RawMonad.joinT (toMonoidalRaw (toKleisli m)) ≡ joinT
      joinTEq = funExt (λ X → begin
        Monoidal.RawMonad.joinT (toMonoidalRaw (toKleisli m)) X ≡⟨⟩
        join* ≡⟨⟩
        join <<< fmap identity ≡⟨ cong (λ φ → join <<< φ) R.isIdentity ⟩
        join <<< identity ≡⟨ ℂ.rightIdentity ⟩
        join ∎)

      joinNTEq : (λ i → NaturalTransformation F[ Req i ∘ Req i ] (Req i))
        [ Monoidal.RawMonad.joinNT (toMonoidalRaw (toKleisli m)) ≡ joinNT ]
      joinNTEq = lemSigP (λ i → propIsNatural F[ Req i ∘ Req i ] (Req i)) _ _ joinTEq

      toMonoidalRawEq : toMonoidalRaw (toKleisli m) ≡ Monoidal.Monad.raw m
      Monoidal.RawMonad.R      (toMonoidalRawEq i) = Req i
      Monoidal.RawMonad.pureNT (toMonoidalRawEq i) = pureNTEq i
      Monoidal.RawMonad.joinNT (toMonoidalRawEq i) = joinNTEq i

    toMonoidaleq : (m : Monoidal.Monad) → toMonoidal (toKleisli m) ≡ m
    toMonoidaleq m = Monoidal.Monad≡ (toMonoidalRawEq m)

  open import Cat.Equivalence

  Monoidal≊Kleisli : Monoidal.Monad ≅ Kleisli.Monad
  Monoidal≊Kleisli = toKleisli , toMonoidal , funExt toMonoidaleq , funExt toKleislieq

  Monoidal≡Kleisli : Monoidal.Monad ≡ Kleisli.Monad
  Monoidal≡Kleisli = isoToPath Monoidal≊Kleisli

  grpdKleisli : isGrpd Kleisli.Monad
  grpdKleisli = Kleisli.grpdMonad

  grpdMonoidal : isGrpd Monoidal.Monad
  grpdMonoidal = subst isGrpd
    (sym Monoidal≡Kleisli) grpdKleisli
