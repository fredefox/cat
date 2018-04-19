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

{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Cat.Category.Monad where

open import Cat.Prelude
open import Cat.Category
open import Cat.Category.Functor as F
import Cat.Category.NaturalTransformation
import Cat.Category.Monad.Monoidal
import Cat.Category.Monad.Kleisli
open import Cat.Categories.Fun

module Monoidal = Cat.Category.Monad.Monoidal
module Kleisli  = Cat.Category.Monad.Kleisli

-- | The monoidal- and kleisli presentation of monads are equivalent.
module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Cat.Category.NaturalTransformation ℂ ℂ using (NaturalTransformation ; propIsNatural)
  private
    module ℂ = Category ℂ
    open ℂ using (Object ; Arrow ; identity ; _<<<_ ; _>>>_)
    module M = Monoidal ℂ
    module K = Kleisli  ℂ

    module _ (m : M.RawMonad) where
      open M.RawMonad m

      forthRaw : K.RawMonad
      K.RawMonad.omap forthRaw = Romap
      K.RawMonad.pure forthRaw = pureT _
      K.RawMonad.bind forthRaw = bind

    module _ {raw : M.RawMonad} (m : M.IsMonad raw) where
      private
        module MI = M.IsMonad m
      forthIsMonad : K.IsMonad (forthRaw raw)
      K.IsMonad.isIdentity     forthIsMonad = snd MI.isInverse
      K.IsMonad.isNatural      forthIsMonad = MI.isNatural
      K.IsMonad.isDistributive forthIsMonad = MI.isDistributive

    forth : M.Monad → K.Monad
    Kleisli.Monad.raw     (forth m) = forthRaw     (M.Monad.raw     m)
    Kleisli.Monad.isMonad (forth m) = forthIsMonad (M.Monad.isMonad m)

    module _ (m : K.Monad) where
      open K.Monad m

      backRaw : M.RawMonad
      M.RawMonad.R      backRaw = R
      M.RawMonad.pureNT backRaw = pureNT
      M.RawMonad.joinNT backRaw = joinNT

      private
        open M.RawMonad backRaw
        module R = Functor (M.RawMonad.R backRaw)

      backIsMonad : M.IsMonad backRaw
      M.IsMonad.isAssociative backIsMonad {X} = begin
        joinT X <<< R.fmap (joinT X)    ≡⟨⟩
        join <<< fmap (joinT X)         ≡⟨⟩
        join <<< fmap join              ≡⟨ isNaturalForeign ⟩
        join <<< join                   ≡⟨⟩
        joinT X  <<< joinT (R.omap X)   ∎
      M.IsMonad.isInverse backIsMonad {X} = inv-l , inv-r
        where
        inv-l = begin
          joinT X <<< pureT (R.omap X) ≡⟨⟩
          join <<< pure                ≡⟨ fst isInverse ⟩
          identity                     ∎
        inv-r = begin
          joinT X <<< R.fmap (pureT X) ≡⟨⟩
          join <<< fmap pure           ≡⟨ snd isInverse ⟩
          identity                     ∎

    back : K.Monad → M.Monad
    Monoidal.Monad.raw     (back m) = backRaw     m
    Monoidal.Monad.isMonad (back m) = backIsMonad m

    module _ (m : K.Monad) where
      private
        open K.Monad m
        bindEq : ∀ {X Y}
          → K.RawMonad.bind (forthRaw (backRaw m)) {X} {Y}
          ≡ K.RawMonad.bind (K.Monad.raw m)
        bindEq {X} {Y} = begin
          K.RawMonad.bind (forthRaw (backRaw m))        ≡⟨⟩
          (λ f → join <<< fmap f)                       ≡⟨⟩
          (λ f → bind (f >>> pure) >>> bind identity)   ≡⟨ funExt lem ⟩
          (λ f → bind f)                                ≡⟨⟩
          bind                                          ∎
          where
          lem : (f : Arrow X (omap Y))
            → bind (f >>> pure) >>> bind identity
            ≡ bind f
          lem f = begin
            bind (f >>> pure) >>> bind identity
              ≡⟨ isDistributive _ _ ⟩
            bind ((f >>> pure) >>> bind identity)
              ≡⟨ cong bind ℂ.isAssociative ⟩
            bind (f >>> (pure >>> bind identity))
              ≡⟨ cong (λ φ → bind (f >>> φ)) (isNatural _) ⟩
            bind (f >>> identity)
              ≡⟨ cong bind ℂ.leftIdentity ⟩
            bind f ∎

      forthRawEq : forthRaw (backRaw m) ≡ K.Monad.raw m
      K.RawMonad.omap  (forthRawEq _) = omap
      K.RawMonad.pure  (forthRawEq _) = pure
      K.RawMonad.bind  (forthRawEq i) = bindEq i

    fortheq : (m : K.Monad) → forth (back m) ≡ m
    fortheq m = K.Monad≡ (forthRawEq m)

    module _ (m : M.Monad) where
      private
        open M.Monad m
        module KM = K.Monad (forth m)
        module R = Functor R
        omapEq : KM.omap ≡ Romap
        omapEq = refl

        bindEq : ∀ {X Y} {f : Arrow X (Romap Y)} → KM.bind f ≡ bind f
        bindEq {X} {Y} {f} = begin
          KM.bind f           ≡⟨⟩
          joinT Y <<< Rfmap f ≡⟨⟩
          bind f              ∎

        joinEq : ∀ {X} → KM.join ≡ joinT X
        joinEq {X} = begin
          KM.join                    ≡⟨⟩
          KM.bind identity           ≡⟨⟩
          bind identity              ≡⟨⟩
          joinT X <<< Rfmap identity ≡⟨ cong (λ φ → _ <<< φ) R.isIdentity ⟩
          joinT X <<< identity       ≡⟨ ℂ.rightIdentity ⟩
          joinT X                    ∎

        fmapEq : ∀ {A B} → KM.fmap {A} {B} ≡ Rfmap
        fmapEq {A} {B} = funExt (λ f → begin
          KM.fmap f                                ≡⟨⟩
          KM.bind (f >>> KM.pure)                  ≡⟨⟩
             bind (f >>> pureT _)                  ≡⟨⟩
             Rfmap (f >>> pureT B) >>> joinT B     ≡⟨⟩
          Rfmap (f >>> pureT B) >>> joinT B        ≡⟨ cong (λ φ → φ >>> joinT B) R.isDistributive ⟩
          Rfmap f >>> Rfmap (pureT B) >>> joinT B  ≡⟨ ℂ.isAssociative ⟩
          joinT B <<< Rfmap (pureT B) <<< Rfmap f  ≡⟨ cong (λ φ → φ <<< Rfmap f) (snd isInverse) ⟩
          identity <<< Rfmap f                     ≡⟨ ℂ.leftIdentity ⟩
          Rfmap f                                  ∎
          )

        rawEq : Functor.raw KM.R ≡ Functor.raw R
        RawFunctor.omap (rawEq i) = omapEq i
        RawFunctor.fmap (rawEq i) = fmapEq i

      Req : M.RawMonad.R (backRaw (forth m)) ≡ R
      Req = Functor≡ rawEq

      pureTEq : M.RawMonad.pureT (backRaw (forth m)) ≡ pureT
      pureTEq = funExt (λ X → refl)

      pureNTEq : (λ i → NaturalTransformation Functors.identity (Req i))
        [ M.RawMonad.pureNT (backRaw (forth m)) ≡ pureNT ]
      pureNTEq = lemSigP (λ i → propIsNatural Functors.identity (Req i)) _ _ pureTEq

      joinTEq : M.RawMonad.joinT (backRaw (forth m)) ≡ joinT
      joinTEq = funExt (λ X → begin
        M.RawMonad.joinT (backRaw (forth m)) X ≡⟨⟩
        KM.join ≡⟨⟩
        joinT X <<< Rfmap identity ≡⟨ cong (λ φ → joinT X <<< φ) R.isIdentity ⟩
        joinT X <<< identity ≡⟨ ℂ.rightIdentity ⟩
        joinT X ∎)

      joinNTEq : (λ i → NaturalTransformation F[ Req i ∘ Req i ] (Req i))
        [ M.RawMonad.joinNT (backRaw (forth m)) ≡ joinNT ]
      joinNTEq = lemSigP (λ i → propIsNatural F[ Req i ∘ Req i ] (Req i)) _ _ joinTEq

      backRawEq : backRaw (forth m) ≡ M.Monad.raw m
      M.RawMonad.R      (backRawEq i) = Req i
      M.RawMonad.pureNT (backRawEq i) = pureNTEq i
      M.RawMonad.joinNT (backRawEq i) = joinNTEq i

    backeq : (m : M.Monad) → back (forth m) ≡ m
    backeq m = M.Monad≡ (backRawEq m)

    eqv : isEquiv M.Monad K.Monad forth
    eqv = gradLemma forth back fortheq backeq

  open import Cat.Equivalence

  Monoidal≊Kleisli : M.Monad ≅ K.Monad
  Monoidal≊Kleisli = forth , back , funExt backeq , funExt fortheq

  Monoidal≡Kleisli : M.Monad ≡ K.Monad
  Monoidal≡Kleisli = isoToPath Monoidal≊Kleisli
