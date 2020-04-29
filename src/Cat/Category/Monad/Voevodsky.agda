{-
This module provides construction 2.3 in [voe]
-}
{-# OPTIONS --cubical #-}
module Cat.Category.Monad.Voevodsky where

open import Cat.Prelude
open import Cat.Equivalence

open import Cat.Category
open import Cat.Category.Functor as F
import Cat.Category.NaturalTransformation
open import Cat.Category.Monad
import Cat.Category.Monad.Monoidal as Monoidal
import Cat.Category.Monad.Kleisli as Kleisli
open import Cat.Categories.Fun
open import Cat.Equivalence

module voe {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Cat.Category.NaturalTransformation ℂ ℂ
  private
    ℓ = ℓa ⊔ ℓb
    module ℂ = Category ℂ
    open ℂ using (Object ; Arrow)
    module M = Monoidal ℂ
    module K = Kleisli  ℂ

  module §2-3 (omap : Object → Object) (pure : {X : Object} → Arrow X (omap X)) where
    record §1 : Set ℓ where
      no-eta-equality
      open M

      field
        fmap : Fmap ℂ ℂ omap
        join : {A : Object} → ℂ [ omap (omap A) , omap A ]

      Rraw : RawFunctor ℂ ℂ
      Rraw = record
        { omap = omap
        ; fmap = fmap
        }

      field
        RisFunctor : IsFunctor ℂ ℂ Rraw

      R : EndoFunctor ℂ
      R = record
        { raw = Rraw
        ; isFunctor = RisFunctor
        }

      pureT : (X : Object) → Arrow X (omap X)
      pureT X = pure {X}

      field
        pureN : Natural Functors.identity R pureT

      pureNT : NaturalTransformation Functors.identity R
      pureNT = pureT , pureN

      joinT : (A : Object) → ℂ [ omap (omap A) , omap A ]
      joinT A = join {A}

      field
        joinN : Natural F[ R ∘ R ] R joinT

      joinNT : NaturalTransformation F[ R ∘ R ] R
      joinNT = joinT , joinN

      rawMnd : RawMonad
      rawMnd = record
        { R = R
        ; pureNT = pureNT
        ; joinNT = joinNT
        }

      field
        isMonad : IsMonad rawMnd

      toMonad : Monad
      toMonad .Monad.raw = rawMnd
      toMonad .Monad.isMonad = isMonad

    record §2 : Set ℓ where
      no-eta-equality
      open K

      field
        bind : {X Y : Object} → ℂ [ X , omap Y ] → ℂ [ omap X , omap Y ]

      rawMnd : RawMonad
      rawMnd = record
        { omap = omap
        ; pure = pure
        ; bind = bind
        }

      field
        isMonad : IsMonad rawMnd

      toMonad : Monad
      toMonad .Monad.raw     = rawMnd
      toMonad .Monad.isMonad = isMonad

  module _ (m : M.Monad) where
    open M.Monad m

    §1-fromMonad : §2-3.§1 (M.Monad.Romap m) (λ {X} → M.Monad.pureT m X)
    §1-fromMonad .§2-3.§1.fmap       = Functor.fmap R
    §1-fromMonad .§2-3.§1.RisFunctor = Functor.isFunctor R
    §1-fromMonad .§2-3.§1.pureN      = pureN
    §1-fromMonad .§2-3.§1.join      {X} = joinT X
    §1-fromMonad .§2-3.§1.joinN      = joinN
    §1-fromMonad .§2-3.§1.isMonad    = M.Monad.isMonad m


  §2-fromMonad : (m : K.Monad) → §2-3.§2 (K.Monad.omap m) (K.Monad.pure m)
  §2-fromMonad m .§2-3.§2.bind    = K.Monad.bind    m
  §2-fromMonad m  .§2-3.§2.isMonad = K.Monad.isMonad m

  -- | In the following we seek to transform the equivalence `Monoidal≃Kleisli`
  -- | to talk about voevodsky's construction.
  module _ (omap : Omap ℂ ℂ) (pure : {X : Object} → Arrow X (omap X)) where
    private
      module E = AreInverses {f = (fst (Monoidal≊Kleisli ℂ))} {fst (snd (Monoidal≊Kleisli ℂ))}(Monoidal≊Kleisli ℂ .snd .snd)

      Monoidal→Kleisli : M.Monad → K.Monad
      Monoidal→Kleisli = E.obverse

      Kleisli→Monoidal : K.Monad → M.Monad
      Kleisli→Monoidal = E.reverse

      ve-re : Kleisli→Monoidal ∘ Monoidal→Kleisli ≡ idFun _
      ve-re = E.verso-recto

      re-ve : Monoidal→Kleisli ∘ Kleisli→Monoidal ≡ idFun _
      re-ve = E.recto-verso

      forth : §2-3.§1 omap pure → §2-3.§2 omap pure
      forth = §2-fromMonad ∘ Monoidal→Kleisli ∘ §2-3.§1.toMonad

      back : §2-3.§2 omap pure → §2-3.§1 omap pure
      back = §1-fromMonad ∘ Kleisli→Monoidal ∘ §2-3.§2.toMonad

      forthEq : ∀ m → (forth ∘ back) m ≡ m
      forthEq m = begin
       §2-fromMonad
         (Monoidal→Kleisli
          (§2-3.§1.toMonad
           (§1-fromMonad (Kleisli→Monoidal (§2-3.§2.toMonad m)))))
         ≡⟨ cong (§2-fromMonad ∘ Monoidal→Kleisli) (lemmaz (Kleisli→Monoidal (§2-3.§2.toMonad m))) ⟩
       §2-fromMonad
         ((Monoidal→Kleisli ∘ Kleisli→Monoidal)
          (§2-3.§2.toMonad m))
         -- Below is the fully normalized goal and context with
         -- `funExt` made abstract.
         --
         -- Goal: PathP (λ _ → §2-3.§2 omap (λ {z} → pure))
         --       (§2-fromMonad
         --        (.Cat.Category.Monad.toKleisli ℂ
         --         (.Cat.Category.Monad.toMonoidal ℂ (§2-3.§2.toMonad m))))
         --       (§2-fromMonad (§2-3.§2.toMonad m))
         -- Have: PathP
         --       (λ i →
         --          §2-3.§2 K.IsMonad.omap
         --          (K.RawMonad.pure
         --           (K.Monad.raw
         --            (funExt (λ m₁ → K.Monad≡ (.Cat.Category.Monad.toKleisliRawEq ℂ m₁))
         --             i (§2-3.§2.toMonad m)))))
         --       (§2-fromMonad
         --        (.Cat.Category.Monad.toKleisli ℂ
         --         (.Cat.Category.Monad.toMonoidal ℂ (§2-3.§2.toMonad m))))
         --       (§2-fromMonad (§2-3.§2.toMonad m))
         ≡⟨ ( cong {x = Monoidal→Kleisli ∘ Kleisli→Monoidal} {y = idFun K.Monad} (\ φ → §2-fromMonad (φ (§2-3.§2.toMonad m))) re-ve) ⟩
       (§2-fromMonad ∘ §2-3.§2.toMonad) m
         ≡⟨ lemma ⟩
       m ∎
        where
        lemma : (§2-fromMonad ∘ §2-3.§2.toMonad) m ≡ m
        §2-3.§2.bind (lemma i) = §2-3.§2.bind m
        §2-3.§2.isMonad (lemma i) = §2-3.§2.isMonad m
        lemmaz : ∀ m → §2-3.§1.toMonad (§1-fromMonad m) ≡ m
        M.Monad.raw (lemmaz m i) = M.Monad.raw m
        M.Monad.isMonad (lemmaz m i) = M.Monad.isMonad m

      backEq : ∀ m → (back ∘ forth) m ≡ m
      backEq m = begin
        §1-fromMonad
        (Kleisli→Monoidal
        (§2-3.§2.toMonad
        (§2-fromMonad (Monoidal→Kleisli (§2-3.§1.toMonad m)))))
          ≡⟨ cong (§1-fromMonad ∘ Kleisli→Monoidal) (lemma (Monoidal→Kleisli (§2-3.§1.toMonad m))) ⟩
        §1-fromMonad
        ((Kleisli→Monoidal ∘ Monoidal→Kleisli)
        (§2-3.§1.toMonad m))
          -- Below is the fully normalized `agda2-goal-and-context`
          -- with `funExt` made abstract.
          --
          -- Goal: PathP (λ _ → §2-3.§1 omap (λ {X} → pure))
          --       (§1-fromMonad
          --        (.Cat.Category.Monad.toMonoidal ℂ
          --         (.Cat.Category.Monad.toKleisli ℂ (§2-3.§1.toMonad m))))
          --       (§1-fromMonad (§2-3.§1.toMonad m))
          -- Have: PathP
          --       (λ i →
          --          §2-3.§1
          --          (RawFunctor.omap
          --           (Functor.raw
          --            (M.RawMonad.R
          --             (M.Monad.raw
          --              (funExt
          --               (λ m₁ → M.Monad≡ (.Cat.Category.Monad.toMonoidalRawEq ℂ m₁)) i
          --               (§2-3.§1.toMonad m))))))
          --          (λ {X} →
          --             fst
          --             (M.RawMonad.pureNT
          --              (M.Monad.raw
          --               (funExt
          --                (λ m₁ → M.Monad≡ (.Cat.Category.Monad.toMonoidalRawEq ℂ m₁)) i
          --                (§2-3.§1.toMonad m))))
          --             X))
          --       (§1-fromMonad
          --        (.Cat.Category.Monad.toMonoidal ℂ
          --         (.Cat.Category.Monad.toKleisli ℂ (§2-3.§1.toMonad m))))
          --       (§1-fromMonad (§2-3.§1.toMonad m))
          ≡⟨ (cong (\ φ → §1-fromMonad (φ (§2-3.§1.toMonad m))) ve-re) ⟩
        §1-fromMonad (§2-3.§1.toMonad m)
          ≡⟨ lemmaz ⟩
        m ∎
       where
        lemmaz : §1-fromMonad (§2-3.§1.toMonad m) ≡ m
        §2-3.§1.fmap (lemmaz i) = §2-3.§1.fmap m
        §2-3.§1.join (lemmaz i) = §2-3.§1.join m
        §2-3.§1.RisFunctor (lemmaz i) = §2-3.§1.RisFunctor m
        §2-3.§1.pureN (lemmaz i) = §2-3.§1.pureN m
        §2-3.§1.joinN (lemmaz i) = §2-3.§1.joinN m
        §2-3.§1.isMonad (lemmaz i) = §2-3.§1.isMonad m
        lemma : ∀ m → §2-3.§2.toMonad (§2-fromMonad m) ≡ m
        K.Monad.raw (lemma m i) = K.Monad.raw m
        K.Monad.isMonad (lemma m i) = K.Monad.isMonad m

    equiv-2-3 : §2-3.§1 omap pure ≃ §2-3.§2 omap pure
    equiv-2-3 = fromIsomorphism _ _
      ( forth , back
      , funExt backEq , funExt forthEq
      )
