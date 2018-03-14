{-
This module provides construction 2.3 in [voe]
-}
{-# OPTIONS --cubical --allow-unsolved-metas --caching #-}
module Cat.Category.Monad.Voevodsky where

open import Agda.Primitive

open import Data.Product
open import Function using (_∘_ ; _$_)

open import Cubical
open import Cubical.NType.Properties using (lemPropF ; lemSig ;  lemSigP)
open import Cubical.GradLemma        using (gradLemma)

open import Cat.Category
open import Cat.Category.Functor as F
open import Cat.Category.NaturalTransformation
open import Cat.Category.Monad
open import Cat.Categories.Fun

-- Utilities
module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  module Equivalence (e : A ≃ B) where
    obverse : A → B
    obverse = proj₁ e

    reverse : B → A
    reverse = inverse e

    -- TODO Implement and push upstream.
    postulate
      verso-recto : reverse ∘ obverse ≡ Function.id
      recto-verso : obverse ∘ reverse ≡ Function.id

module voe {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    ℓ = ℓa ⊔ ℓb
    module ℂ = Category ℂ
    open ℂ using (Object ; Arrow)
    open NaturalTransformation ℂ ℂ
    module M = Monoidal ℂ
    module K = Kleisli  ℂ

  module §2-3 (omap : Omap ℂ ℂ) (pure : {X : Object} → Arrow X (omap X)) where
    record §1 : Set ℓ where
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
        pureN : Natural F.identity R pureT

      pureNT : NaturalTransformation F.identity R
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
        isMnd : IsMonad rawMnd

      toMonad : Monad
      toMonad = record
        { raw     = rawMnd
        ; isMonad = isMnd
        }

    record §2 : Set ℓ where
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
        isMnd : IsMonad rawMnd

      toMonad : Monad
      toMonad = record
        { raw     = rawMnd
        ; isMonad = isMnd
        }

  §1-fromMonad : (m : M.Monad) → §2-3.§1 (M.Monad.Romap m) (λ {X} → M.Monad.pureT m X)
  -- voe-2-3-1-fromMonad : (m : M.Monad) → voe.§2-3.§1 (M.Monad.Romap m) (λ {X} → M.Monad.pureT m X)
  §1-fromMonad m = record
    { fmap = Functor.fmap R
    ; RisFunctor = Functor.isFunctor R
    ; pureN = pureN
    ; join = λ {X} → joinT X
    ; joinN = joinN
    ; isMnd = M.Monad.isMonad m
    }
    where
    raw = M.Monad.raw m
    R   = M.RawMonad.R raw
    pureT = M.RawMonad.pureT raw
    pureN = M.RawMonad.pureN raw
    joinT = M.RawMonad.joinT raw
    joinN = M.RawMonad.joinN raw

  §2-fromMonad : (m : K.Monad) → §2-3.§2 (K.Monad.omap m) (K.Monad.pure m)
  §2-fromMonad m = record
    { bind  = K.Monad.bind    m
    ; isMnd = K.Monad.isMonad m
    }

  -- | In the following we seek to transform the equivalence `Monoidal≃Kleisli`
  -- | to talk about voevodsky's construction.
  module _ (omap : Omap ℂ ℂ) (pure : {X : Object} → Arrow X (omap X)) where
    private
      -- Could just open this module and rename stuff accordingly, but as
      -- documentation I will put in the type-annotations here.
      module E = Equivalence (Monoidal≃Kleisli ℂ)

      Monoidal→Kleisli : M.Monad → K.Monad
      Monoidal→Kleisli = E.obverse

      Kleisli→Monoidal : K.Monad → M.Monad
      Kleisli→Monoidal = E.reverse

      ve-re : Kleisli→Monoidal ∘ Monoidal→Kleisli ≡ Function.id
      ve-re = E.verso-recto

      re-ve : Monoidal→Kleisli ∘ Kleisli→Monoidal ≡ Function.id
      re-ve = E.recto-verso

      forth : §2-3.§1 omap pure → §2-3.§2 omap pure
      forth = §2-fromMonad ∘ Monoidal→Kleisli ∘ §2-3.§1.toMonad

      back : §2-3.§2 omap pure → §2-3.§1 omap pure
      back = §1-fromMonad ∘ Kleisli→Monoidal ∘ §2-3.§2.toMonad

      forthEq : ∀ m → (forth ∘ back) m ≡ m
      forthEq m = begin
        (forth ∘ back) m ≡⟨⟩
        -- In full gory detail:
        ( §2-fromMonad
        ∘ Monoidal→Kleisli
        ∘ §2-3.§1.toMonad
        ∘ §1-fromMonad
        ∘ Kleisli→Monoidal
        ∘ §2-3.§2.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        ( §2-fromMonad
        ∘ Monoidal→Kleisli
        ∘ Kleisli→Monoidal
        ∘ §2-3.§2.toMonad
        ) m ≡⟨ cong (λ φ → φ m) t ⟩
        -- Monoidal→Kleisli and Kleisli→Monoidal are inverses
        -- I should be able to prove this using congruence and `lem` below.
        ( §2-fromMonad
        ∘ §2-3.§2.toMonad
        ) m ≡⟨⟩
        (  §2-fromMonad
        ∘ §2-3.§2.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        m ∎
        where
        t' : ((Monoidal→Kleisli ∘ Kleisli→Monoidal) ∘ §2-3.§2.toMonad {omap} {pure})
          ≡ §2-3.§2.toMonad
        t' = cong (\ φ → φ ∘ §2-3.§2.toMonad) {!re-ve!}
        cong-d : ∀ {ℓ} {A : Set ℓ} {ℓ'} {B : A → Set ℓ'} {x y : A}
          → (f : (x : A) → B x) → (eq : x ≡ y) → PathP (\ i → B (eq i)) (f x) (f y)
        cong-d f p = λ i → f (p i)
        t : (§2-fromMonad ∘ (Monoidal→Kleisli ∘ Kleisli→Monoidal) ∘ §2-3.§2.toMonad {omap} {pure})
          ≡ (§2-fromMonad ∘ §2-3.§2.toMonad)
        t = cong-d (\ f → §2-fromMonad ∘ f) t'
        u : (§2-fromMonad ∘ (Monoidal→Kleisli ∘ Kleisli→Monoidal) ∘ §2-3.§2.toMonad) m
          ≡ (§2-fromMonad ∘ §2-3.§2.toMonad) m
        u = cong (\ f → f m) t
{-
(K.RawMonad.omap (K.Monad.raw (?0 ℂ omap pure m i (§2-3.§2.toMonad m))) x)
  = (omap x) : Object
(K.RawMonad.pure (K.Monad.raw (?0 ℂ omap pure m x (§2-3.§2.toMonad x))))
  = pure     : Arrow X (_350 ℂ omap pure m x x X)
-}

      backEq : ∀ m → (back ∘ forth) m ≡ m
      backEq m = begin
        (back ∘ forth) m ≡⟨⟩
        ( §1-fromMonad
        ∘ Kleisli→Monoidal
        ∘ §2-3.§2.toMonad
        ∘ §2-fromMonad
        ∘ Monoidal→Kleisli
        ∘ §2-3.§1.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        ( §1-fromMonad
        ∘ Kleisli→Monoidal
        ∘ Monoidal→Kleisli
        ∘ §2-3.§1.toMonad
        ) m ≡⟨ cong (λ φ → φ m) t ⟩ -- Monoidal→Kleisli and Kleisli→Monoidal are inverses
        ( §1-fromMonad
        ∘ §2-3.§1.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        m ∎
        where
        t : §1-fromMonad ∘ Kleisli→Monoidal ∘ Monoidal→Kleisli ∘ §2-3.§1.toMonad
          ≡ §1-fromMonad ∘ §2-3.§1.toMonad
        -- Why does `re-ve` not satisfy this goal?
        t = cong (λ φ → §1-fromMonad ∘ φ ∘ §2-3.§1.toMonad) ({!ve-re!})

      voe-isEquiv : isEquiv (§2-3.§1 omap pure) (§2-3.§2 omap pure) forth
      voe-isEquiv = gradLemma forth back forthEq backEq

    equiv-2-3 : §2-3.§1 omap pure ≃ §2-3.§2 omap pure
    equiv-2-3 = forth , voe-isEquiv
