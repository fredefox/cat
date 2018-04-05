{-
This module provides construction 2.3 in [voe]
-}
{-# OPTIONS --cubical --allow-unsolved-metas --caching #-}
module Cat.Category.Monad.Voevodsky where

open import Cat.Prelude
open import Function

open import Cat.Category
open import Cat.Category.Functor as F
import Cat.Category.NaturalTransformation
open import Cat.Category.Monad
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
      toMonad = record
        { raw     = rawMnd
        ; isMonad = isMonad
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
        isMonad : IsMonad rawMnd

      toMonad : Monad
      toMonad = record
        { raw     = rawMnd
        ; isMonad = isMonad
        }

  §1-fromMonad : (m : M.Monad) → §2-3.§1 (M.Monad.Romap m) (λ {X} → M.Monad.pureT m X)
  §1-fromMonad m = record
    { fmap       = Functor.fmap R
    ; RisFunctor = Functor.isFunctor R
    ; pureN      = pureN
    ; join       = λ {X} → joinT X
    ; joinN      = joinN
    ; isMonad    = M.Monad.isMonad m
    }
    where
    open M.Monad m

  §2-fromMonad : (m : K.Monad) → §2-3.§2 (K.Monad.omap m) (K.Monad.pure m)
  §2-fromMonad m = record
    { bind    = K.Monad.bind    m
    ; isMonad = K.Monad.isMonad m
    }

  -- | In the following we seek to transform the equivalence `Monoidal≃Kleisli`
  -- | to talk about voevodsky's construction.
  module _ (omap : Omap ℂ ℂ) (pure : {X : Object} → Arrow X (omap X)) where
    private
      module E = AreInverses (Monoidal≅Kleisli ℂ .snd .snd)

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
        cong-d : ∀ {ℓ} {A : Set ℓ} {ℓ'} {B : A → Set ℓ'} {x y : A}
          → (f : (x : A) → B x) → (eq : x ≡ y) → PathP (\ i → B (eq i)) (f x) (f y)
        cong-d f p = λ i → f (p i)
        t' = cong (\ φ → φ ∘ §2-3.§2.toMonad) re-ve
        t : (§2-fromMonad ∘ (Monoidal→Kleisli ∘ Kleisli→Monoidal) ∘ §2-3.§2.toMonad {omap} {pure})
          ≡ (§2-fromMonad ∘ §2-3.§2.toMonad)
        t = cong-d (\ f → §2-fromMonad ∘ f) t'
        u : (§2-fromMonad ∘ (Monoidal→Kleisli ∘ Kleisli→Monoidal) ∘ §2-3.§2.toMonad) m
          ≡ (§2-fromMonad ∘ §2-3.§2.toMonad) m
        u = cong (\ φ → φ m) t

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
        t i m = §1-fromMonad (ve-re i (§2-3.§1.toMonad m))

      voe-isEquiv : isEquiv (§2-3.§1 omap pure) (§2-3.§2 omap pure) forth
      voe-isEquiv = gradLemma forth back forthEq backEq

    equiv-2-3 : §2-3.§1 omap pure ≃ §2-3.§2 omap pure
    equiv-2-3 = forth , voe-isEquiv
