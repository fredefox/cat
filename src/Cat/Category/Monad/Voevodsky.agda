{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Cat.Category.Monad.Voevodsky where

open import Agda.Primitive

open import Data.Product

open import Cubical
open import Cubical.NType.Properties using (lemPropF ; lemSig ;  lemSigP)
open import Cubical.GradLemma        using (gradLemma)

open import Cat.Category
open import Cat.Category.Functor as F
open import Cat.Category.NaturalTransformation
open import Cat.Category.Monad using (Monoidal≃Kleisli)
import Cat.Category.Monad.Monoidal as Monoidal
import Cat.Category.Monad.Kleisli  as Kleisli
open import Cat.Categories.Fun

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    ℓ = ℓa ⊔ ℓb
    module ℂ = Category ℂ
    open ℂ using (Object ; Arrow ; _∘_)
    open NaturalTransformation ℂ ℂ
    module M = Monoidal ℂ
    module K = Kleisli  ℂ

  module voe-2-3 (omap : Omap ℂ ℂ) (pure : {X : Object} → Arrow X (omap X)) where
    record voe-2-3-1 : Set ℓ where
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

    record voe-2-3-2 : Set ℓ where
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

module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} where
  private
    module M = Monoidal ℂ
    module K = Kleisli  ℂ
    open voe-2-3 ℂ

  voe-2-3-1-fromMonad : (m : M.Monad) → voe-2-3-1 (M.Monad.Romap m) (λ {X} → M.Monad.pureT m X)
  voe-2-3-1-fromMonad m = record
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

  voe-2-3-2-fromMonad : (m : K.Monad) → voe-2-3-2 (K.Monad.omap m) (K.Monad.pure m)
  voe-2-3-2-fromMonad m = record
    { bind  = K.Monad.bind    m
    ; isMnd = K.Monad.isMonad m
    }

module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} where
  private
    ℓ = ℓa ⊔ ℓb
    module ℂ = Category ℂ
    open ℂ using (Object ; Arrow)
    open NaturalTransformation ℂ ℂ
    module M = Monoidal ℂ
    module K = Kleisli  ℂ
    open import Function using (_∘_ ; _$_)

  module _ (omap : Omap ℂ ℂ) (pure : {X : Object} → Arrow X (omap X)) where
    open voe-2-3 ℂ
    private
      Monoidal→Kleisli : M.Monad → K.Monad
      Monoidal→Kleisli = proj₁ Monoidal≃Kleisli

      Kleisli→Monoidal : K.Monad → M.Monad
      Kleisli→Monoidal = inverse Monoidal≃Kleisli

      forth : voe-2-3-1 omap pure → voe-2-3-2 omap pure
      forth = voe-2-3-2-fromMonad ∘ Monoidal→Kleisli ∘ voe-2-3.voe-2-3-1.toMonad

      back : voe-2-3-2 omap pure → voe-2-3-1 omap pure
      back = voe-2-3-1-fromMonad ∘ Kleisli→Monoidal ∘ voe-2-3.voe-2-3-2.toMonad

      forthEq : ∀ m → _ ≡ _
      forthEq m = begin
        (forth ∘ back) m ≡⟨⟩
        -- In full gory detail:
        ( voe-2-3-2-fromMonad
        ∘ Monoidal→Kleisli
        ∘ voe-2-3.voe-2-3-1.toMonad
        ∘ voe-2-3-1-fromMonad
        ∘ Kleisli→Monoidal
        ∘ voe-2-3.voe-2-3-2.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        (  voe-2-3-2-fromMonad
        ∘ Monoidal→Kleisli
        ∘ Kleisli→Monoidal
        ∘ voe-2-3.voe-2-3-2.toMonad
        ) m ≡⟨ u ⟩
        -- Monoidal→Kleisli and Kleisli→Monoidal are inverses
        -- I should be able to prove this using congruence and `lem` below.
        ( voe-2-3-2-fromMonad
        ∘ voe-2-3.voe-2-3-2.toMonad
        ) m ≡⟨⟩
        (  voe-2-3-2-fromMonad
        ∘ voe-2-3.voe-2-3-2.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        m ∎
        where
        lem : Monoidal→Kleisli ∘ Kleisli→Monoidal ≡ Function.id
        lem = {!!} -- verso-recto Monoidal≃Kleisli
        t : {ℓ : Level} {A B : Set ℓ} {a : _ → A} {b : B → _}
          → a ∘ (Monoidal→Kleisli ∘ Kleisli→Monoidal) ∘ b ≡ a ∘ b
        t {a = a} {b} = cong (λ φ → a ∘ φ ∘ b) lem
        u : {ℓ : Level} {A B : Set ℓ} {a : _ → A} {b : B → _}
          → {m : _} → (a ∘ (Monoidal→Kleisli ∘ Kleisli→Monoidal) ∘ b) m ≡ (a ∘ b) m
        u {m = m} = cong (λ φ → φ m) t

      backEq : ∀ m → (back ∘ forth) m ≡ m
      backEq m = begin
        (back ∘ forth) m ≡⟨⟩
        ( voe-2-3-1-fromMonad
        ∘ Kleisli→Monoidal
        ∘ voe-2-3.voe-2-3-2.toMonad
        ∘ voe-2-3-2-fromMonad
        ∘ Monoidal→Kleisli
        ∘ voe-2-3.voe-2-3-1.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        ( voe-2-3-1-fromMonad
        ∘ Kleisli→Monoidal
        ∘ Monoidal→Kleisli
        ∘ voe-2-3.voe-2-3-1.toMonad
        ) m ≡⟨ cong (λ φ → φ m) t ⟩ -- Monoidal→Kleisli and Kleisli→Monoidal are inverses
        ( voe-2-3-1-fromMonad
        ∘ voe-2-3.voe-2-3-1.toMonad
        ) m ≡⟨⟩ -- fromMonad and toMonad are inverses
        m ∎
        where
        t = {!!} -- cong (λ φ → voe-2-3-1-fromMonad ∘ φ ∘ voe-2-3.voe-2-3-1.toMonad) (recto-verso Monoidal≃Kleisli)

      voe-isEquiv : isEquiv (voe-2-3-1 omap pure) (voe-2-3-2 omap pure) forth
      voe-isEquiv = gradLemma forth back forthEq backEq

    equiv-2-3 : voe-2-3-1 omap pure ≃ voe-2-3-2 omap pure
    equiv-2-3 = forth , voe-isEquiv
