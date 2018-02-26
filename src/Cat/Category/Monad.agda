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

  open Category ℂ using (Object ; Arrow ; 𝟙 ; _∘_)
  open NaturalTransformation ℂ ℂ
  record RawMonad : Set ℓ where
    field
      -- R ~ m
      R : Functor ℂ ℂ
      -- η ~ pure
      ηNatTrans : NaturalTransformation F.identity R
      -- μ ~ join
      μNatTrans : NaturalTransformation F[ R ∘ R ] R

    η : Transformation F.identity R
    η = proj₁ ηNatTrans
    μ : Transformation F[ R ∘ R ] R
    μ = proj₁ μNatTrans

    private
      module R  = Functor R
    IsAssociative : Set _
    IsAssociative = {X : Object}
      → μ X ∘ R.func→ (μ X) ≡ μ X ∘ μ (R.func* X)
    IsInverse : Set _
    IsInverse = {X : Object}
      → μ X ∘ η (R.func* X) ≡ 𝟙
      × μ X ∘ R.func→ (η X) ≡ 𝟙

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

  postulate propIsMonad : ∀ {raw} → isProp (IsMonad raw)
  Monad≡ : {m n : Monad} → Monad.raw m ≡ Monad.raw n → m ≡ n
  Monad.raw     (Monad≡ eq i) = eq i
  Monad.isMonad (Monad≡ {m} {n} eq i) = res i
    where
      -- TODO: PathJ nightmare + `propIsMonad`.
      res : (λ i → IsMonad (eq i)) [ Monad.isMonad m ≡ Monad.isMonad n ]
      res = {!!}

-- "A monad in the Kleisli form" [voe]
module Kleisli {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    ℓ = ℓa ⊔ ℓb

  open Category ℂ using (Arrow ; 𝟙 ; Object ; _∘_ ; _>>>_)

  -- | Data for a monad.
  --
  -- Note that (>>=) is not expressible in a general category because objects
  -- are not generally types.
  record RawMonad : Set ℓ where
    field
      RR : Object → Object
      -- Note name-change from [voe]
      pure : {X : Object} → ℂ [ X , RR X ]
      bind : {X Y : Object} → ℂ [ X , RR Y ] → ℂ [ RR X , RR Y ]

    -- | functor map
    --
    -- This should perhaps be defined in a "Klesli-version" of functors as well?
    fmap : ∀ {A B} → ℂ [ A , B ] → ℂ [ RR A , RR B ]
    fmap f = bind (pure ∘ f)

    -- | Composition of monads aka. the kleisli-arrow.
    _>=>_ : {A B C : Object} → ℂ [ A , RR B ] → ℂ [ B , RR C ] → ℂ [ A , RR C ]
    f >=> g = f >>> (bind g)

    -- | Flattening nested monads.
    join : {A : Object} → ℂ [ RR (RR A) , RR A ]
    join = bind 𝟙

    ------------------
    -- * Monad laws --
    ------------------

    -- There may be better names than what I've chosen here.

    IsIdentity     = {X : Object}
      → bind pure ≡ 𝟙 {RR X}
    IsNatural      = {X Y : Object}   (f : ℂ [ X , RR Y ])
      → pure >>> (bind f) ≡ f
    IsDistributive = {X Y Z : Object} (g : ℂ [ Y , RR Z ]) (f : ℂ [ X , RR Y ])
      → (bind f) >>> (bind g) ≡ bind (f >=> g)

    -- | Functor map fusion.
    --
    -- This is really a functor law. Should we have a kleisli-representation of
    -- functors as well and make them a super-class?
    Fusion = {X Y Z : Object} {g : ℂ [ Y , Z ]} {f : ℂ [ X , Y ]}
      → fmap (g ∘ f) ≡ fmap g ∘ fmap f

  record IsMonad (raw : RawMonad) : Set ℓ where
    open RawMonad raw public
    field
      isIdentity     : IsIdentity
      isNatural      : IsNatural
      isDistributive : IsDistributive

    -- | Map fusion is admissable.
    fusion : Fusion
    fusion {g = g} {f} = begin
      fmap (g ∘ f)               ≡⟨⟩
      bind ((f >>> g) >>> pure)  ≡⟨ cong bind isAssociative ⟩
      bind (f >>> (g >>> pure))  ≡⟨ cong (λ φ → bind (f >>> φ)) (sym (isNatural _)) ⟩
      bind (f >>> (pure >>> (bind (g >>> pure)))) ≡⟨⟩
      bind (f >>> (pure >>> fmap g)) ≡⟨⟩
      bind ((fmap g ∘ pure) ∘ f) ≡⟨ cong bind (sym isAssociative) ⟩
      bind (fmap g ∘ (pure ∘ f)) ≡⟨ sym lem ⟩
      bind (pure ∘ g) ∘ bind (pure ∘ f)   ≡⟨⟩
      fmap g ∘ fmap f           ∎
      where
        open Category ℂ using (isAssociative)
        lem : fmap g ∘ fmap f ≡ bind (fmap g ∘ (pure ∘ f))
        lem = isDistributive (pure ∘ g) (pure ∘ f)

  record Monad : Set ℓ where
    field
      raw : RawMonad
      isMonad : IsMonad raw
    open IsMonad isMonad public

  postulate propIsMonad : ∀ {raw} → isProp (IsMonad raw)
  Monad≡ : {m n : Monad} → Monad.raw m ≡ Monad.raw n → m ≡ n
  Monad.raw     (Monad≡ eq i) = eq i
  Monad.isMonad (Monad≡ {m} {n} eq i) = res i
    where
      -- TODO: PathJ nightmare + `propIsMonad`.
      res : (λ i → IsMonad (eq i)) [ Monad.isMonad m ≡ Monad.isMonad n ]
      res = {!!}

-- | The monoidal- and kleisli presentation of monads are equivalent.
--
-- This is problem 2.3 in [voe].
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

        pure : {X : Object} → ℂ [ X , RR X ]
        pure {X} = η X

        bind : {X Y : Object} → ℂ [ X , RR Y ] → ℂ [ RR X , RR Y ]
        bind {X} {Y} f = μ Y ∘ func→ R f

      forthRaw : K.RawMonad
      Kraw.RR   forthRaw = RR
      Kraw.pure forthRaw = pure
      Kraw.bind forthRaw = bind

    module _ {raw : M.RawMonad} (m : M.IsMonad raw) where
      private
        open M.IsMonad m
        open K.RawMonad (forthRaw raw)
        module R = Functor R

        isIdentity : IsIdentity
        isIdentity {X} = begin
          bind pure                    ≡⟨⟩
          bind (η X)                ≡⟨⟩
          μ X ∘ func→ R (η X)       ≡⟨ proj₂ isInverse ⟩
          𝟙 ∎

        isNatural : IsNatural
        isNatural {X} {Y} f = begin
          bind f ∘ pure             ≡⟨⟩
          bind f ∘ η X              ≡⟨⟩
          μ Y ∘ R.func→ f ∘ η X     ≡⟨ sym ℂ.isAssociative ⟩
          μ Y ∘ (R.func→ f ∘ η X)   ≡⟨ cong (λ φ → μ Y ∘ φ) (sym (ηN f)) ⟩
          μ Y ∘ (η (R.func* Y) ∘ f) ≡⟨ ℂ.isAssociative ⟩
          μ Y ∘ η (R.func* Y) ∘ f   ≡⟨ cong (λ φ → φ ∘ f) (proj₁ isInverse) ⟩
          𝟙 ∘ f                     ≡⟨ proj₂ ℂ.isIdentity ⟩
          f ∎
          where
            open NaturalTransformation
            module ℂ = Category ℂ
            ηN : Natural ℂ ℂ F.identity R η
            ηN = proj₂ ηNatTrans

        isDistributive : IsDistributive
        isDistributive {X} {Y} {Z} g f = begin
          bind g ∘ bind f                     ≡⟨⟩
          μ Z ∘ R.func→ g ∘ (μ Y ∘ R.func→ f) ≡⟨ sym lem2 ⟩
          μ Z ∘ R.func→ (μ Z ∘ R.func→ g ∘ f) ≡⟨⟩
          μ Z ∘ R.func→ (bind g ∘ f) ∎
          where
            -- Proved it in reverse here... otherwise it could be neatly inlined.
            lem2
              : μ Z ∘ R.func→ (μ Z ∘ R.func→ g ∘ f)
              ≡ μ Z ∘ R.func→ g ∘ (μ Y ∘ R.func→ f)
            lem2 = begin
              μ Z ∘ R.func→ (μ Z ∘ R.func→ g ∘ f)                     ≡⟨ cong (λ φ → μ Z ∘ φ) distrib ⟩
              μ Z ∘ (R.func→ (μ Z) ∘ R.func→ (R.func→ g) ∘ R.func→ f) ≡⟨⟩
              μ Z ∘ (R.func→ (μ Z) ∘ RR.func→ g ∘ R.func→ f)          ≡⟨ {!!} ⟩ -- ●-solver?
              (μ Z ∘ R.func→ (μ Z)) ∘ (RR.func→ g ∘ R.func→ f)        ≡⟨ cong (λ φ → φ ∘ (RR.func→ g ∘ R.func→ f)) lemmm ⟩
              (μ Z ∘ μ (R.func* Z)) ∘ (RR.func→ g ∘ R.func→ f)        ≡⟨ {!!} ⟩ -- ●-solver?
              μ Z ∘ μ (R.func* Z) ∘ RR.func→ g ∘ R.func→ f            ≡⟨ {!!} ⟩ -- ●-solver + lem4
              μ Z ∘ R.func→ g ∘ μ Y ∘ R.func→ f                       ≡⟨ sym (Category.isAssociative ℂ) ⟩
              μ Z ∘ R.func→ g ∘ (μ Y ∘ R.func→ f) ∎
              where
                module RR = Functor F[ R ∘ R ]
                distrib : ∀ {A B C D} {a : Arrow C D} {b : Arrow B C} {c : Arrow A B}
                  → R.func→ (a ∘ b ∘ c)
                  ≡ R.func→ a ∘ R.func→ b ∘ R.func→ c
                distrib = {!!}
                comm : ∀ {A B C D E}
                  → {a : Arrow D E} {b : Arrow C D} {c : Arrow B C} {d : Arrow A B}
                  → a ∘ (b ∘ c ∘ d) ≡ a ∘ b ∘ c ∘ d
                comm = {!!}
                μN = proj₂ μNatTrans
                lemmm : μ Z ∘ R.func→ (μ Z) ≡ μ Z ∘ μ (R.func* Z)
                lemmm = isAssociative
                lem4 : μ (R.func* Z) ∘ RR.func→ g ≡ R.func→ g ∘ μ Y
                lem4 = μN g

      module KI = K.IsMonad
      forthIsMonad : K.IsMonad (forthRaw raw)
      KI.isIdentity     forthIsMonad = isIdentity
      KI.isNatural      forthIsMonad = isNatural
      KI.isDistributive forthIsMonad = isDistributive

    forth : M.Monad → K.Monad
    Kleisli.Monad.raw     (forth m) = forthRaw     (M.Monad.raw m)
    Kleisli.Monad.isMonad (forth m) = forthIsMonad (M.Monad.isMonad m)

    module _ (m : K.Monad) where
      private
        module ℂ = Category ℂ
        open K.Monad m
        open NaturalTransformation ℂ ℂ

        rawR : RawFunctor ℂ ℂ
        RawFunctor.func* rawR   = RR
        RawFunctor.func→ rawR f = bind (pure ∘ f)

        isFunctorR : IsFunctor ℂ ℂ rawR
        IsFunctor.isIdentity isFunctorR = begin
          bind (pure ∘ 𝟙) ≡⟨ cong bind (proj₁ ℂ.isIdentity) ⟩
          bind pure       ≡⟨ isIdentity ⟩
          𝟙               ∎

        IsFunctor.isDistributive isFunctorR {f = f} {g} = begin
          bind (pure ∘ (g ∘ f))             ≡⟨⟩
          fmap (g ∘ f)                      ≡⟨ fusion ⟩
          fmap g ∘ fmap f                   ≡⟨⟩
          bind (pure ∘ g) ∘ bind (pure ∘ f) ∎

        R : Functor ℂ ℂ
        Functor.raw       R = rawR
        Functor.isFunctor R = isFunctorR

        R² : Functor ℂ ℂ
        R² = F[ R ∘ R ]

        ηNatTrans : NaturalTransformation F.identity R
        ηNatTrans = {!!}

        μNatTrans : NaturalTransformation R² R
        μNatTrans = {!!}

      module MR = M.RawMonad
      backRaw : M.RawMonad
      MR.R         backRaw = R
      MR.ηNatTrans backRaw = ηNatTrans
      MR.μNatTrans backRaw = μNatTrans

    module _ (m : K.Monad) where
      open K.Monad m
      open M.RawMonad (backRaw m)
      module Mis = M.IsMonad

      backIsMonad : M.IsMonad (backRaw m)
      backIsMonad = {!!}

    back : K.Monad → M.Monad
    Monoidal.Monad.raw     (back m) = backRaw     m
    Monoidal.Monad.isMonad (back m) = backIsMonad m

    -- I believe all the proofs here should be `refl`.
    module _ (m : K.Monad) where
      open K.RawMonad (K.Monad.raw m)
      forthRawEq : forthRaw (backRaw m) ≡ K.Monad.raw m
      K.RawMonad.RR    (forthRawEq _) = RR
      K.RawMonad.pure  (forthRawEq _) = pure
      -- stuck
      K.RawMonad.bind  (forthRawEq i) = {!!}

    fortheq : (m : K.Monad) → forth (back m) ≡ m
    fortheq m = K.Monad≡ (forthRawEq m)

    module _ (m : M.Monad) where
      open M.RawMonad (M.Monad.raw m)
      backRawEq : backRaw (forth m) ≡ M.Monad.raw m
      -- stuck
      M.RawMonad.R         (backRawEq i) = {!!}
      M.RawMonad.ηNatTrans (backRawEq i) = {!!}
      M.RawMonad.μNatTrans (backRawEq i) = {!!}

    backeq : (m : M.Monad) → back (forth m) ≡ m
    backeq m = M.Monad≡ (backRawEq m)

    open import Cubical.GradLemma
    eqv : isEquiv M.Monad K.Monad forth
    eqv = gradLemma forth back fortheq backeq

  Monoidal≃Kleisli : M.Monad ≃ K.Monad
  Monoidal≃Kleisli = forth , eqv
