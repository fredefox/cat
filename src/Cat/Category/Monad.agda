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
      ηNat : NaturalTransformation F.identity R
      -- μ ~ join
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

  open Category ℂ using (Arrow ; 𝟙 ; Object ; _∘_)
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
    fmap : ∀ {A B} → ℂ [ A , B ] → ℂ [ RR A , RR B ]
    fmap f = rr (ζ ∘ f)
    -- Why is (>>=) not implementable?
    --
    -- (>>=) : m a -> (a -> m b) -> m b
    -- (>=>) : (a -> m b) -> (b -> m c) -> a -> m c
    _>=>_ : {A B C : Object} → ℂ [ A , RR B ] → ℂ [ B , RR C ] → ℂ [ A , RR C ]
    f >=> g = rr g ∘ f

    -- fmap id ≡ id
    IsIdentity     = {X : Object}
      → rr ζ ≡ 𝟙 {RR X}
    IsNatural      = {X Y : Object}   (f : ℂ [ X , RR Y ])
      → rr f ∘ ζ ≡ f
    IsDistributive = {X Y Z : Object} (g : ℂ [ Y , RR Z ]) (f : ℂ [ X , RR Y ])
      → rr g ∘ rr f ≡ rr (rr g ∘ f)
    Fusion = {X Y Z : Object} {g : ℂ [ Y , Z ]} {f : ℂ [ X , Y ]}
      → fmap (g ∘ f) ≡ fmap g ∘ fmap f

  record IsMonad (raw : RawMonad) : Set ℓ where
    open RawMonad raw public
    field
      isIdentity     : IsIdentity
      isNatural      : IsNatural
      isDistributive : IsDistributive
    fusion : Fusion
    fusion {g = g} {f} = begin
      fmap (g ∘ f)              ≡⟨⟩
      rr (ζ ∘ (g ∘ f))          ≡⟨ {!!} ⟩
      rr (rr (ζ ∘ g) ∘ (ζ ∘ f)) ≡⟨ sym lem ⟩
      rr (ζ ∘ g) ∘ rr (ζ ∘ f)   ≡⟨⟩
      fmap g ∘ fmap f           ∎
      where
        lem : rr (ζ ∘ g) ∘ rr (ζ ∘ f) ≡ rr (rr (ζ ∘ g) ∘ (ζ ∘ f))
        lem = isDistributive (ζ ∘ g) (ζ ∘ f)

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

        ζ : {X : Object} → ℂ [ X , RR X ]
        ζ {X} = η X

        rr : {X Y : Object} → ℂ [ X , RR Y ] → ℂ [ RR X , RR Y ]
        rr {X} {Y} f = μ Y ∘ func→ R f

      forthRaw : K.RawMonad
      Kraw.RR forthRaw = RR
      Kraw.ζ  forthRaw = ζ
      Kraw.rr forthRaw = rr

    module _ {raw : M.RawMonad} (m : M.IsMonad raw) where
      private
        open M.IsMonad m
        open K.RawMonad (forthRaw raw)
        module Kis = K.IsMonad

        isIdentity : IsIdentity
        isIdentity {X} = begin
          rr ζ                      ≡⟨⟩
          rr (η X)                  ≡⟨⟩
          μ X ∘ func→ R (η X)       ≡⟨ proj₂ isInverse ⟩
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
            open NaturalTransformation
            module ℂ = Category ℂ
            ηN : Natural ℂ ℂ F.identity R η
            ηN = proj₂ ηNat

        isDistributive : IsDistributive
        isDistributive {X} {Y} {Z} g f = begin
          rr g ∘ rr f                         ≡⟨⟩
          μ Z ∘ R.func→ g ∘ (μ Y ∘ R.func→ f) ≡⟨ sym lem2 ⟩
          μ Z ∘ R.func→ (μ Z ∘ R.func→ g ∘ f) ≡⟨⟩
          μ Z ∘ R.func→ (rr g ∘ f) ∎
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
                μN = proj₂ μNat
                lemmm : μ Z ∘ R.func→ (μ Z) ≡ μ Z ∘ μ (R.func* Z)
                lemmm = isAssociative
                lem4 : μ (R.func* Z) ∘ RR.func→ g ≡ R.func→ g ∘ μ Y
                lem4 = μN g

      forthIsMonad : K.IsMonad (forthRaw raw)
      Kis.isIdentity forthIsMonad = isIdentity
      Kis.isNatural forthIsMonad = isNatural
      Kis.isDistributive forthIsMonad = isDistributive

    forth : M.Monad → K.Monad
    Kleisli.Monad.raw     (forth m) = forthRaw     (M.Monad.raw m)
    Kleisli.Monad.isMonad (forth m) = forthIsMonad (M.Monad.isMonad m)

    module _ (m : K.Monad) where
      private
        module ℂ = Category ℂ
        open K.Monad m
        module Mraw = M.RawMonad
        open NaturalTransformation ℂ ℂ

        rawR : RawFunctor ℂ ℂ
        RawFunctor.func* rawR = RR
        RawFunctor.func→ rawR f = rr (ζ ∘ f)

        isFunctorR : IsFunctor ℂ ℂ rawR
        IsFunctor.isIdentity     isFunctorR = begin
          rr (ζ ∘ 𝟙) ≡⟨ cong rr (proj₁ ℂ.isIdentity) ⟩
          rr ζ       ≡⟨ isIdentity ⟩
          𝟙 ∎
        IsFunctor.isDistributive isFunctorR {f = f} {g} = begin
          rr (ζ ∘ (g ∘ f))        ≡⟨⟩
          fmap (g ∘ f)            ≡⟨ fusion ⟩
          fmap g ∘ fmap f         ≡⟨⟩
          rr (ζ ∘ g) ∘ rr (ζ ∘ f) ∎

        R : Functor ℂ ℂ
        Functor.raw       R = rawR
        Functor.isFunctor R = isFunctorR

        R2 : Functor ℂ ℂ
        R2 = F[ R ∘ R ]

        ηNat : NaturalTransformation F.identity R
        ηNat = {!!}

        μNat : NaturalTransformation R2 R
        μNat = {!!}

      backRaw : M.RawMonad
      Mraw.R    backRaw = R
      Mraw.ηNat backRaw = ηNat
      Mraw.μNat backRaw = μNat

    module _ (m : K.Monad) where
      open K.Monad m
      open M.RawMonad (backRaw m)
      module Mis = M.IsMonad

      backIsMonad : M.IsMonad (backRaw m)
      backIsMonad = {!!}

    back : K.Monad → M.Monad
    Monoidal.Monad.raw     (back m) = backRaw     m
    Monoidal.Monad.isMonad (back m) = backIsMonad m


    forthRawEq : (m : K.Monad) → forthRaw (backRaw m) ≡ K.Monad.raw m
    K.RawMonad.RR (forthRawEq m _) = K.RawMonad.RR (K.Monad.raw m)
    K.RawMonad.ζ  (forthRawEq m _) = K.RawMonad.ζ  (K.Monad.raw m)
    -- stuck
    K.RawMonad.rr (forthRawEq m i) = {!!}

    fortheq : (m : K.Monad) → forth (back m) ≡ m
    fortheq m = K.Monad≡ (forthRawEq m)

    backRawEq : (m : M.Monad) → backRaw (forth m) ≡ M.Monad.raw m
    -- stuck
    M.RawMonad.R    (backRawEq m _) = ?
    M.RawMonad.ηNat (backRawEq m x) = {!!}
    M.RawMonad.μNat (backRawEq m x) = {!!}

    backeq : (m : M.Monad) → back (forth m) ≡ m
    backeq m = M.Monad≡ (backRawEq m)

    open import Cubical.GradLemma
    eqv : isEquiv M.Monad K.Monad forth
    eqv = gradLemma forth back fortheq backeq

  Monoidal≃Kleisli : M.Monad ≃ K.Monad
  Monoidal≃Kleisli = forth , eqv
