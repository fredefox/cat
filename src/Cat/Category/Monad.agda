{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Cat.Category.Monad where

open import Agda.Primitive

open import Data.Product

open import Cubical
open import Cubical.NType.Properties using (lemPropF)

open import Cat.Category hiding (propIsAssociative ; propIsIdentity)
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
      -- TODO rename fields here
      -- R ~ m
      R : EndoFunctor ℂ
      -- η ~ pure
      ηNatTrans : NaturalTransformation F.identity R
      -- μ ~ join
      μNatTrans : NaturalTransformation F[ R ∘ R ] R

    η : Transformation F.identity R
    η = proj₁ ηNatTrans
    ηNat : Natural F.identity R η
    ηNat = proj₂ ηNatTrans

    μ : Transformation F[ R ∘ R ] R
    μ = proj₁ μNatTrans
    μNat : Natural F[ R ∘ R ] R μ
    μNat = proj₂ μNatTrans

    private
      module R  = Functor R
    IsAssociative : Set _
    IsAssociative = {X : Object}
      → μ X ∘ R.func→ (μ X) ≡ μ X ∘ μ (R.func* X)
    IsInverse : Set _
    IsInverse = {X : Object}
      → μ X ∘ η (R.func* X) ≡ 𝟙
      × μ X ∘ R.func→ (η X) ≡ 𝟙
    IsNatural = ∀ {X Y} f → μ Y ∘ R.func→ f ∘ η X ≡ f
    IsDistributive = ∀ {X Y Z} (g : Arrow Y (R.func* Z)) (f : Arrow X (R.func* Y))
      → μ Z ∘ R.func→ g ∘ (μ Y ∘ R.func→ f)
      ≡ μ Z ∘ R.func→ (μ Z ∘ R.func→ g ∘ f)

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
      μ Y ∘ R.func→ f ∘ η X     ≡⟨ sym ℂ.isAssociative ⟩
      μ Y ∘ (R.func→ f ∘ η X)   ≡⟨ cong (λ φ → μ Y ∘ φ) (sym (ηNat f)) ⟩
      μ Y ∘ (η (R.func* Y) ∘ f) ≡⟨ ℂ.isAssociative ⟩
      μ Y ∘ η (R.func* Y) ∘ f   ≡⟨ cong (λ φ → φ ∘ f) (proj₁ isInverse) ⟩
      𝟙 ∘ f                     ≡⟨ proj₂ ℂ.isIdentity ⟩
      f                         ∎

    isDistributive : IsDistributive
    isDistributive {X} {Y} {Z} g f = sym done
      where
      module R² = Functor F[ R ∘ R ]
      postulate
        distrib : ∀ {A B C D} {a : Arrow C D} {b : Arrow B C} {c : Arrow A B}
          → R.func→ (a ∘ b ∘ c)
          ≡ R.func→ a ∘ R.func→ b ∘ R.func→ c
        comm : ∀ {A B C D E}
          → {a : Arrow D E} {b : Arrow C D} {c : Arrow B C} {d : Arrow A B}
          → a ∘ (b ∘ c ∘ d) ≡ a ∘ b ∘ c ∘ d
      lemmm : μ Z ∘ R.func→ (μ Z) ≡ μ Z ∘ μ (R.func* Z)
      lemmm = isAssociative
      lem4 : μ (R.func* Z) ∘ R².func→ g ≡ R.func→ g ∘ μ Y
      lem4 = μNat g
      done = begin
        μ Z ∘ R.func→ (μ Z ∘ R.func→ g ∘ f)                     ≡⟨ cong (λ φ → μ Z ∘ φ) distrib ⟩
        μ Z ∘ (R.func→ (μ Z) ∘ R.func→ (R.func→ g) ∘ R.func→ f) ≡⟨⟩
        μ Z ∘ (R.func→ (μ Z) ∘ R².func→ g ∘ R.func→ f)          ≡⟨ {!!} ⟩ -- ●-solver?
        (μ Z ∘ R.func→ (μ Z)) ∘ (R².func→ g ∘ R.func→ f)        ≡⟨ cong (λ φ → φ ∘ (R².func→ g ∘ R.func→ f)) lemmm ⟩
        (μ Z ∘ μ (R.func* Z)) ∘ (R².func→ g ∘ R.func→ f)        ≡⟨ {!!} ⟩ -- ●-solver?
        μ Z ∘ μ (R.func* Z) ∘ R².func→ g ∘ R.func→ f            ≡⟨ {!!} ⟩ -- ●-solver + lem4
        μ Z ∘ R.func→ g ∘ μ Y ∘ R.func→ f                       ≡⟨ sym (Category.isAssociative ℂ) ⟩
        μ Z ∘ R.func→ g ∘ (μ Y ∘ R.func→ f) ∎

  record Monad : Set ℓ where
    field
      raw : RawMonad
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
    eqIsMonad : (λ i → IsMonad (eq i)) [ Monad.isMonad m ≡ Monad.isMonad n ]
    eqIsMonad = lemPropF propIsMonad eq

    Monad≡ : m ≡ n
    Monad.raw     (Monad≡ i) = eq i
    Monad.isMonad (Monad≡ i) = eqIsMonad i

-- "A monad in the Kleisli form" [voe]
module Kleisli {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    ℓ = ℓa ⊔ ℓb
    module ℂ = Category ℂ
    open ℂ using (Arrow ; 𝟙 ; Object ; _∘_ ; _>>>_)

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

    -- In the ("foreign") formulation of a monad `IsNatural`'s analogue here would be:
    IsNaturalForeign : Set _
    IsNaturalForeign = {X : Object} → join {X} ∘ fmap join ≡ join ∘ join

    IsInverse : Set _
    IsInverse = {X : Object} → join {X} ∘ pure ≡ 𝟙 × join {X} ∘ fmap pure ≡ 𝟙

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

    -- | This formulation gives rise to the following endo-functor.
    private
      rawR : RawFunctor ℂ ℂ
      RawFunctor.func* rawR = RR
      RawFunctor.func→ rawR = fmap

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

    -- TODO: Naming!
    R : EndoFunctor ℂ
    Functor.raw       R = rawR
    Functor.isFunctor R = isFunctorR

    private
      open NaturalTransformation ℂ ℂ

      R⁰ : EndoFunctor ℂ
      R⁰ = F.identity
      R² : EndoFunctor ℂ
      R² = F[ R ∘ R ]
      module R  = Functor R
      module R⁰ = Functor R⁰
      module R² = Functor R²
      ηTrans : Transformation R⁰ R
      ηTrans A = pure
      ηNatural : Natural R⁰ R ηTrans
      ηNatural {A} {B} f = begin
        ηTrans B        ∘ R⁰.func→ f ≡⟨⟩
        pure            ∘ f          ≡⟨ sym (isNatural _) ⟩
        bind (pure ∘ f) ∘ pure       ≡⟨⟩
        fmap f          ∘ pure       ≡⟨⟩
        R.func→ f       ∘ ηTrans A   ∎
      μTrans : Transformation R² R
      μTrans C = join
      μNatural : Natural R² R μTrans
      μNatural f = begin
        join       ∘ R².func→ f  ≡⟨⟩
        bind 𝟙     ∘ R².func→ f  ≡⟨⟩
        R².func→ f >>> bind 𝟙    ≡⟨⟩
        fmap (fmap f) >>> bind 𝟙 ≡⟨⟩
        fmap (bind (f >>> pure)) >>> bind 𝟙          ≡⟨⟩
        bind (bind (f >>> pure) >>> pure) >>> bind 𝟙
          ≡⟨ isDistributive _ _ ⟩
        bind ((bind (f >>> pure) >>> pure) >=> 𝟙)
          ≡⟨⟩
        bind ((bind (f >>> pure) >>> pure) >>> bind 𝟙)
          ≡⟨ cong bind ℂ.isAssociative ⟩
        bind (bind (f >>> pure) >>> (pure >>> bind 𝟙))
          ≡⟨ cong (λ φ → bind (bind (f >>> pure) >>> φ)) (isNatural _) ⟩
        bind (bind (f >>> pure) >>> 𝟙)
          ≡⟨ cong bind (proj₂ ℂ.isIdentity) ⟩
        bind (bind (f >>> pure))
          ≡⟨ cong bind (sym (proj₁ ℂ.isIdentity)) ⟩
        bind (𝟙 >>> bind (f >>> pure)) ≡⟨⟩
        bind (𝟙 >=> (f >>> pure))
          ≡⟨ sym (isDistributive _ _) ⟩
        bind 𝟙     >>> bind (f >>> pure)    ≡⟨⟩
        bind 𝟙     >>> fmap f    ≡⟨⟩
        bind 𝟙     >>> R.func→ f ≡⟨⟩
        R.func→ f  ∘ bind 𝟙      ≡⟨⟩
        R.func→ f  ∘ join        ∎
        where

    ηNatTrans : NaturalTransformation R⁰ R
    proj₁ ηNatTrans = ηTrans
    proj₂ ηNatTrans = ηNatural

    μNatTrans : NaturalTransformation R² R
    proj₁ μNatTrans = μTrans
    proj₂ μNatTrans = μNatural

    isNaturalForeign : IsNaturalForeign
    isNaturalForeign = begin
      fmap join >>> join ≡⟨⟩
      bind (join >>> pure) >>> bind 𝟙
        ≡⟨ isDistributive _ _ ⟩
      bind ((join >>> pure) >>> bind 𝟙)
        ≡⟨ cong bind ℂ.isAssociative ⟩
      bind (join >>> (pure >>> bind 𝟙))
        ≡⟨ cong (λ φ → bind (join >>> φ)) (isNatural _) ⟩
      bind (join >>> 𝟙)
        ≡⟨ cong bind (proj₂ ℂ.isIdentity) ⟩
      bind join           ≡⟨⟩
      bind (bind 𝟙)
        ≡⟨ cong bind (sym (proj₁ ℂ.isIdentity)) ⟩
      bind (𝟙 >>> bind 𝟙) ≡⟨⟩
      bind (𝟙 >=> 𝟙)      ≡⟨ sym (isDistributive _ _) ⟩
      bind 𝟙 >>> bind 𝟙   ≡⟨⟩
      join >>> join       ∎

    isInverse : IsInverse
    isInverse = inv-l , inv-r
      where
      inv-l = begin
        pure >>> join   ≡⟨⟩
        pure >>> bind 𝟙 ≡⟨ isNatural _ ⟩
        𝟙 ∎
      inv-r = begin
        fmap pure >>> join ≡⟨⟩
        bind (pure >>> pure) >>> bind 𝟙
          ≡⟨ isDistributive _ _ ⟩
        bind ((pure >>> pure) >=> 𝟙) ≡⟨⟩
        bind ((pure >>> pure) >>> bind 𝟙)
          ≡⟨ cong bind ℂ.isAssociative ⟩
        bind (pure >>> (pure >>> bind 𝟙))
          ≡⟨ cong (λ φ → bind (pure >>> φ)) (isNatural _) ⟩
        bind (pure >>> 𝟙)
          ≡⟨ cong bind (proj₂ ℂ.isIdentity) ⟩
        bind pure ≡⟨ isIdentity ⟩
        𝟙 ∎

  record Monad : Set ℓ where
    field
      raw : RawMonad
      isMonad : IsMonad raw
    open IsMonad isMonad public

  module _ (raw : RawMonad) where
    open RawMonad raw
    postulate
      propIsIdentity     : isProp IsIdentity
      propIsNatural      : isProp IsNatural
      propIsDistributive : isProp IsDistributive
  open IsMonad
  propIsMonad : (raw : _) → isProp (IsMonad raw)
  IsMonad.isIdentity     (propIsMonad raw x y i)
    = propIsIdentity raw (isIdentity x) (isIdentity y) i
  IsMonad.isNatural      (propIsMonad raw x y i)
    = propIsNatural raw (isNatural x) (isNatural y) i
  IsMonad.isDistributive (propIsMonad raw x y i)
    = propIsDistributive raw (isDistributive x) (isDistributive y) i
  module _ {m n : Monad} (eq : Monad.raw m ≡ Monad.raw n) where
    eqIsMonad : (λ i → IsMonad (eq i)) [ Monad.isMonad m ≡ Monad.isMonad n ]
    eqIsMonad = lemPropF propIsMonad eq

    Monad≡ : m ≡ n
    Monad.raw     (Monad≡ i) = eq i
    Monad.isMonad (Monad≡ i) = eqIsMonad i

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
        module MI = M.IsMonad m
        module KI = K.IsMonad
      forthIsMonad : K.IsMonad (forthRaw raw)
      KI.isIdentity     forthIsMonad = proj₂ MI.isInverse
      KI.isNatural      forthIsMonad = MI.isNatural
      KI.isDistributive forthIsMonad = MI.isDistributive

    forth : M.Monad → K.Monad
    Kleisli.Monad.raw     (forth m) = forthRaw     (M.Monad.raw m)
    Kleisli.Monad.isMonad (forth m) = forthIsMonad (M.Monad.isMonad m)

    module _ (m : K.Monad) where
      private
        open K.Monad m
        module MR = M.RawMonad
        module MI = M.IsMonad

      backRaw : M.RawMonad
      MR.R         backRaw = R
      MR.ηNatTrans backRaw = ηNatTrans
      MR.μNatTrans backRaw = μNatTrans

      private
        open MR backRaw
        module R = Functor (MR.R backRaw)

      backIsMonad : M.IsMonad backRaw
      MI.isAssociative backIsMonad {X} = begin
        μ X  ∘ R.func→ (μ X)  ≡⟨⟩
        join ∘ fmap (μ X)     ≡⟨⟩
        join ∘ fmap join      ≡⟨ isNaturalForeign ⟩
        join ∘ join           ≡⟨⟩
        μ X  ∘ μ (R.func* X)  ∎
      MI.isInverse backIsMonad {X} = inv-l , inv-r
        where
        inv-l = begin
          μ X ∘ η (R.func* X) ≡⟨⟩
          join ∘ pure         ≡⟨ proj₁ isInverse ⟩
          𝟙 ∎
        inv-r = begin
          μ X ∘ R.func→ (η X) ≡⟨⟩
          join ∘ fmap pure    ≡⟨ proj₂ isInverse ⟩
          𝟙 ∎

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
