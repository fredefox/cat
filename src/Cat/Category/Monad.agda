{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Cat.Category.Monad where

open import Agda.Primitive

open import Data.Product

open import Cubical
open import Cubical.NType.Properties using (lemPropF ; lemSig)

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
      -- TODO rename fields here
      -- R ~ m
      R : EndoFunctor ℂ
      pureNT : NaturalTransformation F.identity R
      joinNT : NaturalTransformation F[ R ∘ R ] R

    -- Note that `pureT` and `joinT` differs from their definition in the
    -- kleisli formulation only by having an explicit parameter.
    pureT : Transformation F.identity R
    pureT = proj₁ pureNT
    pureN : Natural F.identity R pureT
    pureN = proj₂ pureNT

    joinT : Transformation F[ R ∘ R ] R
    joinT = proj₁ joinNT
    joinN : Natural F[ R ∘ R ] R joinT
    joinN = proj₂ joinNT

    private
      module R  = Functor R

    Romap = Functor.func* R
    Rfmap = Functor.func→ R

    bind : {X Y : Object} → ℂ [ X , Romap Y ] → ℂ [ Romap X , Romap Y ]
    bind {X} {Y} f = joinT Y ∘ Rfmap f

    IsAssociative : Set _
    IsAssociative = {X : Object}
      → joinT X ∘ R.func→ (joinT X) ≡ joinT X ∘ joinT (R.func* X)
    IsInverse : Set _
    IsInverse = {X : Object}
      → joinT X ∘ pureT (R.func* X) ≡ 𝟙
      × joinT X ∘ R.func→ (pureT X) ≡ 𝟙
    IsNatural = ∀ {X Y} f → joinT Y ∘ R.func→ f ∘ pureT X ≡ f
    IsDistributive = ∀ {X Y Z} (g : Arrow Y (R.func* Z)) (f : Arrow X (R.func* Y))
      → joinT Z ∘ R.func→ g ∘ (joinT Y ∘ R.func→ f)
      ≡ joinT Z ∘ R.func→ (joinT Z ∘ R.func→ g ∘ f)

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
      joinT Y ∘ R.func→ f ∘ pureT X     ≡⟨ sym ℂ.isAssociative ⟩
      joinT Y ∘ (R.func→ f ∘ pureT X)   ≡⟨ cong (λ φ → joinT Y ∘ φ) (sym (pureN f)) ⟩
      joinT Y ∘ (pureT (R.func* Y) ∘ f) ≡⟨ ℂ.isAssociative ⟩
      joinT Y ∘ pureT (R.func* Y) ∘ f   ≡⟨ cong (λ φ → φ ∘ f) (proj₁ isInverse) ⟩
      𝟙 ∘ f                     ≡⟨ proj₂ ℂ.isIdentity ⟩
      f                         ∎

    isDistributive : IsDistributive
    isDistributive {X} {Y} {Z} g f = sym aux
      where
      module R² = Functor F[ R ∘ R ]
      distrib3 : ∀ {A B C D} {a : Arrow C D} {b : Arrow B C} {c : Arrow A B}
        → R.func→ (a ∘ b ∘ c)
        ≡ R.func→ a ∘ R.func→ b ∘ R.func→ c
      distrib3 {a = a} {b} {c} = begin
        R.func→ (a ∘ b ∘ c)               ≡⟨ R.isDistributive ⟩
        R.func→ (a ∘ b) ∘ R.func→ c       ≡⟨ cong (_∘ _) R.isDistributive ⟩
        R.func→ a ∘ R.func→ b ∘ R.func→ c ∎
      aux = begin
        joinT Z ∘ R.func→ (joinT Z ∘ R.func→ g ∘ f)
          ≡⟨ cong (λ φ → joinT Z ∘ φ) distrib3 ⟩
        joinT Z ∘ (R.func→ (joinT Z) ∘ R.func→ (R.func→ g) ∘ R.func→ f)
          ≡⟨⟩
        joinT Z ∘ (R.func→ (joinT Z) ∘ R².func→ g ∘ R.func→ f)
          ≡⟨ cong (_∘_ (joinT Z)) (sym ℂ.isAssociative) ⟩
        joinT Z ∘ (R.func→ (joinT Z) ∘ (R².func→ g ∘ R.func→ f))
          ≡⟨ ℂ.isAssociative ⟩
        (joinT Z ∘ R.func→ (joinT Z)) ∘ (R².func→ g ∘ R.func→ f)
          ≡⟨ cong (λ φ → φ ∘ (R².func→ g ∘ R.func→ f)) isAssociative ⟩
        (joinT Z ∘ joinT (R.func* Z)) ∘ (R².func→ g ∘ R.func→ f)
          ≡⟨ ℂ.isAssociative ⟩
        joinT Z ∘ joinT (R.func* Z) ∘ R².func→ g ∘ R.func→ f
          ≡⟨⟩
        ((joinT Z ∘ joinT (R.func* Z)) ∘ R².func→ g) ∘ R.func→ f
          ≡⟨ cong (_∘ R.func→ f) (sym ℂ.isAssociative) ⟩
        (joinT Z ∘ (joinT (R.func* Z) ∘ R².func→ g)) ∘ R.func→ f
          ≡⟨ cong (λ φ → φ ∘ R.func→ f) (cong (_∘_ (joinT Z)) (joinN g)) ⟩
        (joinT Z ∘ (R.func→ g ∘ joinT Y)) ∘ R.func→ f
          ≡⟨ cong (_∘ R.func→ f) ℂ.isAssociative ⟩
        joinT Z ∘ R.func→ g ∘ joinT Y ∘ R.func→ f
          ≡⟨ sym (Category.isAssociative ℂ) ⟩
        joinT Z ∘ R.func→ g ∘ (joinT Y ∘ R.func→ f)
          ∎

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
      Romap : Object → Object
      -- Note name-change from [voe]
      pure : {X : Object} → ℂ [ X , Romap X ]
      bind : {X Y : Object} → ℂ [ X , Romap Y ] → ℂ [ Romap X , Romap Y ]

    -- | functor map
    --
    -- This should perhaps be defined in a "Klesli-version" of functors as well?
    fmap : ∀ {A B} → ℂ [ A , B ] → ℂ [ Romap A , Romap B ]
    fmap f = bind (pure ∘ f)

    -- | Composition of monads aka. the kleisli-arrow.
    _>=>_ : {A B C : Object} → ℂ [ A , Romap B ] → ℂ [ B , Romap C ] → ℂ [ A , Romap C ]
    f >=> g = f >>> (bind g)

    -- | Flattening nested monads.
    join : {A : Object} → ℂ [ Romap (Romap A) , Romap A ]
    join = bind 𝟙

    ------------------
    -- * Monad laws --
    ------------------

    -- There may be better names than what I've chosen here.

    IsIdentity     = {X : Object}
      → bind pure ≡ 𝟙 {Romap X}
    IsNatural      = {X Y : Object}   (f : ℂ [ X , Romap Y ])
      → pure >>> (bind f) ≡ f
    IsDistributive = {X Y Z : Object} (g : ℂ [ Y , Romap Z ]) (f : ℂ [ X , Romap Y ])
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
      RawFunctor.func* rawR = Romap
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
      pureT : Transformation R⁰ R
      pureT A = pure
      pureN : Natural R⁰ R pureT
      pureN {A} {B} f = begin
        pureT B             ∘ R⁰.func→ f ≡⟨⟩
        pure            ∘ f          ≡⟨ sym (isNatural _) ⟩
        bind (pure ∘ f) ∘ pure       ≡⟨⟩
        fmap f          ∘ pure       ≡⟨⟩
        R.func→ f       ∘ pureT A        ∎
      joinT : Transformation R² R
      joinT C = join
      joinN : Natural R² R joinT
      joinN f = begin
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

    pureNT : NaturalTransformation R⁰ R
    proj₁ pureNT = pureT
    proj₂ pureNT = pureN

    joinNT : NaturalTransformation R² R
    proj₁ joinNT = joinT
    proj₂ joinNT = joinN

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
    propIsIdentity : isProp IsIdentity
    propIsIdentity x y i = ℂ.arrowsAreSets _ _ x y i
    propIsNatural      : isProp IsNatural
    propIsNatural x y i = λ f
      → ℂ.arrowsAreSets _ _ (x f) (y f) i
    propIsDistributive : isProp IsDistributive
    propIsDistributive x y i = λ g f
      → ℂ.arrowsAreSets _ _ (x g f) (y g f) i

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
    module ℂ = Category ℂ
    open ℂ using (Object ; Arrow ; 𝟙 ; _∘_ ; _>>>_)
    open Functor using (func* ; func→)
    module M = Monoidal ℂ
    module K = Kleisli  ℂ

    module _ (m : M.RawMonad) where
      open M.RawMonad m

      forthRaw : K.RawMonad
      K.RawMonad.Romap   forthRaw = Romap
      K.RawMonad.pure forthRaw = pureT _
      K.RawMonad.bind forthRaw = bind

    module _ {raw : M.RawMonad} (m : M.IsMonad raw) where
      private
        module MI = M.IsMonad m
      forthIsMonad : K.IsMonad (forthRaw raw)
      K.IsMonad.isIdentity     forthIsMonad = proj₂ MI.isInverse
      K.IsMonad.isNatural      forthIsMonad = MI.isNatural
      K.IsMonad.isDistributive forthIsMonad = MI.isDistributive

    forth : M.Monad → K.Monad
    Kleisli.Monad.raw     (forth m) = forthRaw     (M.Monad.raw m)
    Kleisli.Monad.isMonad (forth m) = forthIsMonad (M.Monad.isMonad m)

    module _ (m : K.Monad) where
      private
        open K.Monad m
        module MR = M.RawMonad
        module MI = M.IsMonad

      backRaw : M.RawMonad
      MR.R      backRaw = R
      MR.pureNT backRaw = pureNT
      MR.joinNT backRaw = joinNT

      private
        open MR backRaw
        module R = Functor (MR.R backRaw)

      backIsMonad : M.IsMonad backRaw
      MI.isAssociative backIsMonad {X} = begin
        joinT X  ∘ R.func→ (joinT X)  ≡⟨⟩
        join ∘ fmap (joinT X)     ≡⟨⟩
        join ∘ fmap join      ≡⟨ isNaturalForeign ⟩
        join ∘ join           ≡⟨⟩
        joinT X  ∘ joinT (R.func* X)  ∎
      MI.isInverse backIsMonad {X} = inv-l , inv-r
        where
        inv-l = begin
          joinT X ∘ pureT (R.func* X) ≡⟨⟩
          join ∘ pure         ≡⟨ proj₁ isInverse ⟩
          𝟙 ∎
        inv-r = begin
          joinT X ∘ R.func→ (pureT X) ≡⟨⟩
          join ∘ fmap pure    ≡⟨ proj₂ isInverse ⟩
          𝟙 ∎

    back : K.Monad → M.Monad
    Monoidal.Monad.raw     (back m) = backRaw     m
    Monoidal.Monad.isMonad (back m) = backIsMonad m

    -- I believe all the proofs here should be `refl`.
    module _ (m : K.Monad) where
      open K.Monad m
      -- open K.RawMonad (K.Monad.raw m)
      bindEq : ∀ {X Y}
        → K.RawMonad.bind (forthRaw (backRaw m)) {X} {Y}
        ≡ K.RawMonad.bind (K.Monad.raw m)
      bindEq {X} {Y} = begin
        K.RawMonad.bind (forthRaw (backRaw m)) ≡⟨⟩
        (λ f → joinT Y  ∘ func→ R f)             ≡⟨⟩
        (λ f → join ∘ fmap f)                ≡⟨⟩
        (λ f → bind (f >>> pure) >>> bind 𝟙) ≡⟨ funExt lem ⟩
        (λ f → bind f)                       ≡⟨⟩
        bind                                 ∎
        where
        joinT = proj₁ joinNT
        lem : (f : Arrow X (Romap Y)) → bind (f >>> pure) >>> bind 𝟙 ≡ bind f
        lem f = begin
          bind (f >>> pure) >>> bind 𝟙
            ≡⟨ isDistributive _ _ ⟩
          bind ((f >>> pure) >>> bind 𝟙)
            ≡⟨ cong bind ℂ.isAssociative ⟩
          bind (f >>> (pure >>> bind 𝟙))
            ≡⟨ cong (λ φ → bind (f >>> φ)) (isNatural _) ⟩
          bind (f >>> 𝟙)
            ≡⟨ cong bind (proj₂ ℂ.isIdentity) ⟩
          bind f ∎

      _&_ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → A → (A → B) → B
      x & f = f x

      forthRawEq : forthRaw (backRaw m) ≡ K.Monad.raw m
      K.RawMonad.Romap    (forthRawEq _) = Romap
      K.RawMonad.pure  (forthRawEq _) = pure
      -- stuck
      K.RawMonad.bind  (forthRawEq i) = bindEq i

    fortheq : (m : K.Monad) → forth (back m) ≡ m
    fortheq m = K.Monad≡ (forthRawEq m)

    module _ (m : M.Monad) where
      open M.RawMonad (M.Monad.raw m)
      rawEq* : Functor.func* (K.Monad.R (forth m)) ≡ Functor.func* R
      rawEq* = refl
      left  = Functor.raw (K.Monad.R (forth m))
      right = Functor.raw R
      P : (omap : Omap ℂ ℂ)
        → (eq : RawFunctor.func* left ≡ omap)
        → (fmap' : Fmap ℂ ℂ omap)
        → Set _
      P _ eq fmap' = (λ i → Fmap ℂ ℂ (eq i))
        [ RawFunctor.func→ left ≡ fmap' ]

      module KM = K.Monad (forth m)
      rawEq→ : (λ i → Fmap ℂ ℂ (refl i)) [ Functor.func→ (K.Monad.R (forth m)) ≡ Functor.func→ R ]
      -- aka:
      --
      --     rawEq→ : P (RawFunctor.func* right) refl (RawFunctor.func→ right)
      rawEq→ = begin
        (λ f → RawFunctor.func→ left f) ≡⟨⟩
        (λ f → KM.fmap f)               ≡⟨⟩
        (λ f → KM.bind (f >>> KM.pure)) ≡⟨ {!!} ⟩
        (λ f → Rfmap f)                 ≡⟨⟩
        (λ f → RawFunctor.func→ right f) ∎

      -- This goal is more general than the above goal which I also don't know
      -- how to close.
      p : (fmap' : Fmap ℂ ℂ (RawFunctor.func* left))
        → (λ i → Fmap ℂ ℂ Romap) [ RawFunctor.func→ left ≡ fmap' ]
      -- aka:
      --
      --     p : P (RawFunctor.func* left) refl
      p fmap' = begin
        (λ f → RawFunctor.func→ left f) ≡⟨⟩
        (λ f → KM.fmap f)               ≡⟨⟩
        (λ f → KM.bind (f >>> KM.pure)) ≡⟨ {!!} ⟩
        (λ f → fmap' f) ∎

      rawEq : Functor.raw (K.Monad.R (forth m)) ≡ Functor.raw R
      rawEq = RawFunctor≡ ℂ ℂ {x = left} {right} (λ _ → Romap) p

      Req : M.RawMonad.R (backRaw (forth m)) ≡ R
      Req = Functor≡ rawEq

      open NaturalTransformation ℂ ℂ
      postulate
        pureNTEq : (λ i → NaturalTransformation F.identity (Req i))
          [ M.RawMonad.pureNT (backRaw (forth m)) ≡ pureNT ]
      backRawEq : backRaw (forth m) ≡ M.Monad.raw m
      -- stuck
      M.RawMonad.R         (backRawEq i) = Req i
      M.RawMonad.pureNT (backRawEq i) = {!!} -- pureNTEq i
      M.RawMonad.joinNT (backRawEq i) = {!!}

    backeq : (m : M.Monad) → back (forth m) ≡ m
    backeq m = M.Monad≡ (backRawEq m)

    open import Cubical.GradLemma
    eqv : isEquiv M.Monad K.Monad forth
    eqv = gradLemma forth back fortheq backeq

  Monoidal≃Kleisli : M.Monad ≃ K.Monad
  Monoidal≃Kleisli = forth , eqv
