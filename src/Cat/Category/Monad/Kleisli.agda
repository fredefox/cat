{---
The Kleisli formulation of monads
 ---}
{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Agda.Primitive

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor as F
open import Cat.Categories.Fun

-- "A monad in the Kleisli form" [voe]
module Cat.Category.Monad.Kleisli {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
open import Cat.Category.NaturalTransformation ℂ ℂ
  using (NaturalTransformation ; Transformation ; Natural)

private
  ℓ = ℓa ⊔ ℓb
  module ℂ = Category ℂ
  open ℂ using (Arrow ; identity ; Object ; _∘_ ; _>>>_)

-- | Data for a monad.
--
-- Note that (>>=) is not expressible in a general category because objects
-- are not generally types.
record RawMonad : Set ℓ where
  field
    omap : Object → Object
    pure : {X : Object}   → ℂ [ X , omap X ]
    bind : {X Y : Object} → ℂ [ X , omap Y ] → ℂ [ omap X , omap Y ]

  -- | functor map
  --
  -- This should perhaps be defined in a "Klesli-version" of functors as well?
  fmap : ∀ {A B} → ℂ [ A , B ] → ℂ [ omap A , omap B ]
  fmap f = bind (pure ∘ f)

  -- | Composition of monads aka. the kleisli-arrow.
  _>=>_ : {A B C : Object} → ℂ [ A , omap B ] → ℂ [ B , omap C ] → ℂ [ A , omap C ]
  f >=> g = f >>> (bind g)

  -- | Flattening nested monads.
  join : {A : Object} → ℂ [ omap (omap A) , omap A ]
  join = bind identity

  ------------------
  -- * Monad laws --
  ------------------

  -- There may be better names than what I've chosen here.

  IsIdentity     = {X : Object}
    → bind pure ≡ identity {omap X}
  IsNatural      = {X Y : Object}   (f : ℂ [ X , omap Y ])
    → pure >>> (bind f) ≡ f
  IsDistributive = {X Y Z : Object} (g : ℂ [ Y , omap Z ]) (f : ℂ [ X , omap Y ])
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
  IsInverse = {X : Object} → join {X} ∘ pure ≡ identity × join {X} ∘ fmap pure ≡ identity

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
    bind ((f >>> g) >>> pure)  ≡⟨ cong bind ℂ.isAssociative ⟩
    bind (f >>> (g >>> pure))  ≡⟨ cong (λ φ → bind (f >>> φ)) (sym (isNatural _)) ⟩
    bind (f >>> (pure >>> (bind (g >>> pure)))) ≡⟨⟩
    bind (f >>> (pure >>> fmap g)) ≡⟨⟩
    bind ((fmap g ∘ pure) ∘ f) ≡⟨ cong bind (sym ℂ.isAssociative) ⟩
    bind (fmap g ∘ (pure ∘ f)) ≡⟨ sym distrib ⟩
    bind (pure ∘ g) ∘ bind (pure ∘ f) ≡⟨⟩
    fmap g ∘ fmap f            ∎
    where
      distrib : fmap g ∘ fmap f ≡ bind (fmap g ∘ (pure ∘ f))
      distrib = isDistributive (pure ∘ g) (pure ∘ f)

  -- | This formulation gives rise to the following endo-functor.
  private
    rawR : RawFunctor ℂ ℂ
    RawFunctor.omap rawR = omap
    RawFunctor.fmap rawR = fmap

    isFunctorR : IsFunctor ℂ ℂ rawR
    IsFunctor.isIdentity isFunctorR = begin
      bind (pure ∘ identity) ≡⟨ cong bind (ℂ.rightIdentity) ⟩
      bind pure              ≡⟨ isIdentity ⟩
      identity               ∎

    IsFunctor.isDistributive isFunctorR {f = f} {g} = begin
      bind (pure ∘ (g ∘ f))             ≡⟨⟩
      fmap (g ∘ f)                      ≡⟨ fusion ⟩
      fmap g ∘ fmap f                   ≡⟨⟩
      bind (pure ∘ g) ∘ bind (pure ∘ f) ∎

  -- FIXME Naming!
  R : EndoFunctor ℂ
  Functor.raw       R = rawR
  Functor.isFunctor R = isFunctorR

  private
    R⁰ : EndoFunctor ℂ
    R⁰ = Functors.identity
    R² : EndoFunctor ℂ
    R² = F[ R ∘ R ]
    module R  = Functor R
    module R⁰ = Functor R⁰
    module R² = Functor R²
    pureT : Transformation R⁰ R
    pureT A = pure
    pureN : Natural R⁰ R pureT
    pureN {A} {B} f = begin
      pureT B             ∘ R⁰.fmap f ≡⟨⟩
      pure            ∘ f          ≡⟨ sym (isNatural _) ⟩
      bind (pure ∘ f) ∘ pure       ≡⟨⟩
      fmap f          ∘ pure       ≡⟨⟩
      R.fmap f       ∘ pureT A        ∎
    joinT : Transformation R² R
    joinT C = join
    joinN : Natural R² R joinT
    joinN f = begin
      join       ∘ R².fmap f  ≡⟨⟩
      bind identity     ∘ R².fmap f  ≡⟨⟩
      R².fmap f >>> bind identity    ≡⟨⟩
      fmap (fmap f) >>> bind identity ≡⟨⟩
      fmap (bind (f >>> pure)) >>> bind identity          ≡⟨⟩
      bind (bind (f >>> pure) >>> pure) >>> bind identity
        ≡⟨ isDistributive _ _ ⟩
      bind ((bind (f >>> pure) >>> pure) >=> identity)
        ≡⟨⟩
      bind ((bind (f >>> pure) >>> pure) >>> bind identity)
        ≡⟨ cong bind ℂ.isAssociative ⟩
      bind (bind (f >>> pure) >>> (pure >>> bind identity))
        ≡⟨ cong (λ φ → bind (bind (f >>> pure) >>> φ)) (isNatural _) ⟩
      bind (bind (f >>> pure) >>> identity)
        ≡⟨ cong bind ℂ.leftIdentity ⟩
      bind (bind (f >>> pure))
        ≡⟨ cong bind (sym ℂ.rightIdentity) ⟩
      bind (identity >>> bind (f >>> pure)) ≡⟨⟩
      bind (identity >=> (f >>> pure))
        ≡⟨ sym (isDistributive _ _) ⟩
      bind identity     >>> bind (f >>> pure)    ≡⟨⟩
      bind identity     >>> fmap f    ≡⟨⟩
      bind identity     >>> R.fmap f ≡⟨⟩
      R.fmap f  ∘ bind identity      ≡⟨⟩
      R.fmap f  ∘ join        ∎

  pureNT : NaturalTransformation R⁰ R
  fst pureNT = pureT
  snd pureNT = pureN

  joinNT : NaturalTransformation R² R
  fst joinNT = joinT
  snd joinNT = joinN

  isNaturalForeign : IsNaturalForeign
  isNaturalForeign = begin
    fmap join >>> join ≡⟨⟩
    bind (join >>> pure) >>> bind identity
      ≡⟨ isDistributive _ _ ⟩
    bind ((join >>> pure) >>> bind identity)
      ≡⟨ cong bind ℂ.isAssociative ⟩
    bind (join >>> (pure >>> bind identity))
      ≡⟨ cong (λ φ → bind (join >>> φ)) (isNatural _) ⟩
    bind (join >>> identity)
      ≡⟨ cong bind ℂ.leftIdentity ⟩
    bind join           ≡⟨⟩
    bind (bind identity)
      ≡⟨ cong bind (sym ℂ.rightIdentity) ⟩
    bind (identity >>> bind identity) ≡⟨⟩
    bind (identity >=> identity)      ≡⟨ sym (isDistributive _ _) ⟩
    bind identity >>> bind identity   ≡⟨⟩
    join >>> join       ∎

  isInverse : IsInverse
  isInverse = inv-l , inv-r
    where
    inv-l = begin
      pure >>> join   ≡⟨⟩
      pure >>> bind identity ≡⟨ isNatural _ ⟩
      identity ∎
    inv-r = begin
      fmap pure >>> join ≡⟨⟩
      bind (pure >>> pure) >>> bind identity
        ≡⟨ isDistributive _ _ ⟩
      bind ((pure >>> pure) >=> identity) ≡⟨⟩
      bind ((pure >>> pure) >>> bind identity)
        ≡⟨ cong bind ℂ.isAssociative ⟩
      bind (pure >>> (pure >>> bind identity))
        ≡⟨ cong (λ φ → bind (pure >>> φ)) (isNatural _) ⟩
      bind (pure >>> identity)
        ≡⟨ cong bind ℂ.leftIdentity ⟩
      bind pure ≡⟨ isIdentity ⟩
      identity ∎

record Monad : Set ℓ where
  field
    raw : RawMonad
    isMonad : IsMonad raw
  open IsMonad isMonad public

private
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
  private
    eqIsMonad : (λ i → IsMonad (eq i)) [ Monad.isMonad m ≡ Monad.isMonad n ]
    eqIsMonad = lemPropF propIsMonad eq

  Monad≡ : m ≡ n
  Monad.raw     (Monad≡ i) = eq i
  Monad.isMonad (Monad≡ i) = eqIsMonad i
