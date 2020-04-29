-- This module Essentially just provides the data for natural transformations
--
-- This includes:
--
-- The types:
--
-- * Transformation        - a family of functors
-- * Natural               - naturality condition for transformations
-- * NaturalTransformation - both of the above
--
-- Elements of the above:
--
-- * identityTrans   - the identity transformation
-- * identityNatural - naturality for the above
-- * identity        - both of the above
--
-- Functions for manipulating the above:
--
-- * A composition operator.
{-# OPTIONS --cubical #-}
open import Cat.Prelude

open import Data.Nat using (_≤′_ ; ≤′-refl ; ≤′-step)
module Nat = Data.Nat

open import Cat.Category
open import Cat.Category.Functor

module Cat.Category.NaturalTransformation
  {ℓc ℓc' ℓd ℓd' : Level}
  (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where

open Category using (Object)
private
  module ℂ = Category ℂ
  module 𝔻 = Category 𝔻

module _ (F G : Functor ℂ 𝔻) where
  private
    module F = Functor F
    module G = Functor G
  -- What do you call a non-natural tranformation?
  Transformation : Set (ℓc ⊔ ℓd')
  Transformation = (C : Object ℂ) → 𝔻 [ F.omap C , G.omap C ]

  Natural : Transformation → Set (ℓc ⊔ (ℓc' ⊔ ℓd'))
  Natural θ
    = {A B : Object ℂ}
    → (f : ℂ [ A , B ])
    → 𝔻 [ θ B ∘ F.fmap f ] ≡ 𝔻 [ G.fmap f ∘ θ A ]

  NaturalTransformation : Set (ℓc ⊔ ℓc' ⊔ ℓd')
  NaturalTransformation = Σ Transformation Natural

  -- Think I need propPi and that arrows are sets
  propIsNatural : (θ : _) → isProp (Natural θ)
  propIsNatural θ x y i {A} {B} f = 𝔻.arrowsAreSets _ _ (x f) (y f) i

  NaturalTransformation≡ : {α β : NaturalTransformation}
    → (eq₁ : α .fst ≡ β .fst)
    → α ≡ β
  NaturalTransformation≡ eq = lemSig propIsNatural eq

identityTrans : (F : Functor ℂ 𝔻) → Transformation F F
identityTrans F C = 𝔻.identity

identityNatural : (F : Functor ℂ 𝔻) → Natural F F (identityTrans F)
identityNatural F {A = A} {B = B} f = begin
  𝔻 [ identityTrans F B ∘ F→ f ]  ≡⟨⟩
  𝔻 [ 𝔻.identity ∘  F→ f ]       ≡⟨ 𝔻.leftIdentity ⟩
  F→ f                            ≡⟨ sym 𝔻.rightIdentity ⟩
  𝔻 [ F→ f ∘ 𝔻.identity ]        ≡⟨⟩
  𝔻 [ F→ f ∘ identityTrans F A ]  ∎
  where
    module F = Functor F
    F→ = F.fmap

identity : (F : Functor ℂ 𝔻) → NaturalTransformation F F
identity F = identityTrans F , identityNatural F

module _ {F G H : Functor ℂ 𝔻} where
  private
    module F = Functor F
    module G = Functor G
    module H = Functor H
  T[_∘_] : Transformation G H → Transformation F G → Transformation F H
  T[ θ ∘ η ] C = 𝔻 [ θ C ∘ η C ]

  NT[_∘_] : NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
  fst NT[ (θ , _) ∘ (η , _) ] = T[ θ ∘ η ]
  snd NT[ (θ , θNat) ∘ (η , ηNat) ] {A} {B} f = begin
    𝔻 [ T[ θ ∘ η ] B ∘ F.fmap f ]     ≡⟨⟩
    𝔻 [ 𝔻 [ θ B ∘ η B ] ∘ F.fmap f ] ≡⟨ sym 𝔻.isAssociative ⟩
    𝔻 [ θ B ∘ 𝔻 [ η B ∘ F.fmap f ] ] ≡⟨ cong (λ φ → 𝔻 [ θ B ∘ φ ]) (ηNat f) ⟩
    𝔻 [ θ B ∘ 𝔻 [ G.fmap f ∘ η A ] ] ≡⟨ 𝔻.isAssociative ⟩
    𝔻 [ 𝔻 [ θ B ∘ G.fmap f ] ∘ η A ] ≡⟨ cong (λ φ → 𝔻 [ φ ∘ η A ]) (θNat f) ⟩
    𝔻 [ 𝔻 [ H.fmap f ∘ θ A ] ∘ η A ] ≡⟨ sym 𝔻.isAssociative ⟩
    𝔻 [ H.fmap f ∘ 𝔻 [ θ A ∘ η A ] ] ≡⟨⟩
    𝔻 [ H.fmap f ∘ T[ θ ∘ η ] A ]     ∎

module Properties where
  module _ {F G : Functor ℂ 𝔻} where
    transformationIsSet : isSet (Transformation F G)
    transformationIsSet _ _ p q i j C = 𝔻.arrowsAreSets _ _ (λ l → p l C)   (λ l → q l C) i j

    naturalIsProp : (θ : Transformation F G) → isProp (Natural F G θ)
    naturalIsProp θ θNat θNat' = lem
      where
      lem : (λ _ → Natural F G θ) [ (λ f → θNat f) ≡ (λ f → θNat' f) ]
      lem = λ i f → 𝔻.arrowsAreSets _ _ (θNat f) (θNat' f) i

    naturalIsSet : (θ : Transformation F G) → isSet (Natural F G θ)
    naturalIsSet θ = propSet (naturalIsProp θ)

    naturalTransformationIsSet : isSet (NaturalTransformation F G)
    naturalTransformationIsSet = setSig transformationIsSet naturalIsSet

  module _
    {F G H I : Functor ℂ 𝔻}
    {θ : NaturalTransformation F G}
    {η : NaturalTransformation G H}
    {ζ : NaturalTransformation H I} where
    -- isAssociative : NT[ ζ ∘ NT[ η ∘ θ ] ] ≡ NT[ NT[ ζ ∘ η ] ∘ θ ]
    isAssociative
      : NT[_∘_] {F} {H} {I} ζ (NT[_∘_] {F} {G} {H} η θ)
      ≡ NT[_∘_] {F} {G} {I} (NT[_∘_] {G} {H} {I} ζ η) θ
    isAssociative
      = lemSig (naturalIsProp {F = F} {I})
        (funExt (λ _ → 𝔻.isAssociative))

  module _ {F G : Functor ℂ 𝔻} {θNT : NaturalTransformation F G} where
    private
      propNat = naturalIsProp {F = F} {G}

    rightIdentity : (NT[_∘_] {F} {F} {G} θNT (identity F)) ≡ θNT
    rightIdentity = lemSig propNat (funExt (λ _ → 𝔻.rightIdentity))

    leftIdentity : (NT[_∘_] {F} {G} {G} (identity G) θNT) ≡ θNT
    leftIdentity = lemSig propNat (funExt (λ _ → 𝔻.leftIdentity))

    isIdentity
      : ((NT[_∘_] {F} {G} {G} (identity G) θNT) ≡ θNT)
      × ((NT[_∘_] {F} {F} {G} θNT (identity F)) ≡ θNT)
    isIdentity = leftIdentity , rightIdentity
