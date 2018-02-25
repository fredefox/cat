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
{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Category.NaturalTransformation where
open import Agda.Primitive
open import Data.Product

open import Cubical

open import Cat.Category
open import Cat.Category.Functor hiding (identity)

module NaturalTransformation {ℓc ℓc' ℓd ℓd' : Level}
  (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  open Category using (Object ; 𝟙)

  module _ (F G : Functor ℂ 𝔻) where
    private
      module F = Functor F
      module G = Functor G
    -- What do you call a non-natural tranformation?
    Transformation : Set (ℓc ⊔ ℓd')
    Transformation = (C : Object ℂ) → 𝔻 [ F.func* C , G.func* C ]

    Natural : Transformation → Set (ℓc ⊔ (ℓc' ⊔ ℓd'))
    Natural θ
      = {A B : Object ℂ}
      → (f : ℂ [ A , B ])
      → 𝔻 [ θ B ∘ F.func→ f ] ≡ 𝔻 [ G.func→ f ∘ θ A ]

    NaturalTransformation : Set (ℓc ⊔ ℓc' ⊔ ℓd')
    NaturalTransformation = Σ Transformation Natural

    -- TODO: Since naturality is a mere proposition this principle can be
    -- simplified.
    NaturalTransformation≡ : {α β : NaturalTransformation}
      → (eq₁ : α .proj₁ ≡ β .proj₁)
      → (eq₂ : PathP
          (λ i → {A B : Object ℂ} (f : ℂ [ A , B ])
            → 𝔻 [ eq₁ i B ∘ F.func→ f ]
            ≡ 𝔻 [ G.func→ f ∘ eq₁ i A ])
        (α .proj₂) (β .proj₂))
      → α ≡ β
    NaturalTransformation≡ eq₁ eq₂ i = eq₁ i , eq₂ i

  identityTrans : (F : Functor ℂ 𝔻) → Transformation F F
  identityTrans F C = 𝟙 𝔻

  identityNatural : (F : Functor ℂ 𝔻) → Natural F F (identityTrans F)
  identityNatural F {A = A} {B = B} f = begin
    𝔻 [ identityTrans F B ∘ F→ f ]  ≡⟨⟩
    𝔻 [ 𝟙 𝔻 ∘  F→ f ]              ≡⟨ proj₂ 𝔻.isIdentity ⟩
    F→ f                            ≡⟨ sym (proj₁ 𝔻.isIdentity) ⟩
    𝔻 [ F→ f ∘ 𝟙 𝔻 ]               ≡⟨⟩
    𝔻 [ F→ f ∘ identityTrans F A ]  ∎
    where
      module F = Functor F
      F→ = F.func→
      module 𝔻 = Category 𝔻

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
    proj₁ NT[ (θ , _) ∘ (η , _) ] = T[ θ ∘ η ]
    proj₂ NT[ (θ , θNat) ∘ (η , ηNat) ] {A} {B} f = begin
      𝔻 [ T[ θ ∘ η ] B ∘ F.func→ f ]     ≡⟨⟩
      𝔻 [ 𝔻 [ θ B ∘ η B ] ∘ F.func→ f ] ≡⟨ sym isAssociative ⟩
      𝔻 [ θ B ∘ 𝔻 [ η B ∘ F.func→ f ] ] ≡⟨ cong (λ φ → 𝔻 [ θ B ∘ φ ]) (ηNat f) ⟩
      𝔻 [ θ B ∘ 𝔻 [ G.func→ f ∘ η A ] ] ≡⟨ isAssociative ⟩
      𝔻 [ 𝔻 [ θ B ∘ G.func→ f ] ∘ η A ] ≡⟨ cong (λ φ → 𝔻 [ φ ∘ η A ]) (θNat f) ⟩
      𝔻 [ 𝔻 [ H.func→ f ∘ θ A ] ∘ η A ] ≡⟨ sym isAssociative ⟩
      𝔻 [ H.func→ f ∘ 𝔻 [ θ A ∘ η A ] ] ≡⟨⟩
      𝔻 [ H.func→ f ∘ T[ θ ∘ η ] A ]     ∎
      where
        open Category 𝔻
