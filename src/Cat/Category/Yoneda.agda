{-# OPTIONS --allow-unsolved-metas --cubical #-}

module Cat.Category.Yoneda where

open import Agda.Primitive
open import Data.Product
open import Cubical
open import Cubical.NType.Properties

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Equality

open import Cat.Categories.Fun
open import Cat.Categories.Sets
open import Cat.Categories.Cat

module _ {ℓ : Level} {ℂ : Category ℓ ℓ} where
  private
    𝓢 = Sets ℓ
    open Fun (opposite ℂ) 𝓢
    prshf = presheaf ℂ
    module ℂ = Category ℂ

    -- There is no (small) category of categories. So we won't use _⇑_ from
    -- `HasExponential`
    --
    --     open HasExponentials (Cat.hasExponentials ℓ unprovable) using (_⇑_)
    --
    -- In stead we'll use an ad-hoc definition -- which is definitionally
    -- equivalent to that other one.
    _⇑_ = CatExponential.prodObj

    module _ {A B : ℂ.Object} (f : ℂ [ A , B ]) where
      :func→: : NaturalTransformation (prshf A) (prshf B)
      :func→: = (λ C x → ℂ [ f ∘ x ]) , λ f₁ → funExt λ _ → ℂ.isAssociative

    rawYoneda : RawFunctor ℂ Fun
    RawFunctor.func* rawYoneda = prshf
    RawFunctor.func→ rawYoneda = :func→:
    open RawFunctor rawYoneda

    isIdentity : IsIdentity
    isIdentity {c} = lemSig (naturalIsProp {F = prshf c} {prshf c}) _ _ eq
      where
      eq : (λ C x → ℂ [ ℂ.𝟙 ∘ x ]) ≡ identityTrans (prshf c)
      eq = funExt λ A → funExt λ B → proj₂ ℂ.isIdentity

    isDistributive : IsDistributive
    isDistributive = {!!}

    instance
      isFunctor : IsFunctor ℂ Fun rawYoneda
      IsFunctor.isIdentity     isFunctor = isIdentity
      IsFunctor.isDistributive isFunctor = isDistributive

  yoneda : Functor ℂ Fun
  Functor.raw yoneda = rawYoneda
  Functor.isFunctor yoneda = isFunctor
