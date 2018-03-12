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
    _⇑_ = CatExponential.object

    module _ {A B : ℂ.Object} (f : ℂ [ A , B ]) where
      fmap : Transformation (prshf A) (prshf B)
      fmap C x = ℂ [ f ∘ x ]

      fmapNatural : Natural (prshf A) (prshf B) fmap
      fmapNatural g = funExt λ _ → ℂ.isAssociative

      fmapNT : NaturalTransformation (prshf A) (prshf B)
      fmapNT = fmap , fmapNatural

    rawYoneda : RawFunctor ℂ Fun
    RawFunctor.omap rawYoneda = prshf
    RawFunctor.fmap rawYoneda = fmapNT
    open RawFunctor rawYoneda hiding (fmap)

    isIdentity : IsIdentity
    isIdentity {c} = lemSig (naturalIsProp {F = prshf c} {prshf c}) _ _ eq
      where
      eq : (λ C x → ℂ [ ℂ.𝟙 ∘ x ]) ≡ identityTrans (prshf c)
      eq = funExt λ A → funExt λ B → proj₂ ℂ.isIdentity

    isDistributive : IsDistributive
    isDistributive {A} {B} {C} {f = f} {g}
      = lemSig (propIsNatural (prshf A) (prshf C)) _ _ eq
      where
      T[_∘_]' = T[_∘_] {F = prshf A} {prshf B} {prshf C}
      eqq : (X : ℂ.Object) → (x : ℂ [ X , A ])
        → fmap (ℂ [ g ∘ f ]) X x ≡ T[ fmap g ∘ fmap f ]' X x
      eqq X x = begin
        fmap (ℂ [ g ∘ f ]) X x ≡⟨⟩
        ℂ [ ℂ [ g ∘ f ] ∘ x ] ≡⟨ sym ℂ.isAssociative ⟩
        ℂ [ g ∘ ℂ [ f ∘ x ] ] ≡⟨⟩
        ℂ [ g ∘ fmap f X x ]  ≡⟨⟩
        T[ fmap g ∘ fmap f ]' X x ∎
      eq : fmap (ℂ [ g ∘ f ]) ≡ T[ fmap g ∘ fmap f ]'
      eq = begin
        fmap (ℂ [ g ∘ f ])    ≡⟨ funExt (λ X → funExt λ α → eqq X α) ⟩
        T[ fmap g ∘ fmap f ]' ∎

    instance
      isFunctor : IsFunctor ℂ Fun rawYoneda
      IsFunctor.isIdentity     isFunctor = isIdentity
      IsFunctor.isDistributive isFunctor = isDistributive

  yoneda : Functor ℂ Fun
  Functor.raw yoneda = rawYoneda
  Functor.isFunctor yoneda = isFunctor
