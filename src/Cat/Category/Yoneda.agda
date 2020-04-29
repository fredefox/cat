{-# OPTIONS --cubical #-}

module Cat.Category.Yoneda where

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.NaturalTransformation
  renaming (module Properties to F)
  using ()
open import Cat.Categories.Opposite
open import Cat.Categories.Sets hiding (presheaf)
open import Cat.Categories.Fun using (module Fun)

-- There is no (small) category of categories. So we won't use _⇑_ from
-- `HasExponential`
--
--     open HasExponentials (Cat.hasExponentials ℓ unprovable) using (_⇑_)
--
-- In stead we'll use an ad-hoc definition -- which is definitionally equivalent
-- to that other one - even without mentioning the category of categories.
_⇑_ : {ℓ : Level} → Category ℓ ℓ → Category ℓ ℓ → Category ℓ ℓ
_⇑_ = Fun.Fun

module _ {ℓ : Level} {ℂ : Category ℓ ℓ} where
  private
    𝓢 = Sets ℓ
    open Fun (opposite ℂ) 𝓢

    module ℂ = Category ℂ

    presheaf : ℂ.Object → Presheaf ℂ
    presheaf = Cat.Categories.Sets.presheaf ℂ

    module _ {A B : ℂ.Object} (f : ℂ [ A , B ]) where
      fmap : Transformation (presheaf A) (presheaf B)
      fmap C x = ℂ [ f ∘ x ]

      fmapNatural : Natural (presheaf A) (presheaf B) fmap
      fmapNatural g = funExt λ _ → ℂ.isAssociative

      fmapNT : NaturalTransformation (presheaf A) (presheaf B)
      fmapNT = fmap , fmapNatural

    rawYoneda : RawFunctor ℂ Fun
    RawFunctor.omap rawYoneda = presheaf
    RawFunctor.fmap rawYoneda = fmapNT

    open RawFunctor rawYoneda hiding (fmap)

    isIdentity : IsIdentity
    isIdentity {c} = lemSig prp eq
      where
      eq : (λ C x → ℂ [ ℂ.identity ∘ x ]) ≡ identityTrans (presheaf c)
      eq = funExt λ A → funExt λ B → ℂ.leftIdentity
      prp = F.naturalIsProp _ _ {F = presheaf c} {presheaf c}

    isDistributive : IsDistributive
    isDistributive {A} {B} {C} {f = f} {g}
      = lemSig (propIsNatural (presheaf A) (presheaf C)) eq
      where
      T[_∘_]' = T[_∘_] {F = presheaf A} {presheaf B} {presheaf C}
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
  Functor.raw       yoneda = rawYoneda
  Functor.isFunctor yoneda = isFunctor
