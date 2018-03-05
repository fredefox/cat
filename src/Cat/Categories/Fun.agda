{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Fun where

open import Agda.Primitive
open import Data.Product

open import Data.Nat using (_≤_ ; z≤n ; s≤s)
module Nat = Data.Nat
open import Data.Product

open import Cubical
open import Cubical.Sigma
open import Cubical.NType.Properties

open import Cat.Category
open import Cat.Category.Functor hiding (identity)
open import Cat.Category.NaturalTransformation
open import Cat.Wishlist

open import Cat.Equality
import Cat.Category.NaturalTransformation
open Equality.Data.Product

module Fun {ℓc ℓc' ℓd ℓd' : Level} (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  open Category using (Object ; 𝟙)
  module NT = NaturalTransformation ℂ 𝔻
  open NT public

  private
    module 𝔻 = Category 𝔻

  module _ {F G : Functor ℂ 𝔻} where
    transformationIsSet : isSet (Transformation F G)
    transformationIsSet _ _ p q i j C = 𝔻.arrowsAreSets _ _ (λ l → p l C)   (λ l → q l C) i j

    naturalIsProp : (θ : Transformation F G) → isProp (Natural F G θ)
    naturalIsProp θ θNat θNat' = lem
      where
        lem : (λ _ → Natural F G θ) [ (λ f → θNat f) ≡ (λ f → θNat' f) ]
        lem = λ i f → 𝔻.arrowsAreSets _ _ (θNat f) (θNat' f) i

    naturalTransformationIsSets : isSet (NaturalTransformation F G)
    naturalTransformationIsSets = sigPresSet transformationIsSet
      λ θ → ntypeCommulative
        (s≤s {n = Nat.suc Nat.zero} z≤n)
        (naturalIsProp θ)

  private
    module _ {A B C D : Functor ℂ 𝔻} {θ' : NaturalTransformation A B}
      {η' : NaturalTransformation B C} {ζ' : NaturalTransformation C D} where
      θ = proj₁ θ'
      η = proj₁ η'
      ζ = proj₁ ζ'
      θNat = proj₂ θ'
      ηNat = proj₂ η'
      ζNat = proj₂ ζ'
      L : NaturalTransformation A D
      L = (NT[_∘_] {A} {C} {D} ζ' (NT[_∘_] {A} {B} {C} η' θ'))
      R : NaturalTransformation A D
      R = (NT[_∘_] {A} {B} {D} (NT[_∘_] {B} {C} {D} ζ' η') θ')
      _g⊕f_ = NT[_∘_] {A} {B} {C}
      _h⊕g_ = NT[_∘_] {B} {C} {D}
      isAssociative : L ≡ R
      isAssociative = lemSig (naturalIsProp {F = A} {D})
        L R (funExt (λ x → 𝔻.isAssociative))

  private
    module _ {A B : Functor ℂ 𝔻} {f : NaturalTransformation A B} where
      allNatural = naturalIsProp {F = A} {B}
      f' = proj₁ f
      eq-r : ∀ C → (𝔻 [ f' C ∘ identityTrans A C ]) ≡ f' C
      eq-r C = begin
        𝔻 [ f' C ∘ identityTrans A C ] ≡⟨⟩
        𝔻 [ f' C ∘ 𝔻.𝟙 ]  ≡⟨ proj₁ 𝔻.isIdentity ⟩
        f' C ∎
      eq-l : ∀ C → (𝔻 [ identityTrans B C ∘ f' C ]) ≡ f' C
      eq-l C = proj₂ 𝔻.isIdentity
      ident-r : (NT[_∘_] {A} {A} {B} f (NT.identity A)) ≡ f
      ident-r = lemSig allNatural _ _ (funExt eq-r)
      ident-l : (NT[_∘_] {A} {B} {B} (NT.identity B) f) ≡ f
      ident-l = lemSig allNatural _ _ (funExt eq-l)
      isIdentity
        : (NT[_∘_] {A} {A} {B} f (NT.identity A)) ≡ f
        × (NT[_∘_] {A} {B} {B} (NT.identity B) f) ≡ f
      isIdentity = ident-r , ident-l
  -- Functor categories. Objects are functors, arrows are natural transformations.
  RawFun : RawCategory (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  RawFun = record
    { Object = Functor ℂ 𝔻
    ; Arrow = NaturalTransformation
    ; 𝟙 = λ {F} → NT.identity F
    ; _∘_ = λ {F G H} → NT[_∘_] {F} {G} {H}
    }

  instance
    isCategory : IsCategory RawFun
    isCategory = record
      { isAssociative = λ {A B C D} → isAssociative {A} {B} {C} {D}
      ; isIdentity = λ {A B} → isIdentity {A} {B}
      ; arrowsAreSets = λ {F} {G} → naturalTransformationIsSets {F} {G}
      ; univalent = {!!}
      }

  Fun : Category (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  Category.raw Fun = RawFun

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    open import Cat.Categories.Sets
    open NaturalTransformation (opposite ℂ) (𝓢𝓮𝓽 ℓ')

    -- Restrict the functors to Presheafs.
    rawPresh : RawCategory (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
    rawPresh = record
      { Object = Presheaf ℂ
      ; Arrow = NaturalTransformation
      ; 𝟙 = λ {F} → identity F
      ; _∘_ = λ {F G H} → NT[_∘_] {F = F} {G = G} {H = H}
      }
    instance
      isCategory : IsCategory rawPresh
      isCategory = Fun.isCategory _ _

  Presh : Category (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  Category.raw        Presh = rawPresh
  Category.isCategory Presh = isCategory
