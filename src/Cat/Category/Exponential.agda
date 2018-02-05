module Cat.Category.Exponential where

open import Agda.Primitive
open import Data.Product
open import Cubical

open import Cat.Category
open import Cat.Category.Product

open Category

module _ {ℓ ℓ'} (ℂ : Category ℓ ℓ') {{hasProducts : HasProducts ℂ}} where
  open HasProducts hasProducts
  open Product hiding (obj)
  private
    _×p_ : (A B : Object ℂ) → Object ℂ
    _×p_ A B = Product.obj (product A B)

  module _ (B C : Object ℂ) where
    IsExponential : (Cᴮ : Object ℂ) → ℂ [ Cᴮ ×p B , C ] → Set (ℓ ⊔ ℓ')
    IsExponential Cᴮ eval = ∀ (A : Object ℂ) (f : ℂ [ A ×p B , C ])
      → ∃![ f~ ] (ℂ [ eval ∘ parallelProduct f~ (Category.𝟙 ℂ)] ≡ f)

    record Exponential : Set (ℓ ⊔ ℓ') where
      field
        -- obj ≡ Cᴮ
        obj : Object ℂ
        eval : ℂ [ obj ×p B , C ]
        {{isExponential}} : IsExponential obj eval
      -- If I make this an instance-argument then the instance resolution
      -- algorithm goes into an infinite loop. Why?
      exponentialsHaveProducts : HasProducts ℂ
      exponentialsHaveProducts = hasProducts
      transpose : (A : Object ℂ) → ℂ [ A ×p B , C ] → ℂ [ A , obj ]
      transpose A f = proj₁ (isExponential A f)

record HasExponentials {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') {{_ : HasProducts ℂ}} : Set (ℓ ⊔ ℓ') where
  field
    exponent : (A B : Object ℂ) → Exponential ℂ A B
