module Cat.Category.Exponential where

open import Agda.Primitive
open import Data.Product hiding (_×_)
open import Cubical

open import Cat.Category
open import Cat.Category.Product

module _ {ℓ ℓ'} (ℂ : Category ℓ ℓ') {{hasProducts : HasProducts ℂ}} where
  open Category ℂ
  open HasProducts hasProducts public

  module _ (B C : Object) where
    record IsExponential'
      (Cᴮ : Object)
      (eval : ℂ [ Cᴮ × B , C ]) : Set (ℓ ⊔ ℓ') where
      field
        uniq
          : ∀ (A : Object) (f : ℂ [ A × B , C ])
          → ∃![ f~ ] (ℂ [ eval ∘ f~ |×| Category.𝟙 ℂ ] ≡ f)

    IsExponential : (Cᴮ : Object) → ℂ [ Cᴮ × B , C ] → Set (ℓ ⊔ ℓ')
    IsExponential Cᴮ eval = ∀ (A : Object) (f : ℂ [ A × B , C ])
      → ∃![ f~ ] (ℂ [ eval ∘ f~ |×| Category.𝟙 ℂ ] ≡ f)

    record Exponential : Set (ℓ ⊔ ℓ') where
      field
        -- obj ≡ Cᴮ
        obj : Object
        eval : ℂ [ obj × B , C ]
        {{isExponential}} : IsExponential obj eval

      transpose : (A : Object) → ℂ [ A × B , C ] → ℂ [ A , obj ]
      transpose A f = proj₁ (isExponential A f)

record HasExponentials {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') {{_ : HasProducts ℂ}} : Set (ℓ ⊔ ℓ') where
  open Category ℂ
  open Exponential public
  field
    exponent : (A B : Object) → Exponential ℂ A B

  _⇑_ : (A B : Object) → Object
  A ⇑ B = (exponent A B) .obj
