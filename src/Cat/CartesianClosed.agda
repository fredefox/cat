module Cat.CartesianClosed where

open import Agda.Primitive

open import Cat.Category
open import Cat.Product
open import Cat.Exponential

record CartesianClosed {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  field
    {{hasProducts}}     : HasProducts ℂ
    {{hasExponentials}} : HasExponentials ℂ
