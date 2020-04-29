{-# OPTIONS --cubical #-}
module Cat.Category.CartesianClosed where

open import Agda.Primitive

open import Cat.Category
open import Cat.Category.Product
open import Cat.Category.Exponential

record CartesianClosed {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  field
    {{hasProducts}}     : HasProducts ℂ
    {{hasExponentials}} : HasExponentials ℂ
