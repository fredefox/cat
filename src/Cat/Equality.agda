-- Defines equality-principles for data-types from the standard library.

module Cat.Equality where

open import Level
open import Cubical

-- _[_≡_] = PathP

module Equality where
  module Data where
    module Product where
      open import Data.Product public

      module _ {ℓa ℓb : Level} {A : Set ℓa} {B : A → Set ℓb} {a b : Σ A B}
        (proj₁≡ : (λ _ → A)            [ proj₁ a ≡ proj₁ b ])
        (proj₂≡ : (λ i → B (proj₁≡ i)) [ proj₂ a ≡ proj₂ b ]) where

        Σ≡ : a ≡ b
        proj₁ (Σ≡ i) = proj₁≡ i
        proj₂ (Σ≡ i) = proj₂≡ i
