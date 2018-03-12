module Cat.Wishlist where

open import Level
open import Cubical.NType
open import Data.Nat using (_≤_ ; z≤n ; s≤s)

open import Cubical.NType.Properties

postulate ntypeCommulative : ∀ {ℓ n m} {A : Set ℓ} → n ≤ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A
