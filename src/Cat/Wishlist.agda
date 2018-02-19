module Cat.Wishlist where

open import Level
open import Cubical.NType
open import Data.Nat using (_≤_ ; z≤n ; s≤s)

postulate ntypeCommulative : ∀ {ℓ n m} {A : Set ℓ} → n ≤ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A

-- This follows from [HoTT-book: §7.1.10]
-- Andrea says the proof is in `cubical` but I can't find it.
postulate isSetIsProp : {ℓ : Level} → {A : Set ℓ} → isProp (isSet A)
