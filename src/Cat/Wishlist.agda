module Cat.Wishlist where

open import Level
open import Cubical.NType
open import Data.Nat using (_≤_ ; z≤n ; s≤s)

postulate ntypeCommulative : ∀ {ℓ n m} {A : Set ℓ} → n ≤ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A

module _ {ℓ : Level} {A : Set ℓ} where
  -- This is §7.1.10 in [HoTT]. Andrea says the proof is in `cubical` but I
  -- can't find it.
  postulate propHasLevel : ∀ n → isProp (HasLevel n A)

  isSetIsProp : isProp (isSet A)
  isSetIsProp = propHasLevel (S (S ⟨-2⟩))
