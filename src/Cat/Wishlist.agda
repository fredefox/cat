module Cat.Wishlist where

open import Level
open import Cubical.NType
open import Data.Nat using (_≤_ ; z≤n ; s≤s)

open import Cubical.NType.Properties public using (propHasLevel)

postulate ntypeCommulative : ∀ {ℓ n m} {A : Set ℓ} → n ≤ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A

module _ {ℓ : Level} {A : Set ℓ} where
  isSetIsProp : isProp (isSet A)
  isSetIsProp = propHasLevel (S (S ⟨-2⟩))

  propIsProp : isProp (isProp A)
  propIsProp = propHasLevel (S ⟨-2⟩)
