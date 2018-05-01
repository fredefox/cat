{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Wishlist where

open import Level hiding (suc; zero)
open import Cubical
open import Cubical.NType
open import Data.Nat using (_≤′_ ;  ≤′-refl ;  ≤′-step ; zero ; suc)
open import Agda.Builtin.Sigma

open import Cubical.NType.Properties


module _ {ℓ : Level} {A : Set ℓ} where
  ntypeCumulative : ∀ {n m} → n ≤′ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A
  ntypeCumulative {m}         ≤′-refl      lvl = lvl
  ntypeCumulative {n} {suc m} (≤′-step le) lvl = HasLevel+1 ⟨ m ⟩₋₂ (ntypeCumulative le lvl)
