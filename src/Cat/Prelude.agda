-- | Custom prelude for this module
module Cat.Prelude where

open import Agda.Primitive public
-- FIXME Use:
-- open import Agda.Builtin.Sigma public
-- Rather than
open import Data.Product public
  renaming (∃! to ∃!≈)

-- TODO Import Data.Function under appropriate names.

open import Cubical public
-- FIXME rename `gradLemma` to `fromIsomorphism` - perhaps just use wrapper
-- module.
open import Cubical.GradLemma
  using (gradLemma)
  public
open import Cubical.NType
  using (⟨-2⟩)
  public
open import Cubical.NType.Properties
  using
    ( lemPropF ; lemSig ;  lemSigP ; isSetIsProp
    ; propPi ; propHasLevel ; setPi ; propSet)
  public
open import Cubical.Sigma using (setSig) public
open import Cubical.Universe using (hSet) public

-----------------
-- * Utilities --
-----------------

-- | Unique existensials.
∃! : ∀ {a b} {A : Set a}
  → (A → Set b) → Set (a ⊔ b)
∃! = ∃!≈ _≡_

∃!-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃!-syntax = ∃

syntax ∃!-syntax (λ x → B) = ∃![ x ] B

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : A → Set ℓb} {a b : Σ A B}
  (proj₁≡ : (λ _ → A)            [ proj₁ a ≡ proj₁ b ])
  (proj₂≡ : (λ i → B (proj₁≡ i)) [ proj₂ a ≡ proj₂ b ]) where

  Σ≡ : a ≡ b
  proj₁ (Σ≡ i) = proj₁≡ i
  proj₂ (Σ≡ i) = proj₂≡ i
