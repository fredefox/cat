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
  using (⟨-2⟩ ; ⟨-1⟩ ; ⟨0⟩ ; TLevel ; HasLevel)
  public
open import Cubical.NType.Properties
  using
    ( lemPropF ; lemSig ;  lemSigP ; isSetIsProp
    ; propPi ; propHasLevel ; setPi ; propSet)
  public

propIsContr : {ℓ : Level} → {A : Set ℓ} → isProp (isContr A)
propIsContr = propHasLevel ⟨-2⟩

open import Cubical.Sigma using (setSig ; sigPresSet) public

module _ (ℓ : Level) where
  -- FIXME Ask if we can push upstream.
  -- A redefinition of `Cubical.Universe` with an explicit parameter
  _-type : TLevel → Set (lsuc ℓ)
  n -type = Σ (Set ℓ) (HasLevel n)

  hSet : Set (lsuc ℓ)
  hSet = ⟨0⟩ -type

  Prop : Set (lsuc ℓ)
  Prop = ⟨-1⟩ -type

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
