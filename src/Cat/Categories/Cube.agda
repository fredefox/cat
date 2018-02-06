{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Categories.Cube where

open import Level
open import Data.Bool hiding (T)
open import Data.Sum hiding ([_,_])
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Cubical
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Equality
open Equality.Data.Product

-- See chapter 1 for a discussion on how presheaf categories are CwF's.

-- See section 6.8 in Huber's thesis for details on how to implement the
-- categorical version of CTT

open Category hiding (_∘_)
open Functor

module _ {ℓ ℓ' : Level} (Ns : Set ℓ) where
  -- Ns is the "namespace"
  ℓo = (suc zero ⊔ ℓ)

  FiniteDecidableSubset : Set ℓ
  FiniteDecidableSubset = Ns → Dec ⊤

  isTrue : Bool → Set
  isTrue false = ⊥
  isTrue true = ⊤

  elmsof : FiniteDecidableSubset → Set ℓ
  elmsof P = Σ Ns (λ σ → True (P σ)) -- (σ : Ns) → isTrue (P σ)

  𝟚 : Set
  𝟚 = Bool

  module _ (I J : FiniteDecidableSubset) where
    private
      Hom' : Set ℓ
      Hom' = elmsof I → elmsof J ⊎ 𝟚
      isInl : {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} → A ⊎ B → Set
      isInl (inj₁ _) = ⊤
      isInl (inj₂ _) = ⊥

      Def : Set ℓ
      Def = (f : Hom') → Σ (elmsof I) (λ i → isInl (f i))

      rules : Hom' → Set ℓ
      rules f = (i j : elmsof I)
        → case (f i) of λ
          { (inj₁ (fi , _)) → case (f j) of λ
            { (inj₁ (fj , _)) → fi ≡ fj → i ≡ j
            ; (inj₂ _) → Lift ⊤
            }
          ; (inj₂ _) → Lift ⊤
          }

    Hom = Σ Hom' rules

  module Raw = RawCategory
  -- The category of names and substitutions
  Rawℂ : RawCategory ℓ ℓ -- ℓo (lsuc lzero ⊔ ℓo)
  Raw.Object Rawℂ = FiniteDecidableSubset
  Raw.Arrow Rawℂ = Hom
  Raw.𝟙 Rawℂ {o} = inj₁ , λ { (i , ii) (j , jj) eq → Σ≡ eq {!refl!} }
  Raw._∘_ Rawℂ = {!!}

  postulate IsCategoryℂ : IsCategory Rawℂ

  ℂ : Category ℓ ℓ
  raw ℂ = Rawℂ
  isCategory ℂ = IsCategoryℂ
