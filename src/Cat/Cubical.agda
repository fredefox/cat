{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Cubical where

open import Agda.Primitive
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Cat.Category

module _ {ℓ ℓ' : Level} (Ns : Set ℓ) where
  -- Σ is the "namespace"
  ℓo = (lsuc lzero ⊔ ℓ)

  FiniteDecidableSubset : Set ℓ
  FiniteDecidableSubset = Ns → Bool

  isTrue : Bool → Set
  isTrue false = ⊥
  isTrue true = ⊤

  elmsof : (Ns → Bool) → Set ℓ
  elmsof P = (σ : Ns) → isTrue (P σ)

  𝟚 : Set
  𝟚 = Bool

  module _ (I J : FiniteDecidableSubset) where
    private
      themap : Set {!!}
      themap = elmsof I → elmsof J ⊎ 𝟚
      rules : (elmsof I → elmsof J ⊎ 𝟚) → Set
      rules f = (i j : elmsof I) → {!!}

    Mor = Σ themap rules

  -- The category of names and substitutions
  ℂ : Category -- {ℓo} {lsuc lzero ⊔ ℓo}
  ℂ = record
    -- { Object = FiniteDecidableSubset
    { Object = Ns → Bool
    ; Arrow = Mor
    ; 𝟙 = {!!}
    ; _⊕_ = {!!}
    ; assoc = {!!}
    ; ident = {!!}
    }
