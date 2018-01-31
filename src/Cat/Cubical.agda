{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Cubical where

open import Agda.Primitive
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Function
open import Cubical

open import Cat.Category
open import Cat.Functor
open import Cat.Categories.Fam

-- See chapter 1 for a discussion on how presheaf categories are CwF's.

-- See section 6.8 in Huber's thesis for details on how to implement the
-- categorical version of CTT

open Category hiding (_∘_)
open Functor

module CwF {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  Contexts = ℂ .Object
  Substitutions = ℂ .Arrow

  record CwF : Set {!ℓa ⊔ ℓb!} where
    field
      Terms : Functor (Opposite ℂ) Fam

module _ {ℓ ℓ' : Level} (Ns : Set ℓ) where
  -- Ns is the "namespace"
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
  ℂ : Category ℓ ℓ -- ℓo (lsuc lzero ⊔ ℓo)
  ℂ = record
    -- { Object = FiniteDecidableSubset
    { Object = Ns → Bool
    ; Arrow = Mor
    ; 𝟙 = {!!}
    ; _∘_ = {!!}
    ; isCategory = {!!}
    }
