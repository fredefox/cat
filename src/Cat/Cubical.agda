{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Cubical where

open import Agda.Primitive
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product

open import Cat.Category
open import Cat.Functor

-- See chapter 1 for a discussion on how presheaf categories are CwF's.

-- See section 6.8 in Huber's thesis for details on how to implement the
-- categorical version of CTT

module CwF {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  open Category hiding (_∘_)
  open Functor
  open import Function
  open import Cubical

  module _ {ℓa ℓb : Level} where
    private
      Obj = Σ[ A ∈ Set ℓa ] (A → Set ℓb)
      Arr : Obj → Obj → Set (ℓa ⊔ ℓb)
      Arr (A , B) (A' , B') = Σ[ f ∈ (A → A') ] ({x : A} → B x → B' (f x))
      one : {o : Obj} → Arr o o
      proj₁ one = λ x → x
      proj₂ one = λ b → b
      _:⊕:_ : {a b c : Obj} → Arr b c → Arr a b → Arr a c
      (g , g') :⊕: (f , f') = g ∘ f , g' ∘ f'

      module _ {A B C D : Obj} {f : Arr A B} {g : Arr B C} {h : Arr C D} where
        :assoc: : (_:⊕:_ {A} {C} {D} h (_:⊕:_ {A} {B} {C} g f)) ≡ (_:⊕:_ {A} {B} {D} (_:⊕:_ {B} {C} {D} h g) f)
        :assoc: = {!!}

      module _ {A B : Obj} {f : Arr A B} where
        :ident: : (_:⊕:_ {A} {A} {B} f one) ≡ f × (_:⊕:_ {A} {B} {B} one f) ≡ f
        :ident: = {!!}

      instance
        :isCategory: : IsCategory Obj Arr one (λ {a b c} → _:⊕:_ {a} {b} {c})
        :isCategory: = record
          { assoc = λ {A} {B} {C} {D} {f} {g} {h} → :assoc: {A} {B} {C} {D} {f} {g} {h}
          ; ident = {!!}
          }
    Fam : Category (lsuc (ℓa ⊔ ℓb)) (ℓa ⊔ ℓb)
    Fam = record
      { Object = Obj
      ; Arrow = Arr
      ; 𝟙 = one
      ; _∘_ = λ {a b c} → _:⊕:_ {a} {b} {c}
      }

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
