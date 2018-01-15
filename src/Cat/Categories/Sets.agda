{-# OPTIONS --allow-unsolved-metas #-}

module Cat.Categories.Sets where

open import Cubical.PathPrelude
open import Agda.Primitive
open import Data.Product
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

open import Cat.Category
open import Cat.Functor

-- Sets are built-in to Agda. The set of all small sets is called Set.

Fun : {ℓ : Level} → ( T U : Set ℓ ) → Set ℓ
Fun T U = T → U

Sets : {ℓ : Level} → Category {lsuc ℓ} {ℓ}
Sets {ℓ} = record
  { Object = Set ℓ
  ; Arrow = λ T U → Fun {ℓ} T U
  ; 𝟙 = λ x → x
  ; _⊕_  = λ g f x → g ( f x )
  ; assoc = refl
  ; ident = funExt (λ x → refl) , funExt (λ x → refl)
  }

module _ {ℓ ℓ' : Level} {ℂ : Category {ℓ} {ℓ}} where
  private
    C-Obj = Object ℂ
    _+_   = Arrow ℂ

  RepFunctor : Functor ℂ Sets
  RepFunctor =
    record
      { func* = λ A → (B : C-Obj) → Hom {ℂ = ℂ} A B
      ; func→ = λ { {c} {c'} f g → {!HomFromArrow {ℂ = {!!}} c' g!} }
      ; ident = {!!}
      ; distrib = {!!}
      }

Hom0 : {ℓ ℓ' : Level} → {ℂ : Category {ℓ} {ℓ'}} → Category.Object ℂ → Functor ℂ (Sets {ℓ'})
Hom0 {ℂ = ℂ} A = record
  { func* = λ B → ℂ.Arrow A B
  ; func→ = λ f g → f ℂ.⊕ g
  ; ident = funExt λ _ → snd ℂ.ident
  ; distrib = funExt λ x → sym ℂ.assoc
  }
  where
    open module ℂ = Category ℂ

Hom1 : {ℓ ℓ' : Level} → {ℂ : Category {ℓ} {ℓ'}} → Category.Object ℂ → Functor (Opposite ℂ) (Sets {ℓ'})
Hom1 {ℂ = ℂ} B = record
  { func* = λ A → ℂ.Arrow A B
  ; func→ = λ f g → {!!} ℂ.⊕ {!!}
  ; ident = {!!}
  ; distrib = {!!}
  }
  where
    open module ℂ = Category ℂ
