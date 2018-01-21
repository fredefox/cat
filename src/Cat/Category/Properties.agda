{-# OPTIONS --allow-unsolved-metas #-}

module Cat.Category.Properties where

open import Cat.Category
open import Cat.Functor
open import Cat.Categories.Sets

module _ {ℓa ℓa' ℓb ℓb'} where
  Exponential : Category ℓa ℓa' → Category ℓb ℓb' → Category {!!} {!!}
  Exponential A B = record
    { Object = {!!}
    ; Arrow = {!!}
    ; 𝟙 = {!!}
    ; _⊕_ = {!!}
    ; isCategory = ?
    }

_⇑_ = Exponential

yoneda : ∀ {ℓ ℓ'} → {ℂ : Category ℓ ℓ'} → Functor ℂ (Sets ⇑ (Opposite ℂ))
yoneda = {!!}
