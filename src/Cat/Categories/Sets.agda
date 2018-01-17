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

Representable : {ℓ ℓ' : Level} → (ℂ : Category {ℓ} {ℓ'}) → Set (ℓ ⊔ lsuc ℓ')
Representable {ℓ' = ℓ'} ℂ = Functor ℂ (Sets {ℓ'})

representable : {ℓ ℓ' : Level} → {ℂ : Category {ℓ} {ℓ'}} → Category.Object ℂ → Representable ℂ
representable {ℂ = ℂ} A = record
  { func* = λ B → ℂ.Arrow A B
  ; func→ = λ f g → f ℂ.⊕ g
  ; ident = funExt λ _ → snd ℂ.ident
  ; distrib = funExt λ x → sym ℂ.assoc
  }
  where
    open module ℂ = Category ℂ

Presheaf : {ℓ ℓ' : Level} → (ℂ : Category {ℓ} {ℓ'}) → Set (ℓ ⊔ lsuc ℓ')
Presheaf {ℓ' = ℓ'} ℂ = Functor (Opposite ℂ) (Sets {ℓ'})

presheaf : {ℓ ℓ' : Level} → {ℂ : Category {ℓ} {ℓ'}} → Category.Object (Opposite ℂ) → Presheaf ℂ
presheaf {ℂ = ℂ} B = record
  { func* = λ A → ℂ.Arrow A B
  ; func→ = λ f g → g ℂ.⊕ f
  ; ident = funExt λ x → fst ℂ.ident
  ; distrib = funExt λ x → ℂ.assoc
  }
  where
    open module ℂ = Category ℂ
