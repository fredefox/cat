{-# OPTIONS --allow-unsolved-metas #-}

module Cat.Categories.Sets where

open import Cubical.PathPrelude
open import Agda.Primitive
open import Data.Product
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

open import Cat.Category
open import Cat.Functor
open Category

Sets : {ℓ : Level} → Category (lsuc ℓ) ℓ
Sets {ℓ} = record
  { Object = Set ℓ
  ; Arrow = λ T U → T → U
  ; 𝟙 = id
  ; _⊕_ = _∘′_
  ; isCategory = record { assoc = refl ; ident = funExt (λ _ → refl) , funExt (λ _ → refl) }
  }
  where
    open import Function

-- Covariant Presheaf
Representable : {ℓ ℓ' : Level} → (ℂ : Category ℓ ℓ') → Set (ℓ ⊔ lsuc ℓ')
Representable {ℓ' = ℓ'} ℂ = Functor ℂ (Sets {ℓ'})

-- The "co-yoneda" embedding.
representable : ∀ {ℓ ℓ'} {ℂ : Category ℓ ℓ'} → Category.Object ℂ → Representable ℂ
representable {ℂ = ℂ} A = record
  { func* = λ B → ℂ .Arrow A B
  ; func→ = ℂ ._⊕_
  ; ident = funExt λ _ → snd ident
  ; distrib = funExt λ x → sym assoc
  }
  where
    open IsCategory (ℂ .isCategory)

-- Contravariant Presheaf
Presheaf : ∀ {ℓ ℓ'} (ℂ : Category ℓ ℓ') → Set (ℓ ⊔ lsuc ℓ')
Presheaf {ℓ' = ℓ'} ℂ = Functor (Opposite ℂ) (Sets {ℓ'})

-- Alternate name: `yoneda`
presheaf : {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} → Category.Object (Opposite ℂ) → Presheaf ℂ
presheaf {ℂ = ℂ} B = record
  { func* = λ A → ℂ .Arrow A B
  ; func→ = λ f g → ℂ ._⊕_ g f
  ; ident = funExt λ x → fst ident
  ; distrib = funExt λ x → assoc
  }
  where
    open IsCategory (ℂ .isCategory)
