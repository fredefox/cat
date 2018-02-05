{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Categories.Sets where

open import Cubical
open import Agda.Primitive
open import Data.Product
import Function

open import Cat.Category
open import Cat.Functor
open Category

module _ {ℓ : Level} where
  SetsRaw : RawCategory (lsuc ℓ) ℓ
  SetsRaw = record
       { Object = Set ℓ
       ; Arrow = λ T U → T → U
       ; 𝟙 = Function.id
       ; _∘_ = Function._∘′_
       }

  SetsIsCategory : IsCategory SetsRaw
  SetsIsCategory = record
    { assoc = refl
    ; ident = funExt (λ _ → refl) , funExt (λ _ → refl)
    ; arrow-is-set = {!!}
    ; univalent = {!!}
    }

  Sets : Category (lsuc ℓ) ℓ
  Sets = SetsRaw , SetsIsCategory

  private
    module _ {X A B : Set ℓ} (f : X → A) (g : X → B) where
      _&&&_ : (X → A × B)
      _&&&_ x = f x , g x
    module _ {X A B : Set ℓ} (f : X → A) (g : X → B) where
      lem : Sets [ proj₁ ∘ (f &&& g)] ≡ f × Sets [ proj₂ ∘ (f &&& g)] ≡ g
      proj₁ lem = refl
      proj₂ lem = refl
    instance
      isProduct : {A B : Sets .Object} → IsProduct Sets {A} {B} proj₁ proj₂
      isProduct f g = f &&& g , lem f g

    product : (A B : Sets .Object) → Product {ℂ = Sets} A B
    product A B = record { obj = A × B ; proj₁ = proj₁ ; proj₂ = proj₂ ; isProduct = isProduct }

  instance
    SetsHasProducts : HasProducts Sets
    SetsHasProducts = record { product = product }

-- Covariant Presheaf
Representable : {ℓ ℓ' : Level} → (ℂ : Category ℓ ℓ') → Set (ℓ ⊔ lsuc ℓ')
Representable {ℓ' = ℓ'} ℂ = Functor ℂ (Sets {ℓ'})

-- The "co-yoneda" embedding.
representable : ∀ {ℓ ℓ'} {ℂ : Category ℓ ℓ'} → Category.Object ℂ → Representable ℂ
representable {ℂ = ℂ} A = record
  { func* = λ B → ℂ .Arrow A B
  ; func→ = ℂ ._∘_
  ; isFunctor = record
    { ident = funExt λ _ → proj₂ ident
    ; distrib = funExt λ x → sym assoc
    }
  }
  where
    open IsCategory (isCategory ℂ)

-- Contravariant Presheaf
Presheaf : ∀ {ℓ ℓ'} (ℂ : Category ℓ ℓ') → Set (ℓ ⊔ lsuc ℓ')
Presheaf {ℓ' = ℓ'} ℂ = Functor (Opposite ℂ) (Sets {ℓ'})

-- Alternate name: `yoneda`
presheaf : {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} → Category.Object (Opposite ℂ) → Presheaf ℂ
presheaf {ℂ = ℂ} B = record
  { func* = λ A → ℂ .Arrow A B
  ; func→ = λ f g → ℂ ._∘_ g f
  ; isFunctor = record
    { ident = funExt λ x → proj₁ ident
    ; distrib = funExt λ x → assoc
    }
  }
  where
    open IsCategory (isCategory ℂ)
