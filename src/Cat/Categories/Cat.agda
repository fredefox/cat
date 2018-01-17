{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cat.Categories.Cat where

open import Agda.Primitive
open import Cubical
open import Function
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

open import Cat.Category
open import Cat.Functor

-- The category of categories
module _ {ℓ ℓ' : Level} where
  private
    _⊛_ = functor-comp
    module _ {A B C D : Category {ℓ} {ℓ'}} {f : Functor A B} {g : Functor B C} {h : Functor C D} where
      assc : h ⊛ (g ⊛ f) ≡ (h ⊛ g) ⊛ f
      assc = {!!}

    module _ {A B : Category {ℓ} {ℓ'}} where
      lift-eq : (f g : Functor A B)
        → (eq* : Functor.func* f ≡ Functor.func* g)
        -- TODO: Must transport here using the equality from above.
        -- Reason:
        --   func→  : Arrow A dom cod → Arrow B (func* dom) (func* cod)
        --   func→₁ : Arrow A dom cod → Arrow B (func*₁ dom) (func*₁ cod)
        -- In other words, func→ and func→₁ does not have the same type.
  --      → Functor.func→ f ≡ Functor.func→ g
  --      → Functor.ident f ≡ Functor.ident g
  --       → Functor.distrib f ≡ Functor.distrib g
        → f ≡ g
      lift-eq f g eq* x = {!!}

    module _ {A B : Category {ℓ} {ℓ'}} {f : Functor A B} where
      idHere = identity {ℓ} {ℓ'} {A}
      lem : (Functor.func* f) ∘ (Functor.func* idHere) ≡ Functor.func* f
      lem = refl
      ident-r : f ⊛ identity ≡ f
      ident-r = lift-eq (f ⊛ identity) f refl
      ident-l : identity ⊛ f ≡ f
      ident-l = {!!}

  CatCat : Category {lsuc (ℓ ⊔ ℓ')} {ℓ ⊔ ℓ'}
  CatCat =
    record
      { Object = Category {ℓ} {ℓ'}
      ; Arrow = Functor
      ; 𝟙 = identity
      ; _⊕_ = functor-comp
      ; assoc = {!!}
      ; ident = ident-r , ident-l
      }
