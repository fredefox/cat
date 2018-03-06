module Cat.Category.Product where

open import Agda.Primitive
open import Cubical
open import Data.Product as P hiding (_×_)

open import Cat.Category

open Category

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') {A B obj : Object ℂ} where
  IsProduct : (π₁ : ℂ [ obj , A ]) (π₂ : ℂ [ obj , B ]) → Set (ℓ ⊔ ℓ')
  IsProduct π₁ π₂
    = ∀ {X : Object ℂ} (x₁ : ℂ [ X , A ]) (x₂ : ℂ [ X , B ])
    → ∃![ x ] (ℂ [ π₁ ∘ x ] ≡ x₁ P.× ℂ [ π₂ ∘ x ] ≡ x₂)

-- Tip from Andrea; Consider this style for efficiency:
-- record IsProduct {ℓa ℓb : Level} (ℂ : Category ℓa ℓb)
--   {A B obj : Object ℂ} (π₁ : Arrow ℂ obj A) (π₂ : Arrow ℂ obj B) : Set (ℓa ⊔ ℓb) where
--   field
--      issProduct : ∀ {X : Object ℂ} (x₁ : ℂ [ X , A ]) (x₂ : ℂ [ X , B ])
--        → ∃![ x ] (ℂ [ π₁ ∘ x ] ≡ x₁ P.× ℂ [ π₂ ∘ x ] ≡ x₂)

-- open IsProduct

-- TODO `isProp (Product ...)`
-- TODO `isProp (HasProducts ...)`
record Product {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} (A B : Object ℂ) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    obj : Object ℂ
    proj₁ : ℂ [ obj , A ]
    proj₂ : ℂ [ obj , B ]
    {{isProduct}} : IsProduct ℂ proj₁ proj₂

  -- | Arrow product
  _P[_×_] : ∀ {X} → (π₁ : ℂ [ X , A ]) (π₂ : ℂ [ X , B ])
    → ℂ [ X , obj ]
  _P[_×_] π₁ π₂ = proj₁ (isProduct π₁ π₂)

record HasProducts {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  field
    product : ∀ (A B : Object ℂ) → Product {ℂ = ℂ} A B

  open Product hiding (obj)

  module _ (A B : Object ℂ) where
    open Product (product A B)
    _×_ : Object ℂ
    _×_ = obj

  -- | Parallel product of arrows
  --
  -- The product mentioned in awodey in Def 6.1 is not the regular product of
  -- arrows. It's a "parallel" product
  module _ {A A' B B' : Object ℂ} where
    open Product (product A B) hiding (_P[_×_]) renaming (proj₁ to fst ; proj₂ to snd)
    _|×|_ : ℂ [ A , A' ] → ℂ [ B , B' ] → ℂ [ A × B , A' × B' ]
    a |×| b = product A' B'
      P[ ℂ [ a ∘ fst ]
      ×  ℂ [ b ∘ snd ]
      ]
