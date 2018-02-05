module Cat.Product where

open import Agda.Primitive
open import Data.Product
open import Cubical

open import Cat.Category

open Category

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') {A B obj : Object ℂ} where
  IsProduct : (π₁ : ℂ [ obj , A ]) (π₂ : ℂ [ obj , B ]) → Set (ℓ ⊔ ℓ')
  IsProduct π₁ π₂
    = ∀ {X : Object ℂ} (x₁ : ℂ [ X , A ]) (x₂ : ℂ [ X , B ])
    → ∃![ x ] (ℂ [ π₁ ∘ x ] ≡ x₁ × ℂ [ π₂ ∘ x ] ≡ x₂)

-- Tip from Andrea; Consider this style for efficiency:
-- record IsProduct {ℓ ℓ' : Level} (ℂ : Category {ℓ} {ℓ'})
--   {A B obj : Object ℂ} (π₁ : Arrow ℂ obj A) (π₂ : Arrow ℂ obj B) : Set (ℓ ⊔ ℓ') where
--   field
--      isProduct : ∀ {X : ℂ .Object} (x₁ : ℂ .Arrow X A) (x₂ : ℂ .Arrow X B)
--        → ∃![ x ] (ℂ ._⊕_ π₁ x ≡ x₁ × ℂ. _⊕_ π₂ x ≡ x₂)

record Product {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} (A B : Object ℂ) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    obj : Object ℂ
    proj₁ : ℂ [ obj , A ]
    proj₂ : ℂ [ obj , B ]
    {{isProduct}} : IsProduct ℂ proj₁ proj₂

  arrowProduct : ∀ {X} → (π₁ : ℂ [ X , A ]) (π₂ : ℂ [ X , B ])
    → ℂ [ X , obj ]
  arrowProduct π₁ π₂ = proj₁ (isProduct π₁ π₂)

record HasProducts {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  field
    product : ∀ (A B : Object ℂ) → Product {ℂ = ℂ} A B

  open Product

  objectProduct : (A B : Object ℂ) → Object ℂ
  objectProduct A B = Product.obj (product A B)
  -- The product mentioned in awodey in Def 6.1 is not the regular product of arrows.
  -- It's a "parallel" product
  parallelProduct : {A A' B B' : Object ℂ} → ℂ [ A , A' ] → ℂ [ B , B' ]
    → ℂ [ objectProduct A B , objectProduct A' B' ]
  parallelProduct {A = A} {A' = A'} {B = B} {B' = B'} a b = arrowProduct (product A' B')
    (ℂ [ a ∘ (product A B) .proj₁ ])
    (ℂ [ b ∘ (product A B) .proj₂ ])
