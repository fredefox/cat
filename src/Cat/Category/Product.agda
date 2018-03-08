module Cat.Category.Product where

open import Agda.Primitive
open import Cubical
open import Data.Product as P hiding (_×_ ; proj₁ ; proj₂)

open import Cat.Category hiding (module Propositionality)

open Category

module _ {ℓa ℓb : Level} where
  record RawProduct (ℂ : Category ℓa ℓb) (A B : Object ℂ) : Set (ℓa ⊔ ℓb) where
    no-eta-equality
    field
      obj : Object ℂ
      proj₁ : ℂ [ obj , A ]
      proj₂ : ℂ [ obj , B ]

  record IsProduct (ℂ : Category ℓa ℓb) {A B : Object ℂ} (raw : RawProduct ℂ A B) : Set (ℓa ⊔ ℓb) where
    open RawProduct raw public
    field
      isProduct : ∀ {X : Object ℂ} (x₁ : ℂ [ X , A ]) (x₂ : ℂ [ X , B ])
        → ∃![ x ] (ℂ [ proj₁ ∘ x ] ≡ x₁ P.× ℂ [ proj₂ ∘ x ] ≡ x₂)

    -- | Arrow product
    _P[_×_] : ∀ {X} → (π₁ : ℂ [ X , A ]) (π₂ : ℂ [ X , B ])
      → ℂ [ X , obj ]
    _P[_×_] π₁ π₂ = P.proj₁ (isProduct π₁ π₂)

  record Product (ℂ : Category ℓa ℓb) (A B : Object ℂ) : Set (ℓa ⊔ ℓb) where
    field
      raw        : RawProduct ℂ A B
      isProduct  : IsProduct ℂ {A} {B} raw

    open IsProduct isProduct public

  record HasProducts (ℂ : Category ℓa ℓb) : Set (ℓa ⊔ ℓb) where
    field
      product : ∀ (A B : Object ℂ) → Product ℂ A B

    module _ (A B : Object ℂ) where
      open Product (product A B)
      _×_ : Object ℂ
      _×_ = obj

    -- | Parallel product of arrows
    --
    -- The product mentioned in awodey in Def 6.1 is not the regular product of
    -- arrows. It's a "parallel" product
    module _ {A A' B B' : Object ℂ} where
      open Product
      open Product (product A B) hiding (_P[_×_]) renaming (proj₁ to fst ; proj₂ to snd)
      _|×|_ : ℂ [ A , A' ] → ℂ [ B , B' ] → ℂ [ A × B , A' × B' ]
      a |×| b = product A' B'
        P[ ℂ [ a ∘ fst ]
        ×  ℂ [ b ∘ snd ]
        ]

module Propositionality where
  -- TODO `isProp (Product ...)`
  -- TODO `isProp (HasProducts ...)`
