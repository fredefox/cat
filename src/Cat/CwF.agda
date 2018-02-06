module Cat.CwF where

open import Agda.Primitive
open import Data.Product

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Categories.Fam

open Category
open Functor

module _ {ℓa ℓb : Level} where
  record CwF : Set (lsuc (ℓa ⊔ ℓb)) where
    -- "A category with families consists of"
    field
      -- "A base category"
      ℂ : Category ℓa ℓb
    -- It's objects are called contexts
    Contexts = Object ℂ
    -- It's arrows are called substitutions
    Substitutions = Arrow ℂ
    field
      -- A functor T
      T : Functor (Opposite ℂ) (Fam ℓa ℓb)
      -- Empty context
      [] : Terminal ℂ
    private
      module T = Functor T
    Type : (Γ : Object ℂ) → Set ℓa
    Type Γ = proj₁ (T.func* Γ)

    module _ {Γ : Object ℂ} {A : Type Γ} where

      module _ {A B : Object ℂ} {γ : ℂ [ A , B ]} where
        k : Σ (proj₁ (func* T B) → proj₁ (func* T A))
          (λ f →
          {x : proj₁ (func* T B)} →
          proj₂ (func* T B) x → proj₂ (func* T A) (f x))
        k = T.func→ γ
        k₁ : proj₁ (func* T B) → proj₁ (func* T A)
        k₁ = proj₁ k
        k₂ : ({x : proj₁ (func* T B)} →
          proj₂ (func* T B) x → proj₂ (func* T A) (k₁ x))
        k₂ = proj₂ k

      record ContextComprehension : Set (ℓa ⊔ ℓb) where
        field
          Γ&A : Object ℂ
          proj1 : ℂ [ Γ&A , Γ ]
          -- proj2 : ????

        -- if γ : ℂ [ A , B ]
        -- then T .func→ γ (written T[γ]) interpret substitutions in types and terms respectively.
        -- field
        --   ump : {Δ : ℂ .Object} → (γ : ℂ [ Δ , Γ ])
        --     → (a : {!!}) → {!!}
