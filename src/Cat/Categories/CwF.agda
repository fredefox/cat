module Cat.Categories.CwF where

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Categories.Fam

module _ {ℓa ℓb : Level} where
  record CwF : Set (lsuc (ℓa ⊔ ℓb)) where
    -- "A category with families consists of"
    field
      -- "A base category"
      ℂ : Category ℓa ℓb
    module ℂ = Category ℂ
    -- It's objects are called contexts
    Contexts = ℂ.Object
    -- It's arrows are called substitutions
    Substitutions = ℂ.Arrow
    field
      -- A functor T
      T : Functor (opposite ℂ) (Fam ℓa ℓb)
      -- Empty context
      [] : ℂ.Terminal
    private
      module T = Functor T
    Type : (Γ : ℂ.Object) → Set ℓa
    Type Γ = proj₁ (proj₁ (T.omap Γ))

    module _ {Γ : ℂ.Object} {A : Type Γ} where

      -- module _ {A B : Object ℂ} {γ : ℂ [ A , B ]} where
      --   k : Σ (proj₁ (omap T B) → proj₁ (omap T A))
      --     (λ f →
      --     {x : proj₁ (omap T B)} →
      --     proj₂ (omap T B) x → proj₂ (omap T A) (f x))
      --   k = T.fmap γ
      --   k₁ : proj₁ (omap T B) → proj₁ (omap T A)
      --   k₁ = proj₁ k
      --   k₂ : ({x : proj₁ (omap T B)} →
      --     proj₂ (omap T B) x → proj₂ (omap T A) (k₁ x))
      --   k₂ = proj₂ k

      record ContextComprehension : Set (ℓa ⊔ ℓb) where
        field
          Γ&A : ℂ.Object
          proj1 : ℂ [ Γ&A , Γ ]
          -- proj2 : ????

        -- if γ : ℂ [ A , B ]
        -- then T .fmap γ (written T[γ]) interpret substitutions in types and terms respectively.
        -- field
        --   ump : {Δ : ℂ .Object} → (γ : ℂ [ Δ , Γ ])
        --     → (a : {!!}) → {!!}