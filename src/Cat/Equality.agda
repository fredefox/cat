{-# OPTIONS --cubical #-}
-- Defines equality-principles for data-types from the standard library.

module Cat.Equality where

open import Level
open import Cubical

-- _[_≡_] = PathP

module Equality where
  module Data where
    module Product where
      open import Data.Product

      module _ {ℓa ℓb : Level} {A : Set ℓa} {B : A → Set ℓb} {a b : Σ A B}
        (proj₁≡ : (λ _ → A)            [ proj₁ a ≡ proj₁ b ])
        (proj₂≡ : (λ i → B (proj₁≡ i)) [ proj₂ a ≡ proj₂ b ]) where

        Σ≡ : a ≡ b
        proj₁ (Σ≡ i) = proj₁≡ i
        proj₂ (Σ≡ i) = proj₂≡ i

        -- Remark 2.7.1: This theorem:
        --
        --   (x , u) ≡ (x , v) → u ≡ v
        --
        -- does *not* hold! We can only conclude that there *exists* `p : x ≡ x`
        -- such that
        --
        --   p* u ≡ v
        -- thm : isSet A → (∀ {a} → isSet (B a)) → isSet (Σ A B)
        -- thm sA sB (x , y) (x' , y') p q = res
        --   where
        --     x≡x'0 : x ≡ x'
        --     x≡x'0 = λ i → proj₁ (p i)
        --     x≡x'1 : x ≡ x'
        --     x≡x'1 = λ i → proj₁ (q i)
        --     someP : x ≡ x'
        --     someP = {!!}
        --     tricky : {!y!} ≡ y'
        --     tricky = {!!}
        --     -- res' : (λ _ → Σ A B) [ (x , y) ≡ (x' , y') ]
        --     res' : ({!!} , {!!}) ≡ ({!!} , {!!})
        --     res' = {!!}
        --     res : p ≡ q
        --     res i = {!res'!}
