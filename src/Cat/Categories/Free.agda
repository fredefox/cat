{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Categories.Free where

open import Agda.Primitive
open import Cubical hiding (Path ; isSet ; empty)
open import Data.Product

open import Cat.Category

open IsCategory
open Category

-- data Path {ℓ : Level} {A : Set ℓ} : (a b : A) → Set ℓ where
--   emptyPath : {a : A} → Path a a
--   concatenate : {a b c : A} → Path a b → Path b c → Path a b

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  module ℂ = Category ℂ

  -- import Data.List
  -- P : (a b : Object ℂ) → Set (ℓ ⊔ ℓ')
  -- P = {!Data.List.List ?!}
  -- Generalized paths:
  -- data P {ℓ : Level} {A : Set ℓ} (R : A → A → Set ℓ) : (a b : A) → Set ℓ where
  --   e : {a : A} → P R a a
  --   c : {a b c : A} → R a b → P R b c → P R a c

  -- Path's are like lists with directions.
  -- This implementation is specialized to categories.
  data Path : (a b : Object ℂ) → Set (ℓ ⊔ ℓ') where
    empty : {A : Object ℂ} → Path A A
    cons : ∀ {A B C} → ℂ [ B , C ] → Path A B → Path A C

  concatenate : ∀ {A B C : Object ℂ}  → Path B C → Path A B → Path A C
  concatenate empty p = p
  concatenate (cons x q) p = cons x (concatenate q p)

  private
    module _ {A B C D : Object ℂ} where
      p-assoc : {r : Path A B} {q : Path B C} {p : Path C D} → concatenate p (concatenate q r) ≡ concatenate (concatenate p q) r
      p-assoc {r} {q} {p} = {!!}
    module _ {A B : Object ℂ} {p : Path A B} where
      -- postulate
      --   ident-r : concatenate {A} {A} {B} p (lift 𝟙) ≡ p
      --   ident-l : concatenate {A} {B} {B} (lift 𝟙) p ≡ p
    module _ {A B : Object ℂ} where
      isSet : IsSet (Path A B)
      isSet = {!!}
  RawFree : RawCategory ℓ (ℓ ⊔ ℓ')
  RawFree = record
    { Object = Object ℂ
    ; Arrow = Path
    ; 𝟙 = λ {o} → {!lift 𝟙!}
    ; _∘_ = λ {a b c} → {!concatenate {a} {b} {c}!}
    }
  RawIsCategoryFree : IsCategory RawFree
  RawIsCategoryFree = record
    { assoc = {!p-assoc!}
    ; ident = {!ident-r , ident-l!}
    ; arrowIsSet = {!!}
    ; univalent = {!!}
    }
