module Category.Sets where

open import Cubical.PathPrelude
open import Agda.Primitive
open import Category

-- Sets are built-in to Agda. The set of all small sets is called Set.

Fun : {ℓ : Level} → ( T U : Set ℓ ) → Set ℓ
Fun T U = T → U

Sets : {ℓ : Level} → Category {lsuc ℓ} {ℓ}
Sets {ℓ} = record
  { Object = Set ℓ
  ; Arrow = λ T U → Fun {ℓ} T U
  ; 𝟙 = λ x → x
  ; _⊕_  = λ g f x → g ( f x )
  ; assoc = refl
  ; ident = funExt (λ x → refl) , funExt (λ x → refl)
  }

module _ {ℓ ℓ' : Level} {ℂ : Category {ℓ} {ℓ}} where
  private
    C-Obj = Object ℂ
    _+_   = Arrow ℂ

  RepFunctor : Functor ℂ Sets
  RepFunctor =
    record
    { F = λ A → (B : C-Obj) → Hom {ℂ = ℂ} A B
    ; f = λ { {c' = c'} f g → {!HomFromArrow {ℂ = } c' g!}}
    ; ident = {!!}
    ; distrib = {!!}
    }
