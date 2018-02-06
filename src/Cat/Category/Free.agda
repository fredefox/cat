{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Category.Free where

open import Agda.Primitive
open import Cubical hiding (Path)
open import Data.Product

open import Cat.Category as C

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    open module ℂ = Category ℂ

  postulate
    Path : (a b : ℂ.Object) → Set ℓ'
    emptyPath : (o : ℂ.Object) → Path o o
    concatenate : {a b c : ℂ.Object} → Path b c → Path a b → Path a c

  private
    module _ {A B C D : ℂ.Object} {r : Path A B} {q : Path B C} {p : Path C D} where
      postulate
        p-assoc : concatenate {A} {C} {D} p (concatenate {A} {B} {C} q r)
          ≡ concatenate {A} {B} {D} (concatenate {B} {C} {D} p q) r
    module _ {A B : ℂ.Object} {p : Path A B} where
      postulate
        ident-r : concatenate {A} {A} {B} p (emptyPath A) ≡ p
        ident-l : concatenate {A} {B} {B} (emptyPath B) p ≡ p

  RawFree : RawCategory ℓ ℓ'
  RawFree = record
    { Object = ℂ.Object
    ; Arrow = Path
    ; 𝟙 = λ {o} → emptyPath o
    ; _∘_ = λ {a b c} → concatenate {a} {b} {c}
    }
  RawIsCategoryFree : IsCategory RawFree
  RawIsCategoryFree = record
    { assoc = p-assoc
    ; ident = ident-r , ident-l
    ; arrowIsSet = {!!}
    ; univalent = {!!}
    }
