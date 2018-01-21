module Cat.Category.Free where

open import Agda.Primitive
open import Cubical.PathPrelude hiding (Path)
open import Data.Product

open import Cat.Category as C

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    open module ℂ = Category ℂ
    Obj = ℂ.Object

  Path : ( a b : Obj ) → Set ℓ'
  Path a b = undefined

  postulate emptyPath : (o : Obj) → Path o o

  postulate concatenate : {a b c : Obj} → Path b c → Path a b → Path a c

  private
    module _ {A B C D : Obj} {r : Path A B} {q : Path B C} {p : Path C D} where
      postulate
        p-assoc : concatenate {A} {C} {D} p (concatenate {A} {B} {C} q r)
          ≡ concatenate {A} {B} {D} (concatenate {B} {C} {D} p q) r
    module _ {A B : Obj} {p : Path A B} where
      postulate
        ident-r : concatenate {A} {A} {B} p (emptyPath A) ≡ p
        ident-l : concatenate {A} {B} {B} (emptyPath B) p ≡ p

  Free : Category ℓ ℓ'
  Free = record
    { Object = Obj
    ; Arrow = Path
    ; 𝟙 = λ {o} → emptyPath o
    ; _⊕_ = λ {a b c} → concatenate {a} {b} {c}
    ; isCategory = record { assoc = p-assoc ; ident = ident-r , ident-l }
    }
