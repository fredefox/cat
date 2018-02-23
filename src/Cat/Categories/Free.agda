{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Categories.Free where

open import Agda.Primitive
open import Cubical hiding (Path ; isSet ; empty)
open import Data.Product

open import Cat.Category

open IsCategory

data Path {ℓ ℓ' : Level} {A : Set ℓ} (R : A → A → Set ℓ') : (a b : A) → Set (ℓ ⊔ ℓ') where
  empty : {a : A} → Path R a a
  cons : {a b c : A} → R b c → Path R a b → Path R a c

concatenate _++_ : ∀ {ℓ ℓ'} {A : Set ℓ} {a b c : A} {R : A → A → Set ℓ'} → Path R b c → Path R a b → Path R a c
concatenate empty p = p
concatenate (cons x q) p = cons x (concatenate q p)
_++_ = concatenate

singleton : ∀ {ℓ} {𝓤 : Set ℓ} {ℓr} {R : 𝓤 → 𝓤 → Set ℓr} {A B : 𝓤} → R A B → Path R A B
singleton f = cons f empty

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  module ℂ = Category ℂ
  open Category ℂ

  private
    p-isAssociative : {A B C D : Object} {r : Path Arrow A B} {q : Path Arrow B C} {p : Path Arrow C D}
      → p ++ (q ++ r) ≡ (p ++ q) ++ r
    p-isAssociative {r = r} {q} {empty} = refl
    p-isAssociative {A} {B} {C} {D} {r = r} {q} {cons x p} = begin
      cons x p ++ (q ++ r)   ≡⟨ cong (cons x) lem ⟩
      cons x ((p ++ q) ++ r) ≡⟨⟩
      (cons x p ++ q) ++ r ∎
      where
        lem : p ++ (q ++ r) ≡ ((p ++ q) ++ r)
        lem = p-isAssociative {r = r} {q} {p}

    ident-r : ∀ {A} {B} {p : Path Arrow A B} → concatenate p empty ≡ p
    ident-r {p = empty} = refl
    ident-r {p = cons x p} = cong (cons x) ident-r

    ident-l : ∀ {A} {B} {p : Path Arrow A B} → concatenate empty p ≡ p
    ident-l = refl

    module _ {A B : Object} where
      isSet : Cubical.isSet (Path Arrow A B)
      isSet a b p q = {!!}

  RawFree : RawCategory ℓ (ℓ ⊔ ℓ')
  RawFree = record
    { Object = Object
    ; Arrow = Path Arrow
    ; 𝟙 = empty
    ; _∘_ = concatenate
    }
  RawIsCategoryFree : IsCategory RawFree
  RawIsCategoryFree = record
    { isAssociative = λ { {f = f} {g} {h} → p-isAssociative {r = f} {g} {h}}
    ; ident = ident-r , ident-l
    ; arrowIsSet = {!!}
    ; univalent = {!!}
    }
