{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Categories.Fam where

open import Agda.Primitive
open import Data.Product
open import Cubical
import Function

open import Cat.Category
open import Cat.Equality

open Equality.Data.Product

module _ (ℓa ℓb : Level) where
  private
    Obj' = Σ[ A ∈ Set ℓa ] (A → Set ℓb)
    Arr : Obj' → Obj' → Set (ℓa ⊔ ℓb)
    Arr (A , B) (A' , B') = Σ[ f ∈ (A → A') ] ({x : A} → B x → B' (f x))
    one : {o : Obj'} → Arr o o
    proj₁ one = λ x → x
    proj₂ one = λ b → b
    _∘_ : {a b c : Obj'} → Arr b c → Arr a b → Arr a c
    (g , g') ∘ (f , f') = g Function.∘ f , g' Function.∘ f'
    _⟨_∘_⟩ : {a b : Obj'} → (c : Obj') → Arr b c → Arr a b → Arr a c
    c ⟨ g ∘ f ⟩ = _∘_ {c = c} g f

    module _ {A B C D : Obj'} {f : Arr A B} {g : Arr B C} {h : Arr C D} where
      assoc : (D ⟨ h ∘ C ⟨ g ∘ f ⟩ ⟩) ≡ D ⟨ D ⟨ h ∘ g ⟩ ∘ f ⟩
      assoc = Σ≡ refl refl

    module _ {A B : Obj'} {f : Arr A B} where
      ident : B ⟨ f ∘ one ⟩ ≡ f × B ⟨ one {B} ∘ f ⟩ ≡ f
      ident = (Σ≡ refl refl) , Σ≡ refl refl


    RawFam : RawCategory (lsuc (ℓa ⊔ ℓb)) (ℓa ⊔ ℓb)
    RawFam = record
      { Object = Obj'
      ; Arrow = Arr
      ; 𝟙 = one
      ; _∘_ = λ {a b c} → _∘_ {a} {b} {c}
      }

    instance
      isCategory : IsCategory RawFam
      isCategory = record
        { assoc = λ {A} {B} {C} {D} {f} {g} {h} → assoc {D = D} {f} {g} {h}
        ; ident = λ {A} {B} {f} → ident {A} {B} {f = f}
        ; arrow-is-set = ?
        ; univalent = ?
        }

  Fam : Category (lsuc (ℓa ⊔ ℓb)) (ℓa ⊔ ℓb)
  Fam = RawFam , isCategory
