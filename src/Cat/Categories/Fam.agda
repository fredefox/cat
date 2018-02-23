{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Categories.Fam where

open import Agda.Primitive
open import Data.Product
import Function

open import Cubical
open import Cubical.Universe

open import Cat.Category
open import Cat.Equality

open Equality.Data.Product

module _ (ℓa ℓb : Level) where
  private
    Object = Σ[ hA ∈ hSet {ℓa} ] (proj₁ hA → hSet {ℓb})
    Arr : Object → Object → Set (ℓa ⊔ ℓb)
    Arr ((A , _) , B) ((A' , _) , B') = Σ[ f ∈ (A → A') ] ({x : A} → proj₁ (B x) → proj₁ (B' (f x)))
    𝟙 : {A : Object} → Arr A A
    proj₁ 𝟙 = λ x → x
    proj₂ 𝟙 = λ b → b
    _∘_ : {a b c : Object} → Arr b c → Arr a b → Arr a c
    (g , g') ∘ (f , f') = g Function.∘ f , g' Function.∘ f'

    RawFam : RawCategory (lsuc (ℓa ⊔ ℓb)) (ℓa ⊔ ℓb)
    RawFam = record
      { Object = Object
      ; Arrow = Arr
      ; 𝟙 = λ { {A} → 𝟙 {A = A}}
      ; _∘_ = λ {a b c} → _∘_ {a} {b} {c}
      }

    open RawCategory RawFam hiding (Object ; 𝟙)

    isAssociative : IsAssociative
    isAssociative = Σ≡ refl refl

    isIdentity : IsIdentity λ { {A} → 𝟙 {A} }
    isIdentity = (Σ≡ refl refl) , Σ≡ refl refl

    open import Cubical.NType.Properties
    open import Cubical.Sigma
    instance
      isCategory : IsCategory RawFam
      isCategory = record
        { isAssociative = λ {A} {B} {C} {D} {f} {g} {h} → isAssociative {A} {B} {C} {D} {f} {g} {h}
        ; isIdentity = λ {A} {B} {f} → isIdentity {A} {B} {f = f}
        ; arrowsAreSets = λ {
          {((A , hA) , famA)}
          {((B , hB) , famB)}
            → setSig
              {sA = setPi λ _ → hB}
              {sB = λ f →
                let
                  helpr : isSet ((a : A) → proj₁ (famA a) → proj₁ (famB (f a)))
                  helpr = setPi λ a → setPi λ _ → proj₂ (famB (f a))
                  -- It's almost like above, but where the first argument is
                  -- implicit.
                  res : isSet ({a : A} → proj₁ (famA a) → proj₁ (famB (f a)))
                  res = {!!}
                in res
              }
          }
        ; univalent = {!!}
        }

  Fam : Category (lsuc (ℓa ⊔ ℓb)) (ℓa ⊔ ℓb)
  Category.raw Fam = RawFam
