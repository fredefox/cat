{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --cubical              #-}
module Cat.Categories.Fam where

open import Cat.Prelude

open import Cat.Category

module _ (ℓa ℓb : Level) where
  private
    Object = Σ[ hA ∈ hSet ℓa ] (fst hA → hSet ℓb)
    Arr : Object → Object → Set (ℓa ⊔ ℓb)
    Arr ((A , _) , B) ((A' , _) , B') = Σ[ f ∈ (A → A') ] ({x : A} → fst (B x) → fst (B' (f x)))
    identity : {A : Object} → Arr A A
    fst identity = λ x → x
    snd identity = λ b → b
    _<<<_ : {a b c : Object} → Arr b c → Arr a b → Arr a c
    (g , g') <<< (f , f') = g ∘ f , g' ∘ f'

    RawFam : RawCategory (lsuc (ℓa ⊔ ℓb)) (ℓa ⊔ ℓb)
    RawFam = record
      { Object = Object
      ; Arrow = Arr
      ; identity = λ { {A} → identity {A = A}}
      ; _<<<_ = λ {a b c} → _<<<_ {a} {b} {c}
      }

    open RawCategory RawFam hiding (Object ; identity)

    isAssociative : IsAssociative
    isAssociative = Σ≡ (refl , refl)

    isIdentity : IsIdentity λ { {A} → identity {A} }
    isIdentity = (Σ≡ (refl , refl)) , Σ≡ (refl , refl)

    isPreCategory : IsPreCategory RawFam
    IsPreCategory.isAssociative isPreCategory
      {A} {B} {C} {D} {f} {g} {h} = isAssociative {A} {B} {C} {D} {f} {g} {h}
    IsPreCategory.isIdentity isPreCategory
      {A} {B} {f} = isIdentity {A} {B} {f = f}
    IsPreCategory.arrowsAreSets isPreCategory
      {(A , hA) , famA} {(B , hB) , famB}
      = setSig
        (setPi λ _ → hB)
        (λ f →
          let
            helpr : isSet ((a : A) → fst (famA a) → fst (famB (f a)))
            helpr = setPi λ a → setPi λ _ → snd (famB (f a))
            -- It's almost like above, but where the first argument is
            -- implicit.
            res : isSet ({a : A} → fst (famA a) → fst (famB (f a)))
            res = {!!}
          in res
        )

    isCategory : IsCategory RawFam
    IsCategory.isPreCategory isCategory = isPreCategory
    IsCategory.univalent     isCategory = {!!}

  Fam : Category (lsuc (ℓa ⊔ ℓb)) (ℓa ⊔ ℓb)
  Category.raw Fam = RawFam
  Category.isCategory Fam = isCategory
