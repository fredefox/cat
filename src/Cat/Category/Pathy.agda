{-# OPTIONS --cubical #-}

module Cat.Category.Pathy where

open import Level
open import Cubical

{-
module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
  (P : ∀ y → x ≡ y → Set ℓ') (d : P x ((λ i → x))) where
  pathJ' : (y : A) → (p : x ≡ y) → P y p
  pathJ' _ p = transp (λ i → uncurry P (contrSingl p i)) d

  pathJprop' : pathJ' _ refl ≡ d
  pathJprop' i
    = primComp (λ _ → P x refl) i (λ {j (i = i1) → d}) d


module _ {ℓ ℓ'} {A : Set ℓ}
  (P : (x y : A) → x ≡ y → Set ℓ') (d : (x : A) → P x x refl) where
  pathJ'' : (x y : A) → (p : x ≡ y) → P x y p
  pathJ'' _ _ p = transp (λ i →
    let
      P' = uncurry P
      q  = (contrSingl p i)
    in
      {!uncurry (uncurry P)!} ) d
-}

module _ {ℓ ℓ'} {A : Set ℓ}
  (C : (x y : A) → x ≡ y → Set ℓ')
  (c : (x : A) → C x x refl) where

  =-ind : (x y : A) → (p : x ≡ y) → C x y p
  =-ind x y p = pathJ (C x) (c x) y p

module _ {ℓ ℓ' : Level} {A : Set ℓ} {P : A → Set ℓ} {x y : A} where
  private
    D : (x y : A) → (x ≡ y) → Set ℓ
    D x y p = P x → P y

    id : {ℓ : Level} → {A : Set ℓ} → A → A
    id x = x

    d : (x : A) → D x x refl
    d x = id {A = P x}

  -- the p refers to the third argument
  liftP : x ≡ y → P x → P y
  liftP p = =-ind D d x y p

  -- lift' : (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , liftP p u)
  -- lift' u p = {!!}
