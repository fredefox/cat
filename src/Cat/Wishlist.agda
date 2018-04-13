{-# OPTIONS --allow-unsolved-metas #-}
module Cat.Wishlist where

open import Level hiding (suc)
open import Cubical
open import Cubical.NType
open import Data.Nat using (_≤_ ; z≤n ; s≤s ; zero ; suc)
open import Agda.Builtin.Sigma

open import Cubical.NType.Properties

private
  step : ∀ {ℓ} {A : Set ℓ} → isContr A → (x y : A) → isContr (x ≡ y)
  step (a , contr) x y = {!p , c!}
    -- where
    -- p : x ≡ y
    -- p = begin
    --   x ≡⟨ sym (contr x) ⟩
    --   a ≡⟨ contr y ⟩
    --   y ∎
    -- c : (q : x ≡ y) → p ≡ q
    -- c q i j = contr (p {!!}) {!!}

  -- Contractible types have any given homotopy level.
  contrInitial : {ℓ : Level} {A : Set ℓ} → ∀ n → isContr A → HasLevel n A
  contrInitial ⟨-2⟩ contr = contr
  -- lem' (S ⟨-2⟩) (a , contr) = {!step!}
  contrInitial (S ⟨-2⟩) (a , contr) x y = begin
    x ≡⟨ sym (contr x) ⟩
    a ≡⟨ contr y ⟩
    y ∎
  contrInitial (S (S n)) contr x y = {!lvl!} -- Why is this not well-founded?
    where
    c : isContr (x ≡ y)
    c = step contr x y
    lvl : HasLevel (S n) (x ≡ y)
    lvl = contrInitial {A = x ≡ y} (S n) c

module _ {ℓ : Level} {A : Set ℓ} where
  ntypeCommulative : ∀ {n m} → n ≤ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A
  ntypeCommulative {n = zero} {m} z≤n lvl = {!contrInitial ⟨ m ⟩₋₂ lvl!}
  ntypeCommulative {n = .(suc _)} {.(suc _)} (s≤s x) lvl = {!!}
