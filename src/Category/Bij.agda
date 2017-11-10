{-# OPTIONS --cubical #-}

open import Cubical.PathPrelude hiding ( Id )

module _ {A : Set} {a : A} {P : A → Set} where
  Q : A → Set
  Q a = A

  t : Σ[ a ∈ A ] P a → Q a
  t (a , Pa) = a
  u : Q a → Σ[ a ∈ A ] P a
  u a = a , {!!}

  tu-bij : (a : Q a) → (t ∘ u) a ≡ a
  tu-bij a = refl

  v : P a → Q a
  v x = {!!}
  w : Q a → P a
  w x = {!!}

  vw-bij : (a : P a) → (w ∘ v) a ≡ a
  vw-bij a = refl
  -- tubij a with (t ∘ u) a
  -- ... | q = {!!}

  data Id {A : Set} (a : A) : Set where
    id : A → Id a

  data Id' {A : Set} (a : A) : Set where
    id' : A → Id' a

  T U : Set
  T = Id a
  U = Id' a

  f : T → U
  f (id x) = id' x
  g : U → T
  g (id' x) = id x

  fg-bij : (x : U) → (f ∘ g) x ≡ x
  fg-bij (id' x) = {!!}
