{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Equivalence where

open import Cubical.Primitives
open import Cubical.FromStdLib renaming (ℓ-max to _⊔_)
open import Cubical.PathPrelude hiding (inverse ; _≃_)
open import Cubical.PathPrelude using (isEquiv ; isContr ; fiber) public
open import Cubical.GradLemma

module _ {ℓa ℓb : Level} where
  private
    ℓ = ℓa ⊔ ℓb

  module _ {A : Set ℓa} {B : Set ℓb} where
    -- Quasi-inverse in [HoTT] §2.4.6
    -- FIXME Maybe rename?
    record AreInverses (f : A → B) (g : B → A) : Set ℓ where
      field
        verso-recto : g ∘ f ≡ idFun A
        recto-verso : f ∘ g ≡ idFun B
      obverse = f
      reverse = g
      inverse = reverse
      toPair : Σ _ _
      toPair = verso-recto , recto-verso

    Isomorphism : (f : A → B) → Set _
    Isomorphism f = Σ (B → A) λ g → AreInverses f g

    module _ {f : A → B} {g : B → A}
        (inv : (g ∘ f) ≡ idFun A
             × (f ∘ g) ≡ idFun B) where
      open Σ inv renaming (fst to ve-re ; snd to re-ve)
      toAreInverses : AreInverses f g
      toAreInverses = record
        { verso-recto = ve-re
        ; recto-verso = re-ve
        }

  _≅_ : Set ℓa → Set ℓb → Set _
  A ≅ B = Σ (A → B) Isomorphism

module _ {ℓ : Level} {A B : Set ℓ} {f : A → B}
  (g : B → A) (s : {A B : Set ℓ} → isSet (A → B)) where

  propAreInverses : isProp (AreInverses {A = A} {B} f g)
  propAreInverses x y i = record
    { verso-recto = ve-re
    ; recto-verso = re-ve
    }
    where
    open AreInverses
    ve-re : g ∘ f ≡ idFun A
    ve-re = s (g ∘ f) (idFun A) (verso-recto x) (verso-recto y) i
    re-ve : f ∘ g ≡ idFun B
    re-ve = s (f ∘ g) (idFun B) (recto-verso x) (recto-verso y) i

-- In HoTT they generalize an equivalence to have the following 3 properties:
module _ {ℓa ℓb ℓ : Level} (A : Set ℓa) (B : Set ℓb) where
  record Equiv (iseqv : (A → B) → Set ℓ) : Set (ℓa ⊔ ℓb ⊔ ℓ) where
    field
      fromIso      : {f : A → B} → Isomorphism f → iseqv f
      toIso        : {f : A → B} → iseqv f → Isomorphism f
      propIsEquiv  : (f : A → B) → isProp (iseqv f)

    -- You're alerady assuming here that we don't need eta-equality on the
    -- equivalence!
    _~_ : Set ℓa → Set ℓb → Set _
    A ~ B = Σ _ iseqv

    inverse-from-to-iso : ∀ {f} (x : _) → (fromIso {f} ∘ toIso {f}) x ≡ x
    inverse-from-to-iso x = begin
      (fromIso ∘ toIso) x ≡⟨⟩
      fromIso (toIso x)   ≡⟨ propIsEquiv _ (fromIso (toIso x)) x ⟩
      x ∎

    -- `toIso` is abstract - so I probably can't close this proof.
    -- inverse-to-from-iso : ∀ {f} → toIso {f} ∘ fromIso {f} ≡ idFun _
    -- inverse-to-from-iso = funExt (λ x → begin
    --   (toIso ∘ fromIso) x ≡⟨⟩
    --   toIso (fromIso x)   ≡⟨ cong toIso (propIsEquiv _ (fromIso x) y) ⟩
    --   toIso y             ≡⟨ {!!} ⟩
    --   x ∎)
    --   where
    --   y : iseqv _
    --   y = {!!}

    fromIsomorphism : A ≅ B → A ~ B
    fromIsomorphism (f , iso) = f , fromIso iso

    toIsomorphism : A ~ B → A ≅ B
    toIsomorphism (f , eqv) = f , toIso eqv

module _ {ℓa ℓb : Level} (A : Set ℓa) (B : Set ℓb) where
  -- A wrapper around PathPrelude.≃
  open Cubical.PathPrelude using (_≃_ ; isEquiv)
  private
    module _ {obverse : A → B} (e : isEquiv A B obverse) where
      inverse : B → A
      inverse b = fst (fst (e b))

      reverse : B → A
      reverse = inverse

      areInverses : AreInverses obverse inverse
      areInverses = record
        { verso-recto = funExt verso-recto
        ; recto-verso = funExt recto-verso
        }
        where
        recto-verso : ∀ b → (obverse ∘ inverse) b ≡ b
        recto-verso b = begin
          (obverse ∘ inverse) b ≡⟨ sym (μ b) ⟩
          b ∎
          where
          μ : (b : B) → b ≡ obverse (inverse b)
          μ b = snd (fst (e b))
        verso-recto : ∀ a → (inverse ∘ obverse) a ≡ a
        verso-recto a = begin
          (inverse ∘ obverse) a ≡⟨ sym h ⟩
          a'                    ≡⟨ u' ⟩
          a ∎
          where
          c : isContr (fiber obverse (obverse a))
          c = e (obverse a)
          fbr : fiber obverse (obverse a)
          fbr = fst c
          a' : A
          a' = fst fbr
          allC : (y : fiber obverse (obverse a)) → fbr ≡ y
          allC = snd c
          k : fbr ≡ (inverse (obverse a), _)
          k = allC (inverse (obverse a) , sym (recto-verso (obverse a)))
          h : a' ≡ inverse (obverse a)
          h i = fst (k i)
          u : fbr ≡ (a , refl)
          u = allC (a , refl)
          u' : a' ≡ a
          u' i = fst (u i)

      iso : Isomorphism obverse
      iso = reverse , areInverses

    toIsomorphism : {f : A → B} → isEquiv A B f → Isomorphism f
    toIsomorphism = iso

    ≃isEquiv : Equiv A B (isEquiv A B)
    Equiv.fromIso     ≃isEquiv {f} (f~ , iso) = gradLemma f f~ rv vr
      where
      open AreInverses iso
      rv : (b : B) → _ ≡ b
      rv b i = recto-verso i b
      vr : (a : A) → _ ≡ a
      vr a i = verso-recto i a
    Equiv.toIso        ≃isEquiv = toIsomorphism
    Equiv.propIsEquiv  ≃isEquiv = P.propIsEquiv
      where
      import Cubical.NType.Properties as P

  module Equiv≃ where
    open Equiv ≃isEquiv public
    inverse-to-from-iso : ∀ {f} (x : _) → (toIso {f} ∘ fromIso {f}) x ≡ x
    inverse-to-from-iso {f} x = begin
      (toIso ∘ fromIso) x ≡⟨⟩
      toIso (fromIso x)   ≡⟨ cong toIso (propIsEquiv _ (fromIso x) y) ⟩
      toIso y             ≡⟨ py ⟩
      x ∎
      where
      open Σ x renaming (fst to f~ ; snd to inv)
      module inv = AreInverses inv
      y  : isEquiv _ _ f
      y  = {!!}
      open Σ (toIso y) renaming (fst to f~' ; snd to inv')
      py : toIso y ≡ (f~ , inv)
      py = {!!}

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  open Cubical.PathPrelude using (_≃_)

  -- Gives the quasi inverse from an equivalence.
  module Equivalence (e : A ≃ B) where
    open Equiv≃ A B public
    private
      iso : Isomorphism (fst e)
      iso = snd (toIsomorphism e)

    open AreInverses (snd iso) public

    composeIso : {ℓc : Level} {C : Set ℓc} → (B ≅ C) → A ≅ C
    composeIso {C = C} (g , g' , iso-g) = g ∘ obverse , inverse ∘ g' , inv
      where
      module iso-g = AreInverses iso-g
      inv : AreInverses (g ∘ obverse) (inverse ∘ g')
      AreInverses.verso-recto inv = begin
        (inverse ∘ g') ∘ (g ∘ obverse)   ≡⟨⟩
        (inverse ∘ (g' ∘ g) ∘ obverse)
          ≡⟨ cong (λ φ → φ ∘ obverse) (cong (λ φ → inverse ∘ φ) iso-g.verso-recto) ⟩
        (inverse ∘ idFun B ∘ obverse)    ≡⟨⟩
        (inverse ∘ obverse)              ≡⟨ verso-recto ⟩
        idFun A ∎
      AreInverses.recto-verso inv = begin
        g ∘ obverse ∘ inverse ∘ g'
          ≡⟨ cong (λ φ → φ ∘ g') (cong (λ φ → g ∘ φ) recto-verso) ⟩
        g ∘ idFun B ∘ g' ≡⟨⟩
        g ∘ g'           ≡⟨ iso-g.recto-verso ⟩
        idFun C ∎

    compose : {ℓc : Level} {C : Set ℓc} → (B ≃ C) → A ≃ C
    compose {C = C} e = A≃C.fromIsomorphism is
      where
      module B≃C = Equiv≃ B C
      module A≃C = Equiv≃ A C
      is : A ≅ C
      is = composeIso (B≃C.toIsomorphism e)

    symmetryIso : B ≅ A
    symmetryIso
      = inverse
      , obverse
      , record
        { verso-recto = recto-verso
        ; recto-verso = verso-recto
        }

    symmetry : B ≃ A
    symmetry = B≃A.fromIsomorphism symmetryIso
      where
      module B≃A = Equiv≃ B A

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  open import Cubical.PathPrelude renaming (_≃_ to _≃η_)
  open import Cubical.Univalence using (_≃_)

  doEta : A ≃ B → A ≃η B
  doEta (_≃_.con eqv isEqv) = eqv , isEqv

  deEta : A ≃η B → A ≃ B
  deEta (eqv , isEqv) = _≃_.con eqv isEqv

module NoEta {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  open import Cubical.PathPrelude renaming (_≃_ to _≃η_)
  open import Cubical.Univalence using (_≃_)

  module Equivalence′ (e : A ≃ B) where
    open Equivalence (doEta e) hiding
      ( toIsomorphism ; fromIsomorphism ; _~_
      ; compose ; symmetryIso ; symmetry ) public

    compose : {ℓc : Level} {C : Set ℓc} → (B ≃ C) → A ≃ C
    compose ee = deEta (Equivalence.compose (doEta e) (doEta ee))

    symmetry : B ≃ A
    symmetry = deEta (Equivalence.symmetry (doEta e))

  -- fromIso      : {f : A → B} → Isomorphism f → isEquiv f
  -- fromIso = ?

  -- toIso        : {f : A → B} → isEquiv f → Isomorphism f
  -- toIso = ?

  fromIsomorphism : A ≅ B → A ≃ B
  fromIsomorphism (f , iso) = _≃_.con f (Equiv≃.fromIso _ _ iso)

  toIsomorphism : A ≃ B → A ≅ B
  toIsomorphism (_≃_.con f eqv) = f , Equiv≃.toIso _ _ eqv
