{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Free where

open import Cat.Prelude hiding (Path ; empty)

open import Relation.Binary

open import Cat.Category

module _ {ℓ : Level} {A : Set ℓ} {ℓr : Level} where
  data Path (R : Rel A ℓr) : (a b : A) → Set (ℓ ⊔ ℓr) where
    empty : {a : A}                          → Path R a a
    cons  : {a b c : A} → R b c → Path R a b → Path R a c

  module _ {R : Rel A ℓr} where
    concatenate : {a b c : A} → Path R b c → Path R a b → Path R a c
    concatenate empty p = p
    concatenate (cons x q) p = cons x (concatenate q p)
    _++_ : {a b c : A} → Path R b c → Path R a b → Path R a c
    a ++ b = concatenate a b

    singleton : {a b : A} → R a b → Path R a b
    singleton f = cons f empty

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  private
    module ℂ = Category ℂ

    RawFree : RawCategory ℓa (ℓa ⊔ ℓb)
    RawCategory.Object   RawFree = ℂ.Object
    RawCategory.Arrow    RawFree = Path ℂ.Arrow
    RawCategory.identity RawFree = empty
    RawCategory._<<<_    RawFree = concatenate

    open RawCategory RawFree

    isAssociative : {A B C D : ℂ.Object} {r : Path ℂ.Arrow A B} {q : Path ℂ.Arrow B C} {p : Path ℂ.Arrow C D}
      → p ++ (q ++ r) ≡ (p ++ q) ++ r
    isAssociative {r = r} {q} {empty} = refl
    isAssociative {A} {B} {C} {D} {r = r} {q} {cons x p} = begin
      cons x p ++ (q ++ r)   ≡⟨ cong (cons x) lem ⟩
      cons x ((p ++ q) ++ r) ≡⟨⟩
      (cons x p ++ q) ++ r ∎
      where
      lem : p ++ (q ++ r) ≡ ((p ++ q) ++ r)
      lem = isAssociative {r = r} {q} {p}

    ident-r : ∀ {A} {B} {p : Path ℂ.Arrow A B} → concatenate p empty ≡ p
    ident-r {p = empty} = refl
    ident-r {p = cons x p} = cong (cons x) ident-r

    ident-l : ∀ {A} {B} {p : Path ℂ.Arrow A B} → concatenate empty p ≡ p
    ident-l = refl

    isIdentity : IsIdentity identity
    isIdentity = ident-l , ident-r

    open Univalence isIdentity

    module _ {A B : ℂ.Object} where
      arrowsAreSets : isSet (Path ℂ.Arrow A B)
      arrowsAreSets a b p q = {!!}

    isPreCategory : IsPreCategory RawFree
    IsPreCategory.isAssociative isPreCategory {f = f} {g} {h} = isAssociative {r = f} {g} {h}
    IsPreCategory.isIdentity    isPreCategory = isIdentity
    IsPreCategory.arrowsAreSets isPreCategory = arrowsAreSets

    module _ {A B : ℂ.Object} where
      eqv : isEquiv (Univalence.idToIso isIdentity A B)
      eqv = {!!}

    univalent : Univalent
    univalent = eqv

    isCategory : IsCategory RawFree
    IsCategory.isPreCategory isCategory = isPreCategory
    IsCategory.univalent     isCategory = univalent

  Free : Category _ _
  Free = record { raw = RawFree ; isCategory = isCategory }
