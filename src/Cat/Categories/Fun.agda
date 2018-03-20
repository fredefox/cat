{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Fun where

open import Agda.Primitive
open import Data.Product


open import Cubical
open import Cubical.GradLemma
open import Cubical.NType.Properties

open import Cat.Category
open import Cat.Category.Functor hiding (identity)
open import Cat.Category.NaturalTransformation

module Fun {ℓc ℓc' ℓd ℓd' : Level} (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  module NT = NaturalTransformation ℂ 𝔻
  open NT public
  private
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻
  private
    module _ {A B C D : Functor ℂ 𝔻} {θ' : NaturalTransformation A B}
      {η' : NaturalTransformation B C} {ζ' : NaturalTransformation C D} where
      θ = proj₁ θ'
      η = proj₁ η'
      ζ = proj₁ ζ'
      θNat = proj₂ θ'
      ηNat = proj₂ η'
      ζNat = proj₂ ζ'
      L : NaturalTransformation A D
      L = (NT[_∘_] {A} {C} {D} ζ' (NT[_∘_] {A} {B} {C} η' θ'))
      R : NaturalTransformation A D
      R = (NT[_∘_] {A} {B} {D} (NT[_∘_] {B} {C} {D} ζ' η') θ')
      _g⊕f_ = NT[_∘_] {A} {B} {C}
      _h⊕g_ = NT[_∘_] {B} {C} {D}
      isAssociative : L ≡ R
      isAssociative = lemSig (naturalIsProp {F = A} {D})
        L R (funExt (λ x → 𝔻.isAssociative))

  private
    module _ {A B : Functor ℂ 𝔻} {f : NaturalTransformation A B} where
      allNatural = naturalIsProp {F = A} {B}
      f' = proj₁ f
      eq-r : ∀ C → (𝔻 [ f' C ∘ identityTrans A C ]) ≡ f' C
      eq-r C = begin
        𝔻 [ f' C ∘ identityTrans A C ] ≡⟨⟩
        𝔻 [ f' C ∘ 𝔻.𝟙 ]  ≡⟨ proj₁ 𝔻.isIdentity ⟩
        f' C ∎
      eq-l : ∀ C → (𝔻 [ identityTrans B C ∘ f' C ]) ≡ f' C
      eq-l C = proj₂ 𝔻.isIdentity
      ident-r : (NT[_∘_] {A} {A} {B} f (NT.identity A)) ≡ f
      ident-r = lemSig allNatural _ _ (funExt eq-r)
      ident-l : (NT[_∘_] {A} {B} {B} (NT.identity B) f) ≡ f
      ident-l = lemSig allNatural _ _ (funExt eq-l)
      isIdentity
        : (NT[_∘_] {A} {A} {B} f (NT.identity A)) ≡ f
        × (NT[_∘_] {A} {B} {B} (NT.identity B) f) ≡ f
      isIdentity = ident-r , ident-l
  -- Functor categories. Objects are functors, arrows are natural transformations.
  RawFun : RawCategory (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  RawFun = record
    { Object = Functor ℂ 𝔻
    ; Arrow = NaturalTransformation
    ; 𝟙 = λ {F} → NT.identity F
    ; _∘_ = λ {F G H} → NT[_∘_] {F} {G} {H}
    }

  open RawCategory RawFun
  open Univalence (λ {A} {B} {f} → isIdentity {A} {B} {f})

  private
    module _ {A B : Functor ℂ 𝔻} where
      module A = Functor A
      module B = Functor B
      module _ (p : A ≡ B) where
        omapP : A.omap ≡ B.omap
        omapP i = Functor.omap (p i)

        coerceAB : ∀ {X} → 𝔻 [ A.omap X , A.omap X ] ≡ 𝔻 [ A.omap X , B.omap X ]
        coerceAB {X} = cong (λ φ → 𝔻 [ A.omap X , φ X ]) omapP

        -- The transformation will be the identity on 𝔻. Such an arrow has the
        -- type `A.omap A → A.omap A`. Which we can coerce to have the type
        -- `A.omap → B.omap` since `A` and `B` are equal.
        coe𝟙 : Transformation A B
        coe𝟙 X = coe coerceAB 𝔻.𝟙

        module _ {a b : ℂ.Object} (f : ℂ [ a , b ]) where
          nat' : 𝔻 [ coe𝟙 b ∘ A.fmap f ] ≡ 𝔻 [ B.fmap f ∘ coe𝟙 a ]
          nat' = begin
            (𝔻 [ coe𝟙 b ∘ A.fmap f ]) ≡⟨ {!!} ⟩
            (𝔻 [ B.fmap f ∘ coe𝟙 a ]) ∎

        transs : (i : I) → Transformation A (p i)
        transs = {!!}

        natt : (i : I) → Natural A (p i) {!!}
        natt = {!!}

        t : Natural A B coe𝟙
        t = coe c (identityNatural A)
          where
          c : Natural A A (identityTrans A) ≡ Natural A B coe𝟙
          c = begin
            Natural A A (identityTrans A) ≡⟨ (λ x → {!natt ?!}) ⟩
            Natural A B coe𝟙 ∎
          -- cong (λ φ → {!Natural A A (identityTrans A)!}) {!!}

        k : Natural A A (identityTrans A) → Natural A B coe𝟙
        k n {a} {b} f = res
          where
          res : (𝔻 [ coe𝟙 b ∘ A.fmap f ]) ≡ (𝔻 [ B.fmap f ∘ coe𝟙 a ])
          res = {!!}

        nat : Natural A B coe𝟙
        nat = nat'

        fromEq : NaturalTransformation A B
        fromEq = coe𝟙 , nat

  module _ {A B : Functor ℂ 𝔻} where
    obverse : A ≡ B → A ≅ B
    obverse p = res
      where
      ob  : Arrow A B
      ob = fromEq p
      re : Arrow B A
      re = fromEq (sym p)
      vr : _∘_ {A = A} {B} {A} re ob ≡ 𝟙 {A}
      vr = {!!}
      rv : _∘_ {A = B} {A} {B} ob re ≡ 𝟙 {B}
      rv = {!!}
      isInverse : IsInverseOf {A} {B} ob re
      isInverse = vr , rv
      iso : Isomorphism {A} {B} ob
      iso = re , isInverse
      res : A ≅ B
      res = ob , iso

    reverse : A ≅ B → A ≡ B
    reverse iso = {!!}

    ve-re : (y : A ≅ B) → obverse (reverse y) ≡ y
    ve-re = {!!}

    re-ve : (x : A ≡ B) → reverse (obverse x) ≡ x
    re-ve = {!!}

    done : isEquiv (A ≡ B) (A ≅ B) (Univalence.id-to-iso (λ { {A} {B} → isIdentity {A} {B}}) A B)
    done = {!gradLemma obverse reverse ve-re re-ve!}

  univalent : Univalent
  univalent = done

  instance
    isCategory : IsCategory RawFun
    isCategory = record
      { isAssociative = λ {A B C D} → isAssociative {A} {B} {C} {D}
      ; isIdentity = λ {A B} → isIdentity {A} {B}
      ; arrowsAreSets = λ {F} {G} → naturalTransformationIsSet {F} {G}
      ; univalent = univalent
      }

  Fun : Category (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  Category.raw Fun = RawFun

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    open import Cat.Categories.Sets
    open NaturalTransformation (opposite ℂ) (𝓢𝓮𝓽 ℓ')

    -- Restrict the functors to Presheafs.
    rawPresh : RawCategory (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
    rawPresh = record
      { Object = Presheaf ℂ
      ; Arrow = NaturalTransformation
      ; 𝟙 = λ {F} → identity F
      ; _∘_ = λ {F G H} → NT[_∘_] {F = F} {G = G} {H = H}
      }
    instance
      isCategory : IsCategory rawPresh
      isCategory = Fun.isCategory _ _

  Presh : Category (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  Category.raw        Presh = rawPresh
  Category.isCategory Presh = isCategory
