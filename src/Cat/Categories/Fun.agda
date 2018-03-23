{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Fun where

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.NaturalTransformation

module Fun {ℓc ℓc' ℓd ℓd' : Level} (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  module NT = NaturalTransformation ℂ 𝔻
  open NT public
  private
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻
  private
    module _ {A B C D : Functor ℂ 𝔻} {θNT : NaturalTransformation A B}
      {ηNT : NaturalTransformation B C} {ζNT : NaturalTransformation C D} where
      open Σ θNT renaming (proj₁ to θ ; proj₂ to θNat)
      open Σ ηNT renaming (proj₁ to η ; proj₂ to ηNat)
      open Σ ζNT renaming (proj₁ to ζ ; proj₂ to ζNat)
      private
        L : NaturalTransformation A D
        L = (NT[_∘_] {A} {C} {D} ζNT (NT[_∘_] {A} {B} {C} ηNT θNT))
        R : NaturalTransformation A D
        R = (NT[_∘_] {A} {B} {D} (NT[_∘_] {B} {C} {D} ζNT ηNT) θNT)
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
        𝔻 [ f' C ∘ 𝔻.𝟙 ]  ≡⟨ 𝔻.rightIdentity ⟩
        f' C ∎
      eq-l : ∀ C → (𝔻 [ identityTrans B C ∘ f' C ]) ≡ f' C
      eq-l C = 𝔻.leftIdentity
      ident-r : (NT[_∘_] {A} {A} {B} f (NT.identity A)) ≡ f
      ident-r = lemSig allNatural _ _ (funExt eq-r)
      ident-l : (NT[_∘_] {A} {B} {B} (NT.identity B) f) ≡ f
      ident-l = lemSig allNatural _ _ (funExt eq-l)
      isIdentity
        : (NT[_∘_] {A} {B} {B} (NT.identity B) f) ≡ f
        × (NT[_∘_] {A} {A} {B} f (NT.identity A)) ≡ f
      isIdentity = ident-l , ident-r
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
    module _ (F : Functor ℂ 𝔻) where
      center : Σ[ G ∈ Object ] (F ≅ G)
      center = F , id-to-iso F F refl

      open Σ center renaming (proj₂ to isoF)

      module _ (cG : Σ[ G ∈ Object ] (F ≅ G)) where
        open Σ cG     renaming (proj₁ to G   ; proj₂ to isoG)
        module G = Functor G
        open Σ isoG   renaming (proj₁ to θNT ; proj₂ to invθNT)
        open Σ invθNT renaming (proj₁ to ηNT ; proj₂ to areInv)
        open Σ θNT    renaming (proj₁ to θ   ; proj₂ to θN)
        open Σ ηNT    renaming (proj₁ to η   ; proj₂ to ηN)
        open Σ areInv renaming (proj₁ to ve-re ; proj₂ to re-ve)

        -- f ~ Transformation G G
        -- f : (X : ℂ.Object) → 𝔻 [ G.omap X , G.omap X ]
        -- f X = T[ θ ∘ η ] X
        -- g = T[ η ∘ θ ] {!!}

        ntF : NaturalTransformation F F
        ntF = 𝟙 {A = F}

        ntG : NaturalTransformation G G
        ntG = 𝟙 {A = G}

        idFunctor = Functors.identity

        -- Dunno if this is the way to go, but if I can construct a an inverse of
        -- G that is also inverse of F (possibly by being propositionally equal to
        -- another functor F~)
        postulate
          G~ : Functor 𝔻 ℂ
        F~ : Functor 𝔻 ℂ
        F~ = G~
        postulate
          prop0 : F[ G~ ∘ G  ] ≡ idFunctor
          prop1 : F[ F  ∘ G~ ] ≡ idFunctor

        lem : F[ F  ∘ F~ ] ≡ idFunctor
        lem = begin
          F[ F  ∘ F~ ] ≡⟨⟩
          F[ F  ∘ G~ ] ≡⟨ prop1 ⟩
          idFunctor ∎

        open import Cubical.Univalence
        p0 : F ≡ G
        p0 = begin
          F                              ≡⟨ sym Functors.rightIdentity ⟩
          F[ F           ∘ idFunctor ]   ≡⟨ cong (λ φ → F[ F ∘ φ ]) (sym prop0) ⟩
          F[ F           ∘ F[ G~ ∘ G ] ] ≡⟨ Functors.isAssociative {F = G} {G = G~} {H = F} ⟩
          F[ F[ F ∘ G~ ] ∘ G ]           ≡⟨⟩
          F[ F[ F ∘ F~ ] ∘ G ]           ≡⟨ cong (λ φ → F[ φ ∘ G ]) lem ⟩
          F[ idFunctor   ∘ G ]           ≡⟨ Functors.leftIdentity ⟩
          G ∎

        p1 : (λ i → Σ (Arrow F (p0 i)) (Isomorphism {A = F} {B = p0 i})) [ isoF ≡ isoG ]
        p1 = {!!}

        isContractible : (F , isoF) ≡ (G , isoG)
        isContractible i = p0 i , p1 i

      univalent[Contr] : isContr (Σ[ G ∈ Object ] (F ≅ G))
      univalent[Contr] = center , isContractible

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
