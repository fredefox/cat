{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Fun where

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor

module Fun {ℓc ℓc' ℓd ℓd' : Level} (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  import Cat.Category.NaturalTransformation ℂ 𝔻
    as NaturalTransformation
  open NaturalTransformation public hiding (module Properties)
  open NaturalTransformation.Properties
  private
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻

    -- Functor categories. Objects are functors, arrows are natural transformations.
    raw : RawCategory (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
    RawCategory.Object raw = Functor ℂ 𝔻
    RawCategory.Arrow  raw = NaturalTransformation
    RawCategory.𝟙      raw {F} = identity F
    RawCategory._∘_    raw {F} {G} {H} = NT[_∘_] {F} {G} {H}

    open RawCategory raw
    open Univalence (λ {A} {B} {f} → isIdentity {F = A} {B} {f})

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

      done : isEquiv (A ≡ B) (A ≅ B) (Univalence.id-to-iso (λ { {A} {B} → isIdentity {F = A} {B}}) A B)
      done = {!gradLemma obverse reverse ve-re re-ve!}

    -- univalent : Univalent
    -- univalent = done

    isCategory : IsCategory raw
    IsCategory.isAssociative isCategory {A} {B} {C} {D} = isAssociative {A} {B} {C} {D}
    IsCategory.isIdentity    isCategory {A} {B} = isIdentity {A} {B}
    IsCategory.arrowsAreSets isCategory {F} {G} = naturalTransformationIsSet {F} {G}
    IsCategory.univalent     isCategory = {!!}

  Fun : Category (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  Category.raw        Fun = raw
  Category.isCategory Fun = isCategory

-- module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
--   private
--     open import Cat.Categories.Sets
--     open NaturalTransformation (opposite ℂ) (𝓢𝓮𝓽 ℓ')

--     -- Restrict the functors to Presheafs.
--     rawPresh : RawCategory (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
--     rawPresh = record
--       { Object = Presheaf ℂ
--       ; Arrow = NaturalTransformation
--       ; 𝟙 = λ {F} → identity F
--       ; _∘_ = λ {F G H} → NT[_∘_] {F = F} {G = G} {H = H}
--       }
--     instance
--       isCategory : IsCategory rawPresh
--       isCategory = Fun.isCategory _ _

--   Presh : Category (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
--   Category.raw        Presh = rawPresh
--   Category.isCategory Presh = isCategory
