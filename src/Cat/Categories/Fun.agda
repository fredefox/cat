{-# OPTIONS --allow-unsolved-metas --cubical --caching #-}
module Cat.Categories.Fun where

open import Cat.Prelude

open import Cat.Category
open import Cat.Category.Functor
import Cat.Category.NaturalTransformation
  as NaturalTransformation

module Fun {ℓc ℓc' ℓd ℓd' : Level} (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  open NaturalTransformation ℂ 𝔻 public hiding (module Properties)
  private
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻

    module _ where
      -- Functor categories. Objects are functors, arrows are natural transformations.
      raw : RawCategory (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
      RawCategory.Object   raw = Functor ℂ 𝔻
      RawCategory.Arrow    raw = NaturalTransformation
      RawCategory.identity raw {F} = identity F
      RawCategory._<<<_    raw {F} {G} {H} = NT[_∘_] {F} {G} {H}

    module _ where
      open RawCategory raw hiding (identity)
      open NaturalTransformation.Properties ℂ 𝔻

      isPreCategory : IsPreCategory raw
      IsPreCategory.isAssociative isPreCategory {A} {B} {C} {D} = isAssociative {A} {B} {C} {D}
      IsPreCategory.isIdentity    isPreCategory {A} {B} = isIdentity {A} {B}
      IsPreCategory.arrowsAreSets isPreCategory {F} {G} = naturalTransformationIsSet {F} {G}

    open IsPreCategory isPreCategory hiding (identity)

    module _ (F : Functor ℂ 𝔻) where
      center : Σ[ G ∈ Object ] (F ≅ G)
      center = F , idToIso F F refl

      open Σ center renaming (snd to isoF)

      module _ (cG : Σ[ G ∈ Object ] (F ≅ G)) where
        open Σ cG renaming (fst to G ; snd to isoG)
        module G = Functor G
        open Σ isoG   renaming (fst to θNT ; snd to invθNT)
        open Σ invθNT renaming (fst to ηNT ; snd to areInv)
        open Σ θNT    renaming (fst to θ   ; snd to θN)
        open Σ ηNT    renaming (fst to η   ; snd to ηN)
        open Σ areInv renaming (fst to ve-re ; snd to re-ve)

        -- f ~ Transformation G G
        -- f : (X : ℂ.Object) → 𝔻 [ G.omap X , G.omap X ]
        -- f X = T[ θ ∘ η ] X
        -- g = T[ η ∘ θ ] {!!}

        ntF : NaturalTransformation F F
        ntF = identity F

        ntG : NaturalTransformation G G
        ntG = identity G

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
        coeidentity : Transformation A B
        coeidentity X = coe coerceAB 𝔻.identity

        module _ {a b : ℂ.Object} (f : ℂ [ a , b ]) where
          nat' : 𝔻 [ coeidentity b ∘ A.fmap f ] ≡ 𝔻 [ B.fmap f ∘ coeidentity a ]
          nat' = begin
            (𝔻 [ coeidentity b ∘ A.fmap f ]) ≡⟨ {!!} ⟩
            (𝔻 [ B.fmap f ∘ coeidentity a ]) ∎

        transs : (i : I) → Transformation A (p i)
        transs = {!!}

        natt : (i : I) → Natural A (p i) {!!}
        natt = {!!}

        t : Natural A B coeidentity
        t = coe c (identityNatural A)
          where
          c : Natural A A (identityTrans A) ≡ Natural A B coeidentity
          c = begin
            Natural A A (identityTrans A) ≡⟨ (λ x → {!natt ?!}) ⟩
            Natural A B coeidentity ∎
          -- cong (λ φ → {!Natural A A (identityTrans A)!}) {!!}

        k : Natural A A (identityTrans A) → Natural A B coeidentity
        k n {a} {b} f = res
          where
          res : (𝔻 [ coeidentity b ∘ A.fmap f ]) ≡ (𝔻 [ B.fmap f ∘ coeidentity a ])
          res = {!!}

        nat : Natural A B coeidentity
        nat = nat'

        fromEq : NaturalTransformation A B
        fromEq = coeidentity , nat

    module _ {A B : Functor ℂ 𝔻} where
      obverse : A ≡ B → A ≅ B
      obverse p = res
        where
        ob  : Arrow A B
        ob = fromEq p
        re : Arrow B A
        re = fromEq (sym p)
        vr : _<<<_ {A = A} {B} {A} re ob ≡ identity A
        vr = {!!}
        rv : _<<<_ {A = B} {A} {B} ob re ≡ identity B
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

      done : isEquiv (A ≡ B) (A ≅ B) (idToIso A B)
      done = {!gradLemma obverse reverse ve-re re-ve!}

    univalent : Univalent
    univalent = {!done!}

    isCategory : IsCategory raw
    IsCategory.isPreCategory isCategory = isPreCategory
    IsCategory.univalent     isCategory = univalent

  Fun : Category (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  Category.raw        Fun = raw
  Category.isCategory Fun = isCategory

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    open import Cat.Categories.Sets
    open NaturalTransformation (opposite ℂ) (𝓢𝓮𝓽 ℓ')
    module K = Fun (opposite ℂ) (𝓢𝓮𝓽 ℓ')
    module F = Category K.Fun

    -- Restrict the functors to Presheafs.
    raw : RawCategory (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
    raw = record
      { Object = Presheaf ℂ
      ; Arrow = NaturalTransformation
      ; identity = λ {F} → identity F
      ; _<<<_ = λ {F G H} → NT[_∘_] {F = F} {G = G} {H = H}
      }

  --   isCategory : IsCategory raw
  --   isCategory = record
  --     { isAssociative =
  --       λ{ {A} {B} {C} {D} {f} {g} {h}
  --       → F.isAssociative {A} {B} {C} {D} {f} {g} {h}
  --       }
  --     ; isIdentity =
  --       λ{ {A} {B} {f}
  --       → F.isIdentity {A} {B} {f}
  --       }
  --     ; arrowsAreSets =
  --       λ{ {A} {B}
  --       → F.arrowsAreSets {A} {B}
  --       }
  --     ; univalent =
  --       λ{ {A} {B}
  --       → F.univalent {A} {B}
  --       }
  --     }

  -- Presh : Category (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  -- Category.raw        Presh = raw
  -- Category.isCategory Presh = isCategory
