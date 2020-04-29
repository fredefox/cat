{-# OPTIONS --cubical --caching #-}
module Cat.Categories.Span where

open import Cat.Prelude as P hiding (_×_ ; fst ; snd)
open import Cat.Equivalence
open import Cat.Category

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb)
  (let module ℂ = Category ℂ) (𝒜 ℬ : ℂ.Object) where

  open P

  private
    module _ where
      raw : RawCategory _ _
      raw = record
        { Object = Σ[ X ∈ ℂ.Object ] ℂ.Arrow X 𝒜 × ℂ.Arrow X ℬ
        ; Arrow = λ{ (A , a0 , a1) (B , b0 , b1)
          → Σ[ f ∈ ℂ.Arrow A B ]
              (ℂ [ b0 ∘ f ] ≡ a0)
            × (ℂ [ b1 ∘ f ] ≡ a1)
            }
        ; identity = λ{ {X , f , g} → ℂ.identity {X} , ℂ.rightIdentity , ℂ.rightIdentity}
        ; _<<<_ = λ { {_ , a0 , a1} {_ , b0 , b1} {_ , c0 , c1} (f , f0 , f1) (g , g0 , g1)
          → (f ℂ.<<< g)
            , (begin
                ℂ [ c0 ∘ ℂ [ f ∘ g ] ] ≡⟨ ℂ.isAssociative ⟩
                ℂ [ ℂ [ c0 ∘ f ] ∘ g ] ≡⟨ cong (λ φ → ℂ [ φ ∘ g ]) f0 ⟩
                ℂ [ b0 ∘ g ] ≡⟨ g0 ⟩
                a0 ∎
              )
            , (begin
               ℂ [ c1 ∘ ℂ [ f ∘ g ] ] ≡⟨ ℂ.isAssociative ⟩
               ℂ [ ℂ [ c1 ∘ f ] ∘ g ] ≡⟨ cong (λ φ → ℂ [ φ ∘ g ]) f1 ⟩
               ℂ [ b1 ∘ g ] ≡⟨ g1 ⟩
                a1 ∎
              )
          }
        }

      module _ where
        open RawCategory raw

        propEqs : ∀ {X' : Object}{Y' : Object} (let X , xa , xb = X') (let Y , ya , yb = Y')
                    → (xy : ℂ.Arrow X Y) → isProp ((ℂ [ ya ∘ xy ] ≡ xa) × (ℂ [ yb ∘ xy ] ≡ xb))
        propEqs xs = propSig (ℂ.arrowsAreSets _ _) (\ _ → ℂ.arrowsAreSets _ _)

        arrowEq : {X Y : Object} {f g : Arrow X Y} → fst f ≡ fst g → f ≡ g
        arrowEq {X} {Y} {f} {g} p = λ i → p i , lemPropF propEqs (snd f) (snd g) p i

        isAssociative : IsAssociative
        isAssociative {f = f , f0 , f1} {g , g0 , g1} {h , h0 , h1} = arrowEq ℂ.isAssociative

        isIdentity : IsIdentity identity
        isIdentity {AA@(A , a0 , a1)} {BB@(B , b0 , b1)} {f , f0 , f1} = arrowEq ℂ.leftIdentity , arrowEq ℂ.rightIdentity

        arrowsAreSets : ArrowsAreSets
        arrowsAreSets {X , x0 , x1} {Y , y0 , y1}
          = setSig ℂ.arrowsAreSets λ a → propSet (propEqs _)

        isPreCat : IsPreCategory raw
        IsPreCategory.isAssociative isPreCat = isAssociative
        IsPreCategory.isIdentity    isPreCat = isIdentity
        IsPreCategory.arrowsAreSets isPreCat = arrowsAreSets

      open IsPreCategory isPreCat

      module _ {𝕏 𝕐 : Object} where
        open Σ 𝕏 renaming (fst to X ; snd to x)
        open Σ x renaming (fst to xa ; snd to xb)
        open Σ 𝕐 renaming (fst to Y ; snd to y)
        open Σ y renaming (fst to ya ; snd to yb)
        open import Cat.Equivalence using (composeIso) renaming (_≅_ to _≅_)

        -- The proof will be a sequence of isomorphisms between the
        -- following 4 types:
        T0 = ((X , xa , xb) ≡ (Y , ya , yb))
        T1 = (Σ[ p ∈ (X ≡ Y) ] (PathP (λ i → ℂ.Arrow (p i) 𝒜) xa ya) × (PathP (λ i → ℂ.Arrow (p i) ℬ) xb yb))
        T2 = Σ (X ℂ.≊ Y) (λ iso
            → let p = ℂ.isoToId iso
            in
            ( PathP (λ i → ℂ.Arrow (p i) 𝒜) xa ya)
            × PathP (λ i → ℂ.Arrow (p i) ℬ) xb yb
            )
        T3 = ((X , xa , xb) ≊ (Y , ya , yb))

        step0 : T0 ≅ T1
        step0
          = (λ p → cong fst p , cong (fst ∘ snd) p , cong (snd ∘ snd) p)
          -- , (λ x  → λ i → fst x i , (fst (snd x) i) , (snd (snd x) i))
          , (λ{ (p , q , r) → Σ≡ (p , λ i → q i , r i)})
          , funExt (λ{ p → refl})
          , funExt (λ{ (p , q , r) → refl})

        step1 : T1 ≅ T2
        step1
          = symIso
              (isoSigFst
                {A = (X ℂ.≊ Y)}
                {B = (X ≡ Y)}
                (ℂ.groupoidObject _ _)
                {Q = \ p → (PathP (λ i → ℂ.Arrow (p i) 𝒜) xa ya) × (PathP (λ i → ℂ.Arrow (p i) ℬ) xb yb)}
                ℂ.isoToId
                (symIso (_ , ℂ.asTypeIso {X} {Y}) .snd)
              )

        step2 : T2 ≅ T3
        step2
          = ( λ{ (iso@(f , f~ , inv-f) , p , q)
              → ( f  , sym (ℂ.domain-twist-sym  iso p) , sym (ℂ.domain-twist-sym iso q))
              , ( f~ , sym (ℂ.domain-twist      iso p) , sym (ℂ.domain-twist     iso q))
              , arrowEq (fst inv-f)
              , arrowEq (snd inv-f)
              }
            )
          , (λ{ (f , f~ , inv-f , inv-f~) →
            let
              iso : X ℂ.≊ Y
              iso = fst f , fst f~ , cong fst inv-f , cong fst inv-f~
              p : X ≡ Y
              p = ℂ.isoToId iso
              pA : ℂ.Arrow X 𝒜 ≡ ℂ.Arrow Y 𝒜
              pA = cong (λ x → ℂ.Arrow x 𝒜) p
              pB : ℂ.Arrow X ℬ ≡ ℂ.Arrow Y ℬ
              pB = cong (λ x → ℂ.Arrow x ℬ) p
              k0 = begin
                coe pB xb ≡⟨ ℂ.coe-dom iso ⟩
                xb ℂ.<<< fst f~ ≡⟨ snd (snd f~) ⟩
                yb ∎
              k1 = begin
                coe pA xa ≡⟨ ℂ.coe-dom iso ⟩
                xa ℂ.<<< fst f~ ≡⟨ fst (snd f~) ⟩
                ya ∎
            in iso , coe-lem-inv k1 , coe-lem-inv k0})
          , funExt (λ x → lemSig
              (λ x → propSig prop0 (λ _ → prop1))
              (Σ≡ (refl , ℂ.propIsomorphism _ _ _)))
          , funExt (λ{ (f , _) → lemSig propIsomorphism (Σ≡ (refl , propEqs _ _ _))})
            where
            prop0 : ∀ {x} → isProp (PathP (λ i → ℂ.Arrow (ℂ.isoToId x i) 𝒜) xa ya)
            prop0 {x} = pathJ (λ y p → ∀ x → isProp (PathP (λ i → ℂ.Arrow (p i) 𝒜) xa x)) (λ x → ℂ.arrowsAreSets _ _) (ℂ.isoToId x) ya
            prop1 : ∀ {x} → isProp (PathP (λ i → ℂ.Arrow (ℂ.isoToId x i) ℬ) xb yb)
            prop1 {x} = pathJ (λ y p → ∀ x → isProp (PathP (λ i → ℂ.Arrow (p i) ℬ) xb x)) (λ x → ℂ.arrowsAreSets _ _) (ℂ.isoToId x) yb
        -- One thing to watch out for here is that the isomorphisms going forwards
        -- must compose to give idToIso
        iso
          : ((X , xa , xb) ≡ (Y , ya , yb))
          ≅ ((X , xa , xb) ≊ (Y , ya , yb))
        iso = step0 ⊙ step1 ⊙ step2
          where
          infixl 5 _⊙_
          _⊙_ = composeIso
        equiv1
          : ((X , xa , xb) ≡ (Y , ya , yb))
          ≃ ((X , xa , xb) ≊ (Y , ya , yb))
        equiv1 = _ , fromIso _ _ (snd iso)

      univalent : Univalent
      univalent = univalenceFrom≃ equiv1

      isCat : IsCategory raw
      IsCategory.isPreCategory isCat = isPreCat
      IsCategory.univalent     isCat = univalent

  span : Category _ _
  span = record
    { raw = raw
    ; isCategory = isCat
    }
