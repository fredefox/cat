{-# OPTIONS --cubical #-}
module Cat.Category.Functor where

open import Agda.Primitive
open import Function

open import Cubical
open import Cubical.NType.Properties using (lemPropF)

open import Cat.Category

open Category hiding (_∘_ ; raw ; IsIdentity)

module _ {ℓc ℓc' ℓd ℓd'}
    (ℂ : Category ℓc ℓc')
    (𝔻 : Category ℓd ℓd')
    where

  private
    ℓ = ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd'
    𝓤 = Set ℓ

  Omap = Object ℂ → Object 𝔻
  Fmap : Omap → Set _
  Fmap omap = ∀ {A B}
    → ℂ [ A , B ] → 𝔻 [ omap A , omap B ]
  record RawFunctor : 𝓤 where
    field
      omap : Object ℂ → Object 𝔻
      fmap : ∀ {A B} → ℂ [ A , B ] → 𝔻 [ omap A , omap B ]

    IsIdentity : Set _
    IsIdentity = {A : Object ℂ} → fmap (𝟙 ℂ {A}) ≡ 𝟙 𝔻 {omap A}

    IsDistributive : Set _
    IsDistributive = {A B C : Object ℂ} {f : ℂ [ A , B ]} {g : ℂ [ B , C ]}
      → fmap (ℂ [ g ∘ f ]) ≡ 𝔻 [ fmap g ∘ fmap f ]

  -- | Equality principle for raw functors
  --
  -- The type of `fmap` depend on the value of `omap`. We can wrap this up
  -- into an equality principle for this type like is done for e.g. `Σ` using
  -- `pathJ`.
  module _ {x y : RawFunctor} where
    open RawFunctor
    private
      P : (omap' : Omap) → (eq : omap x ≡ omap') → Set _
      P y eq = (fmap' : Fmap y) → (λ i → Fmap (eq i))
        [ fmap x ≡ fmap' ]
    module _
        (eq : (λ i → Omap) [ omap x ≡ omap y ])
        (kk : P (omap x) refl)
        where
      private
        p : P (omap y) eq
        p = pathJ P kk (omap y) eq
        eq→ : (λ i → Fmap (eq i)) [ fmap x ≡ fmap y ]
        eq→ = p (fmap y)
      RawFunctor≡ : x ≡ y
      omap (RawFunctor≡ i) = eq  i
      fmap (RawFunctor≡ i) = eq→ i

  record IsFunctor (F : RawFunctor) : 𝓤 where
    open RawFunctor F public
    field
      -- FIXME Really ought to be preserves identity or something like this.
      isIdentity : IsIdentity
      isDistributive : IsDistributive

  record Functor : Set (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') where
    field
      raw : RawFunctor
      {{isFunctor}} : IsFunctor raw

    open IsFunctor isFunctor public

EndoFunctor : ∀ {ℓa ℓb} (ℂ : Category ℓa ℓb) → Set _
EndoFunctor ℂ = Functor ℂ ℂ

module _
    {ℓa ℓb : Level}
    {ℂ 𝔻 : Category ℓa ℓb}
    (F : RawFunctor ℂ 𝔻)
    where
  private
    module 𝔻 = Category 𝔻

  propIsFunctor : isProp (IsFunctor _ _ F)
  propIsFunctor isF0 isF1 i = record
    { isIdentity     = 𝔻.arrowsAreSets _ _ isF0.isIdentity     isF1.isIdentity     i
    ; isDistributive = 𝔻.arrowsAreSets _ _ isF0.isDistributive isF1.isDistributive i
    }
    where
      module isF0 = IsFunctor isF0
      module isF1 = IsFunctor isF1

-- Alternate version of above where `F` is indexed by an interval
module _
    {ℓa ℓb : Level}
    {ℂ 𝔻 : Category ℓa ℓb}
    {F : I → RawFunctor ℂ 𝔻}
    where
  private
    module 𝔻 = Category 𝔻
  IsProp' : {ℓ : Level} (A : I → Set ℓ) → Set ℓ
  IsProp' A = (a0 : A i0) (a1 : A i1) → A [ a0 ≡ a1 ]

  IsFunctorIsProp' : IsProp' λ i → IsFunctor _ _ (F i)
  IsFunctorIsProp' isF0 isF1 = lemPropF {B = IsFunctor ℂ 𝔻}
    (\ F → propIsFunctor F) (\ i → F i)

module _ {ℓ ℓ' : Level} {ℂ 𝔻 : Category ℓ ℓ'} where
  open Functor
  Functor≡ : {F G : Functor ℂ 𝔻}
    → Functor.raw F ≡ Functor.raw G
    → F ≡ G
  Functor.raw       (Functor≡ eq i) = eq i
  Functor.isFunctor (Functor≡ {F} {G} eq i)
    = res i
    where
    res : (λ i →  IsFunctor ℂ 𝔻 (eq i)) [ isFunctor F ≡ isFunctor G ]
    res = IsFunctorIsProp' (isFunctor F) (isFunctor G)

module _ {ℓ ℓ' : Level} {A B C : Category ℓ ℓ'} (F : Functor B C) (G : Functor A B) where
  private
    module F = Functor F
    module G = Functor G
    module _ {a0 a1 a2 : Object A} {α0 : A [ a0 , a1 ]} {α1 : A [ a1 , a2 ]} where
      dist : (F.fmap ∘ G.fmap) (A [ α1 ∘ α0 ]) ≡ C [ (F.fmap ∘ G.fmap) α1 ∘ (F.fmap ∘ G.fmap) α0 ]
      dist = begin
        (F.fmap ∘ G.fmap) (A [ α1 ∘ α0 ])
          ≡⟨ refl ⟩
        F.fmap (G.fmap (A [ α1 ∘ α0 ]))
          ≡⟨ cong F.fmap G.isDistributive ⟩
        F.fmap (B [ G.fmap α1 ∘ G.fmap α0 ])
          ≡⟨ F.isDistributive ⟩
        C [ (F.fmap ∘ G.fmap) α1 ∘ (F.fmap ∘ G.fmap) α0 ]
          ∎

    raw : RawFunctor A C
    RawFunctor.omap raw = F.omap ∘ G.omap
    RawFunctor.fmap raw = F.fmap ∘ G.fmap

    isFunctor : IsFunctor A C raw
    isFunctor = record
      { isIdentity = begin
        (F.fmap ∘ G.fmap) (𝟙 A) ≡⟨ refl ⟩
        F.fmap (G.fmap (𝟙 A))   ≡⟨ cong F.fmap (G.isIdentity)⟩
        F.fmap (𝟙 B)            ≡⟨ F.isIdentity ⟩
        𝟙 C                     ∎
      ; isDistributive = dist
      }

  F[_∘_] : Functor A C
  Functor.raw       F[_∘_] = raw
  Functor.isFunctor F[_∘_] = isFunctor

-- The identity functor
identity : ∀ {ℓ ℓ'} → {C : Category ℓ ℓ'} → Functor C C
identity = record
  { raw = record
    { omap = λ x → x
    ; fmap = λ x → x
    }
  ; isFunctor = record
    { isIdentity = refl
    ; isDistributive = refl
    }
  }
