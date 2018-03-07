{-# OPTIONS --cubical #-}
module Cat.Category.Functor where

open import Agda.Primitive
open import Cubical
open import Function

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
      func* : Object ℂ → Object 𝔻
      func→ : ∀ {A B} → ℂ [ A , B ] → 𝔻 [ func* A , func* B ]

    IsIdentity : Set _
    IsIdentity = {A : Object ℂ} → func→ (𝟙 ℂ {A}) ≡ 𝟙 𝔻 {func* A}

    IsDistributive : Set _
    IsDistributive = {A B C : Object ℂ} {f : ℂ [ A , B ]} {g : ℂ [ B , C ]}
      → func→ (ℂ [ g ∘ f ]) ≡ 𝔻 [ func→ g ∘ func→ f ]

  -- | Equality principle for raw functors
  --
  -- The type of `func→` depend on the value of `func*`. We can wrap this up
  -- into an equality principle for this type like is done for e.g. `Σ` using
  -- `pathJ`.
  module _ {x y : RawFunctor} where
    open RawFunctor
    private
      P : (omap : Omap) → (eq : func* x ≡ omap) → Set _
      P y eq = (fmap' : Fmap y) → (λ i → Fmap (eq i))
        [ func→ x ≡ fmap' ]
    module _
        (eq : (λ i → Omap) [ func* x ≡ func* y ])
        (kk : P (func* x) refl)
        where
      private
        p : P (func* y) eq
        p = pathJ P kk (func* y) eq
        eq→ : (λ i → Fmap (eq i)) [ func→ x ≡ func→ y ]
        eq→ = p (func→ y)
      RawFunctor≡ : x ≡ y
      func* (RawFunctor≡ i) = eq  i
      func→ (RawFunctor≡ i) = eq→ i

  record IsFunctor (F : RawFunctor) : 𝓤 where
    open RawFunctor F public
    field
      -- TODO Really ought to be preserves identity or something like this.
      isIdentity : IsIdentity
      isDistributive : IsDistributive

  record Functor : Set (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') where
    field
      raw : RawFunctor
      {{isFunctor}} : IsFunctor raw

    open IsFunctor isFunctor public

open Functor

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
    { isIdentity = 𝔻.arrowsAreSets _ _ isF0.isIdentity isF1.isIdentity i
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
    where
      open import Cubical.NType.Properties using (lemPropF)

module _ {ℓ ℓ' : Level} {ℂ 𝔻 : Category ℓ ℓ'} where
  Functor≡ : {F G : Functor ℂ 𝔻}
    → raw F ≡ raw G
    → F ≡ G
  raw       (Functor≡ eq i) = eq i
  isFunctor (Functor≡ {F} {G} eq i)
    = res i
    where
    res : (λ i →  IsFunctor ℂ 𝔻 (eq i)) [ isFunctor F ≡ isFunctor G ]
    res = IsFunctorIsProp' (isFunctor F) (isFunctor G)

module _ {ℓ ℓ' : Level} {A B C : Category ℓ ℓ'} (F : Functor B C) (G : Functor A B) where
  private
    F* = func* F
    F→ = func→ F
    G* = func* G
    G→ = func→ G
    module _ {a0 a1 a2 : Object A} {α0 : A [ a0 , a1 ]} {α1 : A [ a1 , a2 ]} where

      dist : (F→ ∘ G→) (A [ α1 ∘ α0 ]) ≡ C [ (F→ ∘ G→) α1 ∘ (F→ ∘ G→) α0 ]
      dist = begin
        (F→ ∘ G→) (A [ α1 ∘ α0 ])         ≡⟨ refl ⟩
        F→ (G→ (A [ α1 ∘ α0 ]))           ≡⟨ cong F→ (isDistributive G) ⟩
        F→ (B [ G→ α1 ∘ G→ α0 ])          ≡⟨ isDistributive F ⟩
        C [ (F→ ∘ G→) α1 ∘ (F→ ∘ G→) α0 ] ∎

    _∘fr_ : RawFunctor A C
    RawFunctor.func* _∘fr_ = F* ∘ G*
    RawFunctor.func→ _∘fr_ = F→ ∘ G→
    instance
      isFunctor' : IsFunctor A C _∘fr_
      isFunctor' = record
        { isIdentity = begin
          (F→ ∘ G→) (𝟙 A) ≡⟨ refl ⟩
          F→ (G→ (𝟙 A))   ≡⟨ cong F→ (isIdentity G)⟩
          F→ (𝟙 B)        ≡⟨ isIdentity F ⟩
          𝟙 C             ∎
        ; isDistributive = dist
        }

  F[_∘_] : Functor A C
  raw F[_∘_] = _∘fr_

-- The identity functor
identity : ∀ {ℓ ℓ'} → {C : Category ℓ ℓ'} → Functor C C
identity = record
  { raw = record
    { func* = λ x → x
    ; func→ = λ x → x
    }
  ; isFunctor = record
    { isIdentity = refl
    ; isDistributive = refl
    }
  }
