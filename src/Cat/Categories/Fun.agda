{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Fun where

open import Agda.Primitive
open import Cubical
open import Function
open import Data.Product
import Cubical.GradLemma
module UIP = Cubical.GradLemma
open import Cubical.Sigma

open import Cat.Category
open import Cat.Category.Functor

open import Cat.Equality
open Equality.Data.Product

module _ {ℓc ℓc' ℓd ℓd' : Level} {ℂ : Category ℓc ℓc'} {𝔻 : Category ℓd ℓd'} where
  open Category hiding ( _∘_ ; Arrow )
  open Functor

  module _ (F G : Functor ℂ 𝔻) where
    private
      module F = Functor F
      module G = Functor G
    -- What do you call a non-natural tranformation?
    Transformation : Set (ℓc ⊔ ℓd')
    Transformation = (C : Object ℂ) → 𝔻 [ F.func* C , G.func* C ]

    Natural : Transformation → Set (ℓc ⊔ (ℓc' ⊔ ℓd'))
    Natural θ
      = {A B : Object ℂ}
      → (f : ℂ [ A , B ])
      → 𝔻 [ θ B ∘ F.func→ f ] ≡ 𝔻 [ G.func→ f ∘ θ A ]

    -- naturalIsProp : ∀ θ → isProp (Natural θ)
    -- naturalIsProp θ x y = {!funExt!}

    NaturalTransformation : Set (ℓc ⊔ ℓc' ⊔ ℓd')
    NaturalTransformation = Σ Transformation Natural

    -- NaturalTranformation : Set (ℓc ⊔ (ℓc' ⊔ ℓd'))
    -- NaturalTranformation = ∀ (θ : Transformation) {A B : ℂ .Object} → (f : ℂ .Arrow A B) → 𝔻 ._⊕_ (θ B) (F .func→ f) ≡ 𝔻 ._⊕_ (G .func→ f) (θ A)

    NaturalTransformation≡ : {α β : NaturalTransformation}
      → (eq₁ : α .proj₁ ≡ β .proj₁)
      → (eq₂ : PathP
          (λ i → {A B : Object ℂ} (f : ℂ [ A , B ])
            → 𝔻 [ eq₁ i B ∘ F.func→ f ]
            ≡ 𝔻 [ G.func→ f ∘ eq₁ i A ])
        (α .proj₂) (β .proj₂))
      → α ≡ β
    NaturalTransformation≡ eq₁ eq₂ i = eq₁ i , eq₂ i

  identityTrans : (F : Functor ℂ 𝔻) → Transformation F F
  identityTrans F C = 𝟙 𝔻

  identityNatural : (F : Functor ℂ 𝔻) → Natural F F (identityTrans F)
  identityNatural F {A = A} {B = B} f = begin
    𝔻 [ identityTrans F B ∘ F→ f ]  ≡⟨⟩
    𝔻 [ 𝟙 𝔻 ∘  F→ f ]              ≡⟨ proj₂ 𝔻.ident ⟩
    F→ f                            ≡⟨ sym (proj₁ 𝔻.ident) ⟩
    𝔻 [ F→ f ∘ 𝟙 𝔻 ]               ≡⟨⟩
    𝔻 [ F→ f ∘ identityTrans F A ]  ∎
    where
      module F = Functor F
      F→ = F.func→
      module 𝔻 = IsCategory (isCategory 𝔻)

  identityNat : (F : Functor ℂ 𝔻) → NaturalTransformation F F
  identityNat F = identityTrans F , identityNatural F

  module _ {F G H : Functor ℂ 𝔻} where
    private
      module F = Functor F
      module G = Functor G
      module H = Functor H
      _∘nt_ : Transformation G H → Transformation F G → Transformation F H
      (θ ∘nt η) C = 𝔻 [ θ C ∘ η C ]

    NatComp _:⊕:_ : NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
    proj₁ ((θ , _) :⊕: (η , _)) = θ ∘nt η
    proj₂ ((θ , θNat) :⊕: (η , ηNat)) {A} {B} f = begin
      𝔻 [ (θ ∘nt η) B ∘ F.func→ f ]     ≡⟨⟩
      𝔻 [ 𝔻 [ θ B ∘ η B ] ∘ F.func→ f ] ≡⟨ sym assoc ⟩
      𝔻 [ θ B ∘ 𝔻 [ η B ∘ F.func→ f ] ] ≡⟨ cong (λ φ → 𝔻 [ θ B ∘ φ ]) (ηNat f) ⟩
      𝔻 [ θ B ∘ 𝔻 [ G.func→ f ∘ η A ] ] ≡⟨ assoc ⟩
      𝔻 [ 𝔻 [ θ B ∘ G.func→ f ] ∘ η A ] ≡⟨ cong (λ φ → 𝔻 [ φ ∘ η A ]) (θNat f) ⟩
      𝔻 [ 𝔻 [ H.func→ f ∘ θ A ] ∘ η A ] ≡⟨ sym assoc ⟩
      𝔻 [ H.func→ f ∘ 𝔻 [ θ A ∘ η A ] ] ≡⟨⟩
      𝔻 [ H.func→ f ∘ (θ ∘nt η) A ]     ∎
      where
        open IsCategory (isCategory 𝔻)

    NatComp = _:⊕:_

  private
    module _ {F G : Functor ℂ 𝔻} where
      module 𝔻 = IsCategory (isCategory 𝔻)

      transformationIsSet : isSet (Transformation F G)
      transformationIsSet _ _ p q i j C = 𝔻.arrowIsSet _ _ (λ l → p l C)   (λ l → q l C) i j
      IsSet'   : {ℓ : Level} (A : Set ℓ) → Set ℓ
      IsSet' A = {x y : A} → (p q : (λ _ → A) [ x ≡ y ]) → p ≡ q

      -- Example 3.1.6. in HoTT states that
      -- If `B a` is a set for all `a : A` then `(a : A) → B a` is a set.
      -- In the case below `B = Natural F G`.

      -- naturalIsSet : (θ : Transformation F G) → IsSet' (Natural F G θ)
      -- naturalIsSet = {!!}

      -- isS : IsSet' ((θ : Transformation F G) → Natural F G θ)
      -- isS = {!!}

      naturalIsProp : (θ : Transformation F G) → isProp (Natural F G θ)
      naturalIsProp θ θNat θNat' = lem
        where
          lem : (λ _ → Natural F G θ) [ (λ f → θNat f) ≡ (λ f → θNat' f) ]
          lem = λ i f → 𝔻.arrowIsSet _ _ (θNat f) (θNat' f) i

      naturalTransformationIsSets : isSet (NaturalTransformation F G)
      naturalTransformationIsSets = {!sigPresSet!}
      -- f a b p q i = res
      --   where
      --     k : (θ : Transformation F G) → (xx yy : Natural F G θ) → xx ≡ yy
      --     k θ x y = let kk = naturalIsProp θ x y in {!!}
      --     res : a ≡ b
      --     res j = {!!} , {!!}
      -- -- naturalTransformationIsSets σa σb p q
      --   -- where
      --     -- -- In Andrea's proof `lemSig` he proves something very similiar to
      --     -- -- what I'm doing here, just for `Cubical.FromPathPrelude.Σ` rather
      --     -- -- than `Σ`. In that proof, he just needs *one* proof that the first
      --     -- -- components are equal - hence the arbitrary usage of `p` here.
      --     -- secretSauce : proj₁ σa ≡ proj₁ σb
      --     -- secretSauce i = proj₁ (p i)
      --     -- lemSig : σa ≡ σb
      --     -- lemSig i = (secretSauce i) , (UIP.lemPropF naturalIsProp secretSauce) {proj₂ σa} {proj₂ σb} i
      --     -- res : p ≡ q
      --     -- res = {!!}
      -- naturalTransformationIsSets (θ , θNat) (η , ηNat) p q i j
      --   = θ-η
      --   -- `i or `j - `p'` or `q'`?
      --   , {!!} -- UIP.lemPropF {B = Natural F G} (λ x → {!!}) {(θ , θNat)} {(η , ηNat)} {!!} i
      --   -- naturalIsSet i (λ i → {!!} i) {!!} {!!} i j
      --   -- naturalIsSet {!p''!} {!p''!} {!!} i j
      --   -- λ f k → 𝔻.arrowIsSet (λ l → proj₂ (p l) f k) (λ l → proj₂ (p l) f k) {!!} {!!}
      --   where
      --     θ≡η θ≡η' : θ ≡ η
      --     θ≡η  i = proj₁ (p i)
      --     θ≡η' i = proj₁ (q i)
      --     θ-η : Transformation F G
      --     θ-η = transformationIsSet _ _ θ≡η θ≡η' i j
      --     θNat≡ηNat  : (λ i → Natural F G (θ≡η  i)) [ θNat ≡ ηNat ]
      --     θNat≡ηNat  i = proj₂ (p i)
      --     θNat≡ηNat' : (λ i → Natural F G (θ≡η' i)) [ θNat ≡ ηNat ]
      --     θNat≡ηNat' i = proj₂ (q i)
      --     k  : Natural F G (θ≡η  i)
      --     k  = θNat≡ηNat  i
      --     k' : Natural F G (θ≡η' i)
      --     k' = θNat≡ηNat' i
      --     t : Natural F G θ-η
      --     t = naturalIsProp {!θ!} {!!} {!!} {!!}

    module _ {A B C D : Functor ℂ 𝔻} {θ' : NaturalTransformation A B}
      {η' : NaturalTransformation B C} {ζ' : NaturalTransformation C D} where
      private
        θ = proj₁ θ'
        η = proj₁ η'
        ζ = proj₁ ζ'
      _g⊕f_ = _:⊕:_ {A} {B} {C}
      _h⊕g_ = _:⊕:_ {B} {C} {D}
      :assoc: : (_:⊕:_ {A} {C} {D} ζ' (_:⊕:_ {A} {B} {C} η' θ')) ≡ (_:⊕:_ {A} {B} {D} (_:⊕:_ {B} {C} {D} ζ' η') θ')
      :assoc: = Σ≡ (funExt (λ _ → assoc)) {!!}
        where
          open IsCategory (isCategory 𝔻)

    module _ {A B : Functor ℂ 𝔻} {f : NaturalTransformation A B} where
      ident-r : (_:⊕:_ {A} {A} {B} f (identityNat A)) ≡ f
      ident-r = {!!}
      ident-l : (_:⊕:_ {A} {B} {B} (identityNat B) f) ≡ f
      ident-l = {!!}
      :ident:
        : (_:⊕:_ {A} {A} {B} f (identityNat A)) ≡ f
        × (_:⊕:_ {A} {B} {B} (identityNat B) f) ≡ f
      :ident: = ident-r , ident-l

  -- Functor categories. Objects are functors, arrows are natural transformations.
  RawFun : RawCategory (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  RawFun = record
    { Object = Functor ℂ 𝔻
    ; Arrow = NaturalTransformation
    ; 𝟙 = λ {F} → identityNat F
    ; _∘_ = λ {F G H} → _:⊕:_ {F} {G} {H}
    }

  instance
    :isCategory: : IsCategory RawFun
    :isCategory: = record
      { assoc = λ {A B C D} → :assoc: {A} {B} {C} {D}
      ; ident = λ {A B} → :ident: {A} {B}
      ; arrowIsSet = λ {F} {G} → naturalTransformationIsSets {F} {G}
      ; univalent = {!!}
      }

  Fun : Category (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  raw Fun = RawFun

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  open import Cat.Categories.Sets

  -- Restrict the functors to Presheafs.
  RawPresh : RawCategory (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  RawPresh = record
    { Object = Presheaf ℂ
    ; Arrow = NaturalTransformation
    ; 𝟙 = λ {F} → identityNat F
    ; _∘_ = λ {F G H} → NatComp {F = F} {G = G} {H = H}
    }
