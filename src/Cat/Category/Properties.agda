{-# OPTIONS --allow-unsolved-metas --cubical #-}

module Cat.Category.Properties where

open import Agda.Primitive
open import Data.Product
open import Cubical

open import Cat.Category
open import Cat.Functor
open import Cat.Categories.Sets
open import Cat.Equality
open Equality.Data.Product

module _ {ℓ ℓ' : Level} {ℂ : Category ℓ ℓ'} { A B : ℂ .Category.Object } {X : ℂ .Category.Object} (f : ℂ .Category.Arrow A B) where
  open Category ℂ
  open IsCategory (isCategory)

  iso-is-epi : Isomorphism f → Epimorphism {X = X} f
  iso-is-epi (f- , left-inv , right-inv) g₀ g₁ eq = begin
    g₀              ≡⟨ sym (proj₁ ident) ⟩
    g₀ ∘ 𝟙          ≡⟨ cong (_∘_ g₀) (sym right-inv) ⟩
    g₀ ∘ (f ∘ f-)   ≡⟨ assoc ⟩
    (g₀ ∘ f) ∘ f-   ≡⟨ cong (λ φ → φ ∘ f-) eq ⟩
    (g₁ ∘ f) ∘ f-   ≡⟨ sym assoc ⟩
    g₁ ∘ (f ∘ f-)   ≡⟨ cong (_∘_ g₁) right-inv ⟩
    g₁ ∘ 𝟙          ≡⟨ proj₁ ident ⟩
    g₁              ∎

  iso-is-mono : Isomorphism f → Monomorphism {X = X} f
  iso-is-mono (f- , (left-inv , right-inv)) g₀ g₁ eq =
    begin
    g₀            ≡⟨ sym (proj₂ ident) ⟩
    𝟙 ∘ g₀        ≡⟨ cong (λ φ → φ ∘ g₀) (sym left-inv) ⟩
    (f- ∘ f) ∘ g₀ ≡⟨ sym assoc ⟩
    f- ∘ (f ∘ g₀) ≡⟨ cong (_∘_ f-) eq ⟩
    f- ∘ (f ∘ g₁) ≡⟨ assoc ⟩
    (f- ∘ f) ∘ g₁ ≡⟨ cong (λ φ → φ ∘ g₁) left-inv ⟩
    𝟙 ∘ g₁        ≡⟨ proj₂ ident ⟩
    g₁            ∎

  iso-is-epi-mono : Isomorphism f → Epimorphism {X = X} f × Monomorphism {X = X} f
  iso-is-epi-mono iso = iso-is-epi iso , iso-is-mono iso

{-
epi-mono-is-not-iso : ∀ {ℓ ℓ'} → ¬ ((ℂ : Category {ℓ} {ℓ'}) {A B X : Object ℂ} (f : Arrow ℂ A B ) → Epimorphism {ℂ = ℂ} {X = X} f → Monomorphism {ℂ = ℂ} {X = X} f → Isomorphism {ℂ = ℂ} f)
epi-mono-is-not-iso f =
  let k = f {!!} {!!} {!!} {!!}
  in {!!}
-}

open import Cat.Category
open Category
open import Cat.Functor
open Functor

-- module _ {ℓ : Level} {ℂ : Category ℓ ℓ}
--   {isSObj : isSet (ℂ .Object)}
--   {isz2 : ∀ {ℓ} → {A B : Set ℓ} → isSet (Sets [ A , B ])} where
--   -- open import Cat.Categories.Cat using (Cat)
--   open import Cat.Categories.Fun
--   open import Cat.Categories.Sets
--   -- module Cat = Cat.Categories.Cat
--   open Exponential
--   private
--     Catℓ = Cat ℓ ℓ
--     prshf = presheaf {ℂ = ℂ}
--     module ℂ = IsCategory (ℂ .isCategory)

--     -- Exp : Set (lsuc (lsuc ℓ))
--     -- Exp = Exponential (Cat (lsuc ℓ) ℓ)
--     --   Sets (Opposite ℂ)

--     _⇑_ : (A B : Catℓ .Object) → Catℓ .Object
--     A ⇑ B = (exponent A B) .obj
--       where
--         open HasExponentials (Cat.hasExponentials ℓ)

--     module _ {A B : ℂ .Object} (f : ℂ .Arrow A B) where
--       :func→: : NaturalTransformation (prshf A) (prshf B)
--       :func→: = (λ C x → ℂ [ f ∘ x ]) , λ f₁ → funExt λ _ → ℂ.assoc

--     module _ {c : ℂ .Object} where
--       eqTrans : (λ _ → Transformation (prshf c) (prshf c))
--         [ (λ _ x → ℂ [ ℂ .𝟙 ∘ x ]) ≡ identityTrans (prshf c) ]
--       eqTrans = funExt λ x → funExt λ x → ℂ.ident .proj₂

--       eqNat : (λ i → Natural (prshf c) (prshf c) (eqTrans i))
--         [(λ _ → funExt (λ _ → ℂ.assoc)) ≡ identityNatural (prshf c)]
--       eqNat = λ i {A} {B} f →
--         let
--          open IsCategory (Sets .isCategory)
--          lemm : (Sets [ eqTrans i B ∘ prshf c .func→ f ]) ≡
--            (Sets [ prshf c .func→ f ∘ eqTrans i A ])
--          lemm = {!!}
--          lem : (λ _ → Sets [ Functor.func* (prshf c) A , prshf c .func* B ])
--                 [ Sets [ eqTrans i B ∘ prshf c .func→ f ]
--                 ≡ Sets [ prshf c .func→ f ∘ eqTrans i A ] ]
--          lem
--           = isz2 _ _ lemm _ i
--             -- (Sets [ eqTrans i B ∘ prshf c .func→ f ])
--             -- (Sets [ prshf c .func→ f ∘ eqTrans i A ])
--             -- lemm
--             -- _ i
--         in
--           lem
--       -- eqNat = λ {A} {B} i ℂ[B,A] i' ℂ[A,c] →
--       --   let
--       --     k : ℂ [ {!!} , {!!} ]
--       --     k = ℂ[A,c]
--       --   in {!ℂ [ ? ∘ ? ]!}

--       :ident: : (:func→: (ℂ .𝟙 {c})) ≡ (Fun .𝟙 {o = prshf c})
--       :ident: = Σ≡ eqTrans eqNat

--   yoneda : Functor ℂ (Fun {ℂ = Opposite ℂ} {𝔻 = Sets {ℓ}})
--   yoneda = record
--     { func* = prshf
--     ; func→ = :func→:
--     ; isFunctor = record
--       { ident = :ident:
--       ; distrib = {!!}
--       }
--     }
