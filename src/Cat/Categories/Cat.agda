{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cat.Categories.Cat where

open import Agda.Primitive
open import Cubical
open import Function
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

open import Cat.Category
open import Cat.Functor

-- Use co-patterns - they help with showing more understandable types in goals.
lift-eq : ∀ {ℓ} {A B : Set ℓ} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
fst (lift-eq a b i) = a i
snd (lift-eq a b i) = b i
--lift-eq a b = λ i → a i , b i



open Functor
open Category
module _ {ℓ ℓ' : Level} {A B : Category ℓ ℓ'} where
  lift-eq-functors : {f g : Functor A B}
    → (eq* : Functor.func* f ≡ Functor.func* g)
    → (eq→ : PathP (λ i → ∀ {x y} → Arrow A x y → Arrow B (eq* i x) (eq* i y))
    (func→ f) (func→ g))
    --        → (eq→ : Functor.func→ f ≡ {!!}) -- Functor.func→ g)
    -- Use PathP
    -- directly to show heterogeneous equalities by using previous
    -- equalities (i.e. continuous paths) to create new continuous paths.
    → (eqI : PathP (λ i → ∀ {c : A .Object} → eq→ i (A .𝟙 {c}) ≡ B .𝟙 {eq* i c})
    (ident f) (ident g))
    → (eqD : PathP (λ i → { c c' c'' : A .Object} {a : A .Arrow c c'} {a' : A .Arrow c' c''}
    → eq→ i (A ._⊕_ a' a) ≡ B ._⊕_ (eq→ i a') (eq→ i a))
    (distrib f) (distrib g))
    → f ≡ g
  lift-eq-functors eq* eq→ eqI eqD i = record { func* = eq* i ; func→ = eq→ i ; ident = eqI i ; distrib = eqD i }

-- The category of categories
module _ {ℓ ℓ' : Level} where
  private
    _⊛_ = functor-comp
    module _ {A B C D : Category ℓ ℓ'} {f : Functor A B} {g : Functor B C} {h : Functor C D} where
      postulate assc : h ⊛ (g ⊛ f) ≡ (h ⊛ g) ⊛ f
      -- assc = lift-eq-functors refl refl {!refl!} λ i j → {!!}

    module _ {A B : Category ℓ ℓ'} {f : Functor A B} where
      lem : (func* f) ∘ (func* (identity {C = A})) ≡ func* f
      lem = refl
      -- lemmm : func→ {C = A} {D = B} (f ⊛ identity) ≡ func→ f
      lemmm : PathP
        (λ i →
        {x y : Object A} → Arrow A x y → Arrow B (func* f x) (func* f y))
        (func→ (f ⊛ identity)) (func→ f)
      lemmm = refl
      postulate lemz : PathP (λ i → {c : A .Object} → PathP (λ _ → Arrow B (func* f c) (func* f c)) (func→ f (A .𝟙)) (B .𝟙))
                  (ident (f ⊛ identity)) (ident f)
      -- lemz = {!!}
      postulate ident-r : f ⊛ identity ≡ f
      -- ident-r = lift-eq-functors lem lemmm {!lemz!} {!!}
      postulate ident-l : identity ⊛ f ≡ f
      -- ident-l = lift-eq-functors lem lemmm {!refl!} {!!}

  CatCat : Category (lsuc (ℓ ⊔ ℓ')) (ℓ ⊔ ℓ')
  CatCat =
    record
      { Object = Category ℓ ℓ'
      ; Arrow = Functor
      ; 𝟙 = identity
      ; _⊕_ = functor-comp
      -- What gives here? Why can I not name the variables directly?
      ; assoc = λ {_ _ _ _ f g h} → assc {f = f} {g = g} {h = h}
      ; ident = ident-r , ident-l
      }

module _  {ℓ : Level} (C D : Category ℓ ℓ) where
  private
    proj₁ : Arrow CatCat (catProduct C D) C
    proj₁ = record { func* = fst ; func→ = fst ; ident = refl ; distrib = refl }

    proj₂ : Arrow CatCat (catProduct C D) D
    proj₂ = record { func* = snd ; func→ = snd ; ident = refl ; distrib = refl }

    module _ {X : Object (CatCat {ℓ} {ℓ})} (x₁ : Arrow CatCat X C) (x₂ : Arrow CatCat X D) where
      open Functor

      -- ident' : {c : Object X} → ((func→ x₁) {dom = c} (𝟙 X) , (func→ x₂) {dom = c} (𝟙 X)) ≡ 𝟙 (catProduct C D)
      -- ident' {c = c} = lift-eq (ident x₁) (ident x₂)

      x : Functor X (catProduct C D)
      x = record
        { func* = λ x → (func* x₁) x , (func* x₂) x
        ; func→ = λ x → func→ x₁ x , func→ x₂ x
        ; ident = lift-eq (ident x₁) (ident x₂)
        ; distrib = lift-eq (distrib x₁) (distrib x₂)
        }

      -- Need to "lift equality of functors"
      -- If I want to do this like I do it for pairs it's gonna be a pain.
      isUniqL : (CatCat ⊕ proj₁) x ≡ x₁
      isUniqL = lift-eq-functors refl refl {!!} {!!}

      isUniqR : (CatCat ⊕ proj₂) x ≡ x₂
      isUniqR = lift-eq-functors refl refl {!!} {!!}

      isUniq : (CatCat ⊕ proj₁) x ≡ x₁ × (CatCat ⊕ proj₂) x ≡ x₂
      isUniq = isUniqL , isUniqR

      uniq : ∃![ x ] ((CatCat ⊕ proj₁) x ≡ x₁ × (CatCat ⊕ proj₂) x ≡ x₂)
      uniq = x , isUniq

    instance
      isProduct : IsProduct CatCat proj₁ proj₂
      isProduct = uniq

  product : Product {ℂ = CatCat} C D
  product = record
    { obj = catProduct C D
    ; proj₁ = proj₁
    ; proj₂ = proj₂
    }
