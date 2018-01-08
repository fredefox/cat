{-# OPTIONS --cubical #-}

module Category where

open import Agda.Primitive
open import Data.Unit.Base
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Empty
open import Function

open import Cubical

postulate undefined : {ℓ : Level} → {A : Set ℓ} → A

record Category {ℓ ℓ'} : Set (lsuc (ℓ' ⊔ ℓ)) where
  constructor category
  field
    Object : Set ℓ
    Arrow  : Object → Object → Set ℓ'
    𝟙      : {o : Object} → Arrow o o
    _⊕_    : { a b c : Object } → Arrow b c → Arrow a b → Arrow a c
    assoc : { A B C D : Object } { f : Arrow A B } { g : Arrow B C } { h : Arrow C D }
      → h ⊕ (g ⊕ f) ≡ (h ⊕ g) ⊕ f
    ident  : { A B : Object } { f : Arrow A B }
      → f ⊕ 𝟙 ≡ f × 𝟙 ⊕ f ≡ f
  infixl 45 _⊕_
  domain : { a b : Object } → Arrow a b → Object
  domain {a = a} _ = a
  codomain : { a b : Object } → Arrow a b → Object
  codomain {b = b} _ = b

open Category public

record Functor {ℓc ℓc' ℓd ℓd'} (C : Category {ℓc} {ℓc'}) (D : Category {ℓd} {ℓd'})
  : Set (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') where
  constructor functor
  private
    open module C = Category C
    open module D = Category D
  field
    func* : C.Object → D.Object
    func→ : {dom cod : C.Object} → C.Arrow dom cod → D.Arrow (func* dom) (func* cod)
    ident   : { c : C.Object } → func→ (C.𝟙 {c}) ≡ D.𝟙 {func* c}
    -- TODO: Avoid use of ugly explicit arguments somehow.
    -- This guy managed to do it:
    --    https://github.com/copumpkin/categories/blob/master/Categories/Functor/Core.agda
    distrib : { c c' c'' : C.Object} {a : C.Arrow c c'} {a' : C.Arrow c' c''}
      → func→ (a' C.⊕ a) ≡ func→ a' D.⊕ func→ a

module _ {ℓ ℓ' : Level} {A B C : Category {ℓ} {ℓ'}} (F : Functor B C) (G : Functor A B) where
  private
    open module F = Functor F
    open module G = Functor G
    open module A = Category A
    open module B = Category B
    open module C = Category C

    F* = F.func*
    F→ = F.func→
    G* = G.func*
    G→ = G.func→
    module _ {a0 a1 a2 : A.Object} {α0 : A.Arrow a0 a1} {α1 : A.Arrow a1 a2} where

      dist : (F→ ∘ G→) (α1 A.⊕ α0) ≡ (F→ ∘ G→) α1 C.⊕ (F→ ∘ G→) α0
      dist = begin
        (F→ ∘ G→) (α1 A.⊕ α0)         ≡⟨ refl ⟩
        F→ (G→ (α1 A.⊕ α0))           ≡⟨ cong F→ G.distrib ⟩
        F→ ((G→ α1) B.⊕ (G→ α0))      ≡⟨ F.distrib ⟩
        (F→ ∘ G→) α1 C.⊕ (F→ ∘ G→) α0 ∎

  functor-comp : Functor A C
  functor-comp =
    record
      { func* = F* ∘ G*
      ; func→ = F→ ∘ G→
      ; ident = begin
        (F→ ∘ G→) (A.𝟙) ≡⟨ refl ⟩
        F→ (G→ (A.𝟙))   ≡⟨ cong F→ G.ident ⟩
        F→ (B.𝟙)        ≡⟨ F.ident ⟩
        C.𝟙             ∎
      ; distrib = dist
      }

-- The identity functor
identity : {ℓ ℓ' : Level} → {C : Category {ℓ} {ℓ'}} → Functor C C
-- Identity = record { F* = λ x → x ; F→ = λ x → x ; ident = refl ; distrib = refl }
identity = functor (λ x → x) (λ x → x) (refl) (refl)

module _ {ℓ ℓ' : Level} {ℂ : Category {ℓ} {ℓ'}} { A B : Object ℂ } where
  private
    open module ℂ = Category ℂ
    _+_ = ℂ._⊕_

  Isomorphism : (f : ℂ.Arrow A B) → Set ℓ'
  Isomorphism f = Σ[ g ∈ ℂ.Arrow B A ] g + f ≡ ℂ.𝟙 × f + g ≡ ℂ.𝟙

  Epimorphism : {X : ℂ.Object } → (f : ℂ.Arrow A B) → Set ℓ'
  Epimorphism {X} f = ( g₀ g₁ : ℂ.Arrow B X ) → g₀ + f ≡ g₁ + f → g₀ ≡ g₁

  Monomorphism : {X : ℂ.Object} → (f : ℂ.Arrow A B) → Set ℓ'
  Monomorphism {X} f = ( g₀ g₁ : ℂ.Arrow X A ) → f + g₀ ≡ f + g₁ → g₀ ≡ g₁

  iso-is-epi : ∀ {X} (f : ℂ.Arrow A B) → Isomorphism f → Epimorphism {X = X} f
  -- Idea: Pre-compose with f- on both sides of the equality of eq to get
  -- g₀ + f + f- ≡ g₁ + f + f-
  -- which by left-inv reduces to the goal.
  iso-is-epi f (f- , left-inv , right-inv) g₀ g₁ eq =
     trans (sym (fst ℂ.ident))
       ( trans (cong (_+_ g₀) (sym right-inv))
         ( trans ℂ.assoc
           ( trans (cong (λ x → x + f-) eq)
             ( trans (sym ℂ.assoc)
               ( trans (cong (_+_ g₁) right-inv) (fst ℂ.ident))
             )
           )
         )
       )

  iso-is-mono : ∀ {X} (f : ℂ.Arrow A B ) → Isomorphism f → Monomorphism {X = X} f
  -- For the next goal we do something similar: Post-compose with f- and use
  -- right-inv to get the goal.
  iso-is-mono f (f- , (left-inv , right-inv)) g₀ g₁ eq =
    trans (sym (snd ℂ.ident))
      ( trans (cong (λ x → x + g₀) (sym left-inv))
        ( trans (sym ℂ.assoc)
          ( trans (cong (_+_ f-) eq)
            ( trans ℂ.assoc
              ( trans (cong (λ x → x + g₁) left-inv) (snd ℂ.ident)
              )
            )
          )
        )
      )

  iso-is-epi-mono : ∀ {X} (f : ℂ.Arrow A B ) → Isomorphism f → Epimorphism {X = X} f × Monomorphism {X = X} f
  iso-is-epi-mono f iso = iso-is-epi f iso , iso-is-mono f iso

{-
epi-mono-is-not-iso : ∀ {ℓ ℓ'} → ¬ ((ℂ : Category {ℓ} {ℓ'}) {A B X : Object ℂ} (f : Arrow ℂ A B ) → Epimorphism {ℂ = ℂ} {X = X} f → Monomorphism {ℂ = ℂ} {X = X} f → Isomorphism {ℂ = ℂ} f)
epi-mono-is-not-iso f =
  let k = f {!!} {!!} {!!} {!!}
  in {!!}
-}

-- Isomorphism of objects
_≅_ : { ℓ ℓ' : Level } → { ℂ : Category {ℓ} {ℓ'} } → ( A B : Object ℂ ) → Set ℓ'
_≅_ {ℂ = ℂ} A B = Σ[ f ∈ ℂ.Arrow A B ] (Isomorphism {ℂ = ℂ} f)
  where
    open module ℂ = Category ℂ

Product : {ℓ : Level} → ( C D : Category {ℓ} {ℓ} ) → Category {ℓ} {ℓ}
Product C D =
  record
    { Object = C.Object × D.Object
    ; Arrow = λ { (c , d) (c' , d') →
      let carr = C.Arrow c c'
          darr = D.Arrow d d'
      in carr × darr}
    ; 𝟙 = C.𝟙 , D.𝟙
    ; _⊕_ = λ { (bc∈C , bc∈D) (ab∈C , ab∈D) → bc∈C C.⊕ ab∈C , bc∈D D.⊕ ab∈D}
    ; assoc = eqpair C.assoc D.assoc
    ; ident =
      let (Cl , Cr) = C.ident
          (Dl , Dr) = D.ident
      in eqpair Cl Dl , eqpair Cr Dr
    }
  where
    open module C = Category C
    open module D = Category D
    -- Two pairs are equal if their components are equal.
    eqpair : {ℓ : Level} → { A : Set ℓ } → { B : Set ℓ } → { a a' : A } → { b b' : B } → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
    eqpair {a = a} {b = b} eqa eqb = subst eqa (subst eqb (refl {x = (a , b)}))

Opposite : ∀ {ℓ ℓ'} → Category {ℓ} {ℓ'} → Category {ℓ} {ℓ'}
Opposite ℂ =
  record
    { Object = ℂ.Object
    ; Arrow = λ A B → ℂ.Arrow B A
    ; 𝟙 = ℂ.𝟙
    ; _⊕_ = λ g f → f ℂ.⊕ g
    ; assoc = sym ℂ.assoc
    ; ident = swap ℂ.ident
    }
  where
    open module ℂ = Category ℂ

Hom : {ℓ ℓ' : Level} → {ℂ : Category {ℓ} {ℓ'}} → (A B : Object ℂ) → Set ℓ'
Hom {ℂ = ℂ} A B = Arrow ℂ A B

module _ {ℓ ℓ' : Level} {ℂ : Category {ℓ} {ℓ'}} where
  private
    Obj = Object ℂ
    Arr = Arrow ℂ
    _+_ = _⊕_ ℂ

  HomFromArrow : (A : Obj) → {B B' : Obj} → (g : Arr B B')
    → Hom {ℂ = ℂ} A B → Hom {ℂ = ℂ} A B'
  HomFromArrow _A g = λ f → g + f
