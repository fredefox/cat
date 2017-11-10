{-# OPTIONS --cubical #-}

module Category where

open import Agda.Primitive
open import Data.Unit.Base
open import Data.Product
open import Cubical.PathPrelude

postulate undefined : {ℓ : Level} → {A : Set ℓ} → A

record Category {ℓ ℓ'} : Set (lsuc (ℓ' ⊔ ℓ)) where
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
  dom : { a b : Object } → Arrow a b → Object
  dom {a = a} _ = a
  cod : { a b : Object } → Arrow a b → Object
  cod {b = b} _ = b

open Category public

record Functor {ℓc ℓc' ℓd ℓd'} (C : Category {ℓc} {ℓc'}) (D : Category {ℓd} {ℓd'})
  : Set (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') where
  private
    open module C = Category C
    open module D = Category D
  field
    F : C.Object → D.Object
    f : {c c' : C.Object} → C.Arrow c c' → D.Arrow (F c) (F c')
    ident   : { c : C.Object } → f (C.𝟙 {c}) ≡ D.𝟙 {F c}
    -- TODO: Avoid use of ugly explicit arguments somehow.
    -- This guy managed to do it:
    --    https://github.com/copumpkin/categories/blob/master/Categories/Functor/Core.agda
    distrib : { c c' c'' : C.Object} {a : C.Arrow c c'} {a' : C.Arrow c' c''}
      → f (a' C.⊕ a) ≡ f a' D.⊕ f a

FunctorComp : ∀ {ℓ ℓ'} {a b c : Category {ℓ} {ℓ'}} → Functor b c → Functor a b → Functor a c
FunctorComp {a = a} {b = b} {c = c} F G =
  record
    { F = F.F ∘ G.F
    ; f = F.f ∘ G.f
    ; ident = λ { {c = obj} →
      let --t : (F.f ∘ G.f) (𝟙 a) ≡ (𝟙 c)
          g-ident = G.ident
          k : F.f (G.f {c' = obj} (𝟙 a)) ≡ F.f (G.f (𝟙 a))
          k = refl {x = F.f (G.f (𝟙 a))}
          t : F.f (G.f (𝟙 a)) ≡ (𝟙 c)
          -- t = subst F.ident (subst G.ident k)
          t = undefined
      in t }
    ; distrib = undefined -- subst F.distrib (subst G.distrib refl)
    }
    where
      open module F = Functor F
      open module G = Functor G

-- The identity functor
Identity : {ℓ ℓ' : Level} → {C : Category {ℓ} {ℓ'}} → Functor C C
Identity = record { F = λ x → x ; f = λ x → x ; ident = refl ; distrib = refl }

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

data ⊥ : Set where

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → ⊥

{-
epi-mono-is-not-iso : ∀ {ℓ ℓ'} → ¬ ((ℂ : Category {ℓ} {ℓ'}) {A B X : Object ℂ} (f : Arrow ℂ A B ) → Epimorphism {ℂ = ℂ} {X = X} f → Monomorphism {ℂ = ℂ} {X = X} f → Isomorphism {ℂ = ℂ} f)
epi-mono-is-not-iso f =
  let k = f {!!} {!!} {!!} {!!}
  in {!!}
-}

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

CatCat : {ℓ ℓ' : Level} → Category {ℓ-suc (ℓ ⊔ ℓ')} {ℓ ⊔ ℓ'}
CatCat {ℓ} {ℓ'} =
  record
    { Object = Category {ℓ} {ℓ'}
    ; Arrow = Functor
    ; 𝟙 = Identity
    ; _⊕_ = FunctorComp
    ; assoc = undefined
    ; ident = λ { {f = f} →
      let eq : f ≡ f
          eq = refl
      in undefined , undefined}
    }

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
