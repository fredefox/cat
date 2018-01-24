{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cat.Categories.Cat where

open import Agda.Primitive
open import Cubical
open import Function
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

open import Cat.Category
open import Cat.Functor

-- Tip from Andrea:
-- Use co-patterns - they help with showing more understandable types in goals.
lift-eq : ∀ {ℓ} {A B : Set ℓ} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
fst (lift-eq a b i) = a i
snd (lift-eq a b i) = b i

eqpair : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} {a a' : A} {b b' : B}
  → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
eqpair eqa eqb i = eqa i , eqb i

open Functor
open Category
module _ {ℓ ℓ' : Level} {A B : Category ℓ ℓ'} where
  lift-eq-functors : {f g : Functor A B}
    → (eq* : f .func* ≡ g .func*)
    → (eq→ : PathP (λ i → ∀ {x y} → A .Arrow x y → B .Arrow (eq* i x) (eq* i y))
    (f .func→) (g .func→))
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
module _ (ℓ ℓ' : Level) where
  private
    module _ {A B C D : Category ℓ ℓ'} {f : Functor A B} {g : Functor B C} {h : Functor C D} where
      eq* : func* (h ∘f (g ∘f f)) ≡ func* ((h ∘f g) ∘f f)
      eq* = refl
      eq→ : PathP
        (λ i → {x y : A .Object} → A .Arrow x y → D .Arrow (eq* i x) (eq* i y))
        (func→ (h ∘f (g ∘f f))) (func→ ((h ∘f g) ∘f f))
      eq→ = refl
      id-l = (h ∘f (g ∘f f)) .ident -- = func→ (h ∘f (g ∘f f)) (𝟙 A) ≡ 𝟙 D
      id-r = ((h ∘f g) ∘f f) .ident -- = func→ ((h ∘f g) ∘f f) (𝟙 A) ≡ 𝟙 D
      postulate eqI : PathP
                 (λ i → ∀ {c : A .Object} → eq→ i (A .𝟙 {c}) ≡ D .𝟙 {eq* i c})
                 (ident ((h ∘f (g ∘f f))))
                 (ident ((h ∘f g) ∘f f))
      postulate eqD : PathP (λ i → { c c' c'' : A .Object} {a : A .Arrow c c'} {a' : A .Arrow c' c''}
                        → eq→ i (A ._⊕_ a' a) ≡ D ._⊕_ (eq→ i a') (eq→ i a))
                        (distrib (h ∘f (g ∘f f))) (distrib ((h ∘f g) ∘f f))
      -- eqD = {!!}

      assc : h ∘f (g ∘f f) ≡ (h ∘f g) ∘f f
      assc = lift-eq-functors eq* eq→ eqI eqD

    module _ {A B : Category ℓ ℓ'} {f : Functor A B} where
      lem : (func* f) ∘ (func* (identity {C = A})) ≡ func* f
      lem = refl
      -- lemmm : func→ {C = A} {D = B} (f ∘f identity) ≡ func→ f
      lemmm : PathP
        (λ i →
        {x y : Object A} → Arrow A x y → Arrow B (func* f x) (func* f y))
        (func→ (f ∘f identity)) (func→ f)
      lemmm = refl
      postulate lemz : PathP (λ i → {c : A .Object} → PathP (λ _ → Arrow B (func* f c) (func* f c)) (func→ f (A .𝟙)) (B .𝟙))
                  (ident (f ∘f identity)) (ident f)
      -- lemz = {!!}
      postulate ident-r : f ∘f identity ≡ f
      -- ident-r = lift-eq-functors lem lemmm {!lemz!} {!!}
      postulate ident-l : identity ∘f f ≡ f
      -- ident-l = lift-eq-functors lem lemmm {!refl!} {!!}

  Cat : Category (lsuc (ℓ ⊔ ℓ')) (ℓ ⊔ ℓ')
  Cat =
    record
      { Object = Category ℓ ℓ'
      ; Arrow = Functor
      ; 𝟙 = identity
      ; _⊕_ = _∘f_
      -- What gives here? Why can I not name the variables directly?
      ; isCategory = record
        { assoc = λ {_ _ _ _ f g h} → assc {f = f} {g = g} {h = h}
        ; ident = ident-r , ident-l
        }
      }

module _ {ℓ ℓ' : Level} where
  Catt = Cat ℓ ℓ'

  module _ (C D : Category ℓ ℓ') where
    private
      :Object: = C .Object × D .Object
      :Arrow:  : :Object: → :Object: → Set ℓ'
      :Arrow: (c , d) (c' , d') = Arrow C c c' × Arrow D d d'
      :𝟙: : {o : :Object:} → :Arrow: o o
      :𝟙: = C .𝟙 , D .𝟙
      _:⊕:_ :
        {a b c : :Object:} →
        :Arrow: b c →
        :Arrow: a b →
        :Arrow: a c
      _:⊕:_ = λ { (bc∈C , bc∈D) (ab∈C , ab∈D) → (C ._⊕_) bc∈C ab∈C , D ._⊕_ bc∈D ab∈D}

      instance
        :isCategory: : IsCategory :Object: :Arrow: :𝟙: _:⊕:_
        :isCategory: = record
          { assoc = eqpair C.assoc D.assoc
          ; ident
          = eqpair (fst C.ident) (fst D.ident)
          , eqpair (snd C.ident) (snd D.ident)
          }
          where
            open module C = IsCategory (C .isCategory)
            open module D = IsCategory (D .isCategory)

      :product: : Category ℓ ℓ'
      :product: = record
        { Object = :Object:
        ; Arrow = :Arrow:
        ; 𝟙 = :𝟙:
        ; _⊕_ = _:⊕:_
        }

      proj₁ : Arrow Catt :product: C
      proj₁ = record { func* = fst ; func→ = fst ; ident = refl ; distrib = refl }

      proj₂ : Arrow Catt :product: D
      proj₂ = record { func* = snd ; func→ = snd ; ident = refl ; distrib = refl }

      module _ {X : Object Catt} (x₁ : Arrow Catt X C) (x₂ : Arrow Catt X D) where
        open Functor

        -- ident' : {c : Object X} → ((func→ x₁) {dom = c} (𝟙 X) , (func→ x₂) {dom = c} (𝟙 X)) ≡ 𝟙 (catProduct C D)
        -- ident' {c = c} = lift-eq (ident x₁) (ident x₂)

        x : Functor X :product:
        x = record
          { func* = λ x → (func* x₁) x , (func* x₂) x
          ; func→ = λ x → func→ x₁ x , func→ x₂ x
          ; ident = lift-eq (ident x₁) (ident x₂)
          ; distrib = lift-eq (distrib x₁) (distrib x₂)
          }

        -- Need to "lift equality of functors"
        -- If I want to do this like I do it for pairs it's gonna be a pain.
        postulate isUniqL : (Catt ⊕ proj₁) x ≡ x₁
        -- isUniqL = lift-eq-functors refl refl {!!} {!!}

        postulate isUniqR : (Catt ⊕ proj₂) x ≡ x₂
        -- isUniqR = lift-eq-functors refl refl {!!} {!!}

        isUniq : (Catt ⊕ proj₁) x ≡ x₁ × (Catt ⊕ proj₂) x ≡ x₂
        isUniq = isUniqL , isUniqR

        uniq : ∃![ x ] ((Catt ⊕ proj₁) x ≡ x₁ × (Catt ⊕ proj₂) x ≡ x₂)
        uniq = x , isUniq

      instance
        isProduct : IsProduct Catt proj₁ proj₂
        isProduct = uniq

    product : Product {ℂ = Catt} C D
    product = record
      { obj = :product:
      ; proj₁ = proj₁
      ; proj₂ = proj₂
      }

module _ {ℓ ℓ' : Level} where
  open Category
  instance
    CatHasProducts : HasProducts (Cat ℓ ℓ')
    CatHasProducts = record { product = product }

-- Basically proves that `Cat ℓ ℓ` is cartesian closed.
module _ {ℓ : Level} {ℂ : Category ℓ ℓ} {{_ : HasProducts (Opposite ℂ)}} where
  open Data.Product
  open Category

  private
    Catℓ : Category (lsuc (ℓ ⊔ ℓ)) (ℓ ⊔ ℓ)
    Catℓ = Cat ℓ ℓ
    open import Cat.Categories.Fun
    open Functor
    module _ (ℂ 𝔻 : Category ℓ ℓ) where
      private
        :obj: : Cat ℓ ℓ .Object
        :obj: = Fun {ℂ = ℂ} {𝔻 = 𝔻}

        :func*: : Functor ℂ 𝔻 × ℂ .Object → 𝔻 .Object
        :func*: (F , A) = F .func* A

      module _ {dom cod : Functor ℂ 𝔻 × ℂ .Object} where
        private
          F : Functor ℂ 𝔻
          F = proj₁ dom
          A : ℂ .Object
          A = proj₂ dom

          G : Functor ℂ 𝔻
          G = proj₁ cod
          B : ℂ .Object
          B = proj₂ cod

        :func→: : (pobj : NaturalTransformation F G × ℂ .Arrow A B)
          → 𝔻 .Arrow (F .func* A) (G .func* B)
        :func→: ((θ , θNat) , f) = result
          where
            _𝔻⊕_ = 𝔻 ._⊕_
            θA : 𝔻 .Arrow (F .func* A) (G .func* A)
            θA = θ A
            θB : 𝔻 .Arrow (F .func* B) (G .func* B)
            θB = θ B
            F→f : 𝔻 .Arrow (F .func* A) (F .func* B)
            F→f = F .func→ f
            G→f : 𝔻 .Arrow (G .func* A) (G .func* B)
            G→f = G .func→ f
            l : 𝔻 .Arrow (F .func* A) (G .func* B)
            l = θB 𝔻⊕ F→f
            r : 𝔻 .Arrow (F .func* A) (G .func* B)
            r = G→f 𝔻⊕ θA
            -- There are two choices at this point,
            -- but I suppose the whole point is that
            -- by `θNat f` we have `l ≡ r`
            --     lem : θ B 𝔻⊕ F .func→ f ≡ G .func→ f 𝔻⊕ θ A
            --     lem = θNat f
            result : 𝔻 .Arrow (F .func* A) (G .func* B)
            result = l

      _×p_ = product

      module _ {c : Functor ℂ 𝔻 × ℂ .Object} where
        private
          F : Functor ℂ 𝔻
          F = proj₁ c
          C : ℂ .Object
          C = proj₂ c

        -- NaturalTransformation F G × ℂ .Arrow A B
        :ident: : :func→: {c} {c} (identityNat F , ℂ .𝟙) ≡ 𝔻 .𝟙
        :ident: = trans (proj₂ 𝔻.ident) (F .ident)
          where
            _𝔻⊕_ = 𝔻 ._⊕_
            open module 𝔻 = IsCategory (𝔻 .isCategory)
        -- Unfortunately the equational version has some ambigous arguments.
        -- :ident: : :func→: (identityNat F , ℂ .𝟙 {o = proj₂ c}) ≡ 𝔻 .𝟙
        -- :ident: = begin
        --   :func→: ((:obj: ×p ℂ) .Product.obj .𝟙) ≡⟨⟩
        --   :func→: (identityNat F , ℂ .𝟙) ≡⟨⟩
        --   (identityTrans F C 𝔻⊕ F .func→ (ℂ .𝟙)) ≡⟨⟩
        --   (𝔻 .𝟙 𝔻⊕ F .func→ (ℂ .𝟙)) ≡⟨ proj₂ 𝔻.ident ⟩
        --   F .func→ (ℂ .𝟙) ≡⟨ F .ident ⟩
        --   𝔻 .𝟙 ∎
        --   where
        --     _𝔻⊕_ = 𝔻 ._⊕_
        --     open module 𝔻 = IsCategory (𝔻 .isCategory)
      module _ {F×A G×B H×C : Functor ℂ 𝔻 × ℂ .Object} where
        F = F×A .proj₁
        A = F×A .proj₂
        G = G×B .proj₁
        B = G×B .proj₂
        H = H×C .proj₁
        C = H×C .proj₂
        _𝔻⊕_ = 𝔻 ._⊕_
        _ℂ⊕_ = ℂ ._⊕_
        -- Not entirely clear what this is at this point:
        _P⊕_ = (:obj: ×p ℂ) .Product.obj ._⊕_ {F×A} {G×B} {H×C}
        module _
          -- NaturalTransformation F G × ℂ .Arrow A B
          {θ×α : NaturalTransformation F G × ℂ .Arrow A B}
          {η×β : NaturalTransformation G H × ℂ .Arrow B C} where
          θ : Transformation F G
          θ = proj₁ (proj₁ θ×α)
          θNat : Natural F G θ
          θNat = proj₂ (proj₁ θ×α)
          f : ℂ .Arrow A B
          f = proj₂ θ×α
          η : Transformation G H
          η = proj₁ (proj₁ η×β)
          ηNat : Natural G H η
          ηNat = proj₂ (proj₁ η×β)
          g : ℂ .Arrow B C
          g = proj₂ η×β
          -- :func→: ((θ , θNat) , f) = θB 𝔻⊕ F→f
          _ : (:func→: {F×A} {G×B} θ×α) ≡ (θ B 𝔻⊕ F .func→ f)
          _ = refl
          ηθ : NaturalTransformation F H
          ηθ = Fun ._⊕_ {F} {G} {H} (η , ηNat) (θ , θNat)
          _ : ηθ ≡ Fun ._⊕_ {F} {G} {H} (η , ηNat) (θ , θNat)
          _ = refl
          ηθT = proj₁ ηθ
          ηθN = proj₂ ηθ
          _ : ηθT ≡ λ T → η T 𝔻⊕ θ T -- Fun ._⊕_ {F} {G} {H} (η , ηNat) (θ , θNat)
          _ = refl
          :distrib: :
              :func→: {F×A} {H×C} (η×β P⊕ θ×α)
            ≡ (:func→: {G×B} {H×C} η×β) 𝔻⊕ (:func→: {F×A} {G×B} θ×α)
          :distrib: = begin
            :func→: {F×A} {H×C} (η×β P⊕ θ×α)        ≡⟨⟩
            :func→: {F×A} {H×C} (ηθ , g ℂ⊕ f)       ≡⟨⟩
            (ηθT C 𝔻⊕ F .func→ (g ℂ⊕ f))            ≡⟨ ηθN (g ℂ⊕ f) ⟩
            (H .func→ (g ℂ⊕ f) 𝔻⊕ ηθT A)            ≡⟨ cong (λ φ → φ 𝔻⊕ ηθT A) (H .distrib) ⟩
            ((H .func→ g 𝔻⊕ H .func→ f) 𝔻⊕ ηθT A)   ≡⟨ sym 𝔻.assoc ⟩
            (H .func→ g 𝔻⊕ (H .func→ f 𝔻⊕ ηθT A))   ≡⟨⟩
            (H .func→ g 𝔻⊕ (H .func→ f 𝔻⊕ (η A 𝔻⊕ θ A))) ≡⟨ cong (λ φ → H .func→ g 𝔻⊕ φ) 𝔻.assoc ⟩
            (H .func→ g 𝔻⊕ ((H .func→ f 𝔻⊕ η A) 𝔻⊕ θ A)) ≡⟨ cong (λ φ → H .func→ g 𝔻⊕ φ) (cong (λ φ → φ 𝔻⊕ θ A) (sym (ηNat f))) ⟩
            (H .func→ g 𝔻⊕ ((η B 𝔻⊕ G .func→ f) 𝔻⊕ θ A)) ≡⟨ cong (λ φ → H .func→ g 𝔻⊕ φ) (sym 𝔻.assoc) ⟩
            (H .func→ g 𝔻⊕ (η B 𝔻⊕ (G .func→ f 𝔻⊕ θ A))) ≡⟨ 𝔻.assoc ⟩
            ((H .func→ g 𝔻⊕ η B) 𝔻⊕ (G .func→ f 𝔻⊕ θ A)) ≡⟨ cong (λ φ → φ 𝔻⊕ (G .func→ f 𝔻⊕ θ A)) (sym (ηNat g)) ⟩
            ((η C 𝔻⊕ G .func→ g) 𝔻⊕ (G .func→ f 𝔻⊕ θ A)) ≡⟨ cong (λ φ → (η C 𝔻⊕ G .func→ g) 𝔻⊕ φ) (sym (θNat f)) ⟩
            ((η C 𝔻⊕ G .func→ g) 𝔻⊕ (θ B 𝔻⊕ F .func→ f)) ≡⟨⟩
            ((:func→: {G×B} {H×C} η×β) 𝔻⊕ (:func→: {F×A} {G×B} θ×α)) ∎
            where
              lemθ : θ B 𝔻⊕ F .func→ f ≡ G .func→ f 𝔻⊕ θ A
              lemθ = θNat f
              lemη : η C 𝔻⊕ G .func→ g ≡ H .func→ g 𝔻⊕ η B
              lemη = ηNat g
              lemm : ηθT C 𝔻⊕ F .func→ (g ℂ⊕ f) ≡ (H .func→ (g ℂ⊕ f) 𝔻⊕ ηθT A)
              lemm = ηθN (g ℂ⊕ f)
              final : η B 𝔻⊕ G .func→ f ≡ H .func→ f 𝔻⊕ η A
              final = ηNat f
              open module 𝔻 = IsCategory (𝔻 .isCategory)
      -- Type of `:eval:` is aka.:
      --     Functor ((:obj: ×p ℂ) .Product.obj) 𝔻
      -- :eval: : Cat ℓ ℓ .Arrow ((:obj: ×p ℂ) .Product.obj) 𝔻
      :eval: : Functor ((:obj: ×p ℂ) .Product.obj) 𝔻
      :eval: = record
        { func* = :func*:
        ; func→ = λ {dom} {cod} → :func→: {dom} {cod}
        ; ident = λ {o} → :ident: {o}
        ; distrib = λ {f u n k y} → :distrib: {f} {u} {n} {k} {y}
        }

      module _ (𝔸 : Category ℓ ℓ) (F : Functor ((𝔸 ×p ℂ) .Product.obj) 𝔻) where
        instance
          CatℓHasProducts : HasProducts Catℓ
          CatℓHasProducts = CatHasProducts {ℓ} {ℓ}
        t : Catℓ .Arrow ((𝔸 ×p ℂ) .Product.obj) 𝔻 ≡ Functor ((𝔸 ×p ℂ) .Product.obj) 𝔻
        t = refl
        tt : Category ℓ ℓ
        tt = (𝔸 ×p ℂ) .Product.obj
        open HasProducts CatℓHasProducts
        postulate
          transpose : Functor 𝔸 :obj:
          eq : Catℓ ._⊕_ :eval: (parallelProduct transpose (Catℓ .𝟙 {o = ℂ})) ≡ F

        catTranspose : ∃![ F~ ] (Catℓ ._⊕_ :eval: (parallelProduct F~ (Catℓ .𝟙 {o = ℂ})) ≡ F)
        catTranspose = transpose , eq

      -- :isExponential: : IsExponential Catℓ A B :obj: {!:eval:!}
      :isExponential: : IsExponential Catℓ ℂ 𝔻 :obj: :eval:
      :isExponential: = catTranspose

      -- :exponent: : Exponential (Cat ℓ ℓ) A B
      :exponent: : Exponential Catℓ ℂ 𝔻
      :exponent: = record
        { obj = :obj:
        ; eval = :eval:
        ; isExponential = :isExponential:
        }

  CatHasExponentials : HasExponentials Catℓ
  CatHasExponentials = record { exponent = :exponent: }
