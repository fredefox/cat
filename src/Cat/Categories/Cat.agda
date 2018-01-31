{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cat.Categories.Cat where

open import Agda.Primitive
open import Cubical
open import Function
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

open import Cat.Category
open import Cat.Functor

open import Cat.Equality
open Equality.Data.Product

open Functor
open IsFunctor
open Category hiding (_∘_)

-- The category of categories
module _ (ℓ ℓ' : Level) where
  private
    module _ {𝔸 𝔹 ℂ 𝔻 : Category ℓ ℓ'} {F : Functor 𝔸 𝔹} {G : Functor 𝔹 ℂ} {H : Functor ℂ 𝔻} where
      private
        eq* : func* (H ∘f (G ∘f F)) ≡ func* ((H ∘f G) ∘f F)
        eq* = refl
        eq→ : PathP
          (λ i → {A B : 𝔸 .Object} → 𝔸 [ A , B ] → 𝔻 [ eq* i A , eq* i B ])
          (func→ (H ∘f (G ∘f F))) (func→ ((H ∘f G) ∘f F))
        eq→ = refl
        postulate
          eqI
            : (λ i → ∀ {A : 𝔸 .Object} → eq→ i (𝔸 .𝟙 {A}) ≡ 𝔻 .𝟙 {eq* i A})
            [ (H ∘f (G ∘f F)) .isFunctor .ident
            ≡ ((H ∘f G) ∘f F) .isFunctor .ident
            ]
          eqD
            : (λ i → ∀ {A B C} {f : 𝔸 [ A , B ]} {g : 𝔸 [ B , C ]}
              → eq→ i (𝔸 [ g ∘ f ]) ≡ 𝔻 [ eq→ i g ∘ eq→ i f ])
            [ (H ∘f (G ∘f F)) .isFunctor .distrib
            ≡ ((H ∘f G) ∘f F) .isFunctor .distrib
            ]

      assc : H ∘f (G ∘f F) ≡ (H ∘f G) ∘f F
      assc = Functor≡ eq* eq→ (IsFunctor≡ eqI eqD)

    module _ {ℂ 𝔻 : Category ℓ ℓ'} {F : Functor ℂ 𝔻} where
      module _ where
        private
          eq* : (func* F) ∘ (func* (identity {C = ℂ})) ≡ func* F
          eq* = refl
          -- lemmm : func→ {C = A} {D = B} (f ∘f identity) ≡ func→ f
          eq→ : PathP
            (λ i →
            {x y : Object ℂ} → Arrow ℂ x y → Arrow 𝔻 (func* F x) (func* F y))
            (func→ (F ∘f identity)) (func→ F)
          eq→ = refl
          postulate
            eqI-r
              : (λ i → {c : ℂ .Object} → (λ _ → 𝔻 [ func* F c , func* F c ])
                [ func→ F (ℂ .𝟙) ≡ 𝔻 .𝟙 ])
              [(F ∘f identity) .isFunctor .ident ≡ F .isFunctor .ident ]
            eqD-r : PathP
                        (λ i →
                        {A B C : ℂ .Object} {f : ℂ .Arrow A B} {g : ℂ .Arrow B C} →
                        eq→ i (ℂ [ g ∘ f ]) ≡ 𝔻 [ eq→ i g ∘ eq→ i f ])
                        ((F ∘f identity) .isFunctor .distrib) (F .isFunctor .distrib)
        ident-r : F ∘f identity ≡ F
        ident-r = Functor≡ eq* eq→ (IsFunctor≡ eqI-r eqD-r)
      module _ where
        private
          postulate
            eq* : (identity ∘f F) .func* ≡ F .func*
            eq→ : PathP
              (λ i → {x y : Object ℂ} → ℂ .Arrow x y → 𝔻 .Arrow (eq* i x) (eq* i y))
              ((identity ∘f F) .func→) (F .func→)
            eqI : (λ i → ∀ {A : ℂ .Object} → eq→ i (ℂ .𝟙 {A}) ≡ 𝔻 .𝟙 {eq* i A})
                  [ ((identity ∘f F) .isFunctor .ident) ≡ (F .isFunctor .ident) ]
            eqD : PathP (λ i → {A B C : ℂ .Object} {f : ℂ .Arrow A B} {g : ℂ .Arrow B C}
                 → eq→ i (ℂ [ g ∘ f ]) ≡ 𝔻 [ eq→ i g ∘ eq→ i f ])
                 ((identity ∘f F) .isFunctor .distrib) (F .isFunctor .distrib)
                 -- (λ z → eq* i z) (eq→ i)
        ident-l : identity ∘f F ≡ F
        ident-l = Functor≡ eq* eq→ λ i → record { ident = eqI i ; distrib = eqD i }

  Cat : Category (lsuc (ℓ ⊔ ℓ')) (ℓ ⊔ ℓ')
  Cat =
    record
      { Object = Category ℓ ℓ'
      ; Arrow = Functor
      ; 𝟙 = identity
      ; _∘_ = _∘f_
      -- What gives here? Why can I not name the variables directly?
      ; isCategory = record
        { assoc = λ {_ _ _ _ F G H} → assc {F = F} {G = G} {H = H}
        ; ident = ident-r , ident-l
        }
      }

module _ {ℓ ℓ' : Level} where
  module _ (ℂ 𝔻 : Category ℓ ℓ') where
    private
      Catt = Cat ℓ ℓ'
      :Object: = ℂ .Object × 𝔻 .Object
      :Arrow:  : :Object: → :Object: → Set ℓ'
      :Arrow: (c , d) (c' , d') = Arrow ℂ c c' × Arrow 𝔻 d d'
      :𝟙: : {o : :Object:} → :Arrow: o o
      :𝟙: = ℂ .𝟙 , 𝔻 .𝟙
      _:⊕:_ :
        {a b c : :Object:} →
        :Arrow: b c →
        :Arrow: a b →
        :Arrow: a c
      _:⊕:_ = λ { (bc∈C , bc∈D) (ab∈C , ab∈D) → ℂ [ bc∈C ∘ ab∈C ] , 𝔻 [ bc∈D ∘ ab∈D ]}

      instance
        :isCategory: : IsCategory :Object: :Arrow: :𝟙: _:⊕:_
        :isCategory: = record
          { assoc = Σ≡ C.assoc D.assoc
          ; ident
          = Σ≡ (fst C.ident) (fst D.ident)
          , Σ≡ (snd C.ident) (snd D.ident)
          }
          where
            open module C = IsCategory (ℂ .isCategory)
            open module D = IsCategory (𝔻 .isCategory)

      :product: : Category ℓ ℓ'
      :product: = record
        { Object = :Object:
        ; Arrow = :Arrow:
        ; 𝟙 = :𝟙:
        ; _∘_ = _:⊕:_
        }

      proj₁ : Catt [ :product: , ℂ ]
      proj₁ = record { func* = fst ; func→ = fst ; isFunctor = record { ident = refl ; distrib = refl } }

      proj₂ : Catt [ :product: , 𝔻 ]
      proj₂ = record { func* = snd ; func→ = snd ; isFunctor = record { ident = refl ; distrib = refl } }

      module _ {X : Object Catt} (x₁ : Catt [ X , ℂ ]) (x₂ : Catt [ X , 𝔻 ]) where
        open Functor

        x : Functor X :product:
        x = record
          { func* = λ x → x₁ .func* x , x₂ .func* x
          ; func→ = λ x → func→ x₁ x , func→ x₂ x
          ; isFunctor = record
            { ident   = Σ≡ x₁.ident x₂.ident
            ; distrib = Σ≡ x₁.distrib x₂.distrib
            }
          }
          where
            open module x₁ = IsFunctor (x₁ .isFunctor)
            open module x₂ = IsFunctor (x₂ .isFunctor)

        isUniqL : Catt [ proj₁ ∘ x ] ≡ x₁
        isUniqL = Functor≡ eq* eq→ eqIsF -- Functor≡ refl refl λ i → record { ident = refl i ; distrib = refl i }
          where
            eq* : (Catt [ proj₁ ∘ x ]) .func* ≡ x₁ .func*
            eq* = refl
            eq→ : (λ i → {A : X .Object} {B : X .Object} → X [ A , B ] → ℂ [ eq* i A , eq* i B ])
                    [ (Catt [ proj₁ ∘ x ]) .func→ ≡ x₁ .func→ ]
            eq→ = refl
            postulate eqIsF : (Catt [ proj₁ ∘ x ]) .isFunctor ≡ x₁ .isFunctor
            -- eqIsF = IsFunctor≡ {!refl!} {!!}

        postulate isUniqR : Catt [ proj₂ ∘ x ] ≡ x₂
        -- isUniqR = Functor≡ refl refl {!!} {!!}

        isUniq : Catt [ proj₁ ∘ x ] ≡ x₁ × Catt [ proj₂ ∘ x ] ≡ x₂
        isUniq = isUniqL , isUniqR

        uniq : ∃![ x ] (Catt [ proj₁ ∘ x ] ≡ x₁ × Catt [ proj₂ ∘ x ] ≡ x₂)
        uniq = x , isUniq

    instance
      isProduct : IsProduct (Cat ℓ ℓ') proj₁ proj₂
      isProduct = uniq

    product : Product {ℂ = (Cat ℓ ℓ')} ℂ 𝔻
    product = record
      { obj = :product:
      ; proj₁ = proj₁
      ; proj₂ = proj₂
      }

module _ {ℓ ℓ' : Level} where
  instance
    hasProducts : HasProducts (Cat ℓ ℓ')
    hasProducts = record { product = product }

-- Basically proves that `Cat ℓ ℓ` is cartesian closed.
module _ (ℓ : Level) where
  private
    open Data.Product
    open import Cat.Categories.Fun

    Catℓ : Category (lsuc (ℓ ⊔ ℓ)) (ℓ ⊔ ℓ)
    Catℓ = Cat ℓ ℓ
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
            θA : 𝔻 .Arrow (F .func* A) (G .func* A)
            θA = θ A
            θB : 𝔻 .Arrow (F .func* B) (G .func* B)
            θB = θ B
            F→f : 𝔻 .Arrow (F .func* A) (F .func* B)
            F→f = F .func→ f
            G→f : 𝔻 .Arrow (G .func* A) (G .func* B)
            G→f = G .func→ f
            l : 𝔻 .Arrow (F .func* A) (G .func* B)
            l = 𝔻 [ θB ∘ F→f ]
            r : 𝔻 .Arrow (F .func* A) (G .func* B)
            r = 𝔻 [ G→f ∘ θA ]
            -- There are two choices at this point,
            -- but I suppose the whole point is that
            -- by `θNat f` we have `l ≡ r`
            --     lem : 𝔻 [ θ B ∘ F .func→ f ] ≡ 𝔻 [ G .func→ f ∘ θ A ]
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
        -- :ident: : :func→: {c} {c} (identityNat F , ℂ .𝟙) ≡ 𝔻 .𝟙
        -- :ident: = trans (proj₂ 𝔻.ident) (F .ident)
        --   where
        --     open module 𝔻 = IsCategory (𝔻 .isCategory)
        -- Unfortunately the equational version has some ambigous arguments.
        :ident: : :func→: {c} {c} (identityNat F , ℂ .𝟙 {o = proj₂ c}) ≡ 𝔻 .𝟙
        :ident: = begin
          :func→: {c} {c} ((:obj: ×p ℂ) .Product.obj .𝟙 {c}) ≡⟨⟩
          :func→: {c} {c} (identityNat F , ℂ .𝟙)             ≡⟨⟩
          𝔻 [ identityTrans F C ∘ F .func→ (ℂ .𝟙)]           ≡⟨⟩
          𝔻 [ 𝔻 .𝟙 ∘ F .func→ (ℂ .𝟙)]                        ≡⟨ proj₂ 𝔻.ident ⟩
          F .func→ (ℂ .𝟙)                                    ≡⟨ F.ident ⟩
          𝔻 .𝟙                                               ∎
          where
            open module 𝔻 = IsCategory (𝔻 .isCategory)
            open module F = IsFunctor (F .isFunctor)

      module _ {F×A G×B H×C : Functor ℂ 𝔻 × ℂ .Object} where
        F = F×A .proj₁
        A = F×A .proj₂
        G = G×B .proj₁
        B = G×B .proj₂
        H = H×C .proj₁
        C = H×C .proj₂
        -- Not entirely clear what this is at this point:
        _P⊕_ = (:obj: ×p ℂ) .Product.obj .Category._∘_ {F×A} {G×B} {H×C}
        module _
          -- NaturalTransformation F G × ℂ .Arrow A B
          {θ×f : NaturalTransformation F G × ℂ .Arrow A B}
          {η×g : NaturalTransformation G H × ℂ .Arrow B C} where
          private
            θ : Transformation F G
            θ = proj₁ (proj₁ θ×f)
            θNat : Natural F G θ
            θNat = proj₂ (proj₁ θ×f)
            f : ℂ .Arrow A B
            f = proj₂ θ×f
            η : Transformation G H
            η = proj₁ (proj₁ η×g)
            ηNat : Natural G H η
            ηNat = proj₂ (proj₁ η×g)
            g : ℂ .Arrow B C
            g = proj₂ η×g

            ηθNT : NaturalTransformation F H
            ηθNT = Fun .Category._∘_ {F} {G} {H} (η , ηNat) (θ , θNat)

            ηθ = proj₁ ηθNT
            ηθNat = proj₂ ηθNT

          :distrib: :
              𝔻 [ 𝔻 [ η C ∘ θ C ] ∘ F .func→ ( ℂ [ g ∘ f ] ) ]
            ≡ 𝔻 [ 𝔻 [ η C ∘ G .func→ g ] ∘ 𝔻 [ θ B ∘ F .func→ f ] ]
          :distrib: = begin
            𝔻 [ (ηθ C) ∘ F .func→ (ℂ [ g ∘ f ]) ]
              ≡⟨ ηθNat (ℂ [ g ∘ f ]) ⟩
            𝔻 [ H .func→ (ℂ [ g ∘ f ]) ∘ (ηθ A) ]
              ≡⟨ cong (λ φ → 𝔻 [ φ ∘ ηθ A ]) (H.distrib) ⟩
            𝔻 [ 𝔻 [ H .func→ g ∘ H .func→ f ] ∘ (ηθ A) ]
              ≡⟨ sym assoc ⟩
            𝔻 [ H .func→ g ∘ 𝔻 [ H .func→ f ∘ ηθ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ H .func→ g ∘ φ ]) assoc ⟩
            𝔻 [ H .func→ g ∘ 𝔻 [ 𝔻 [ H .func→ f ∘ η A ] ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ H .func→ g ∘ φ ]) (cong (λ φ → 𝔻 [ φ ∘ θ A ]) (sym (ηNat f))) ⟩
            𝔻 [ H .func→ g ∘ 𝔻 [ 𝔻 [ η B ∘ G .func→ f ] ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ H .func→ g ∘ φ ]) (sym assoc) ⟩
            𝔻 [ H .func→ g ∘ 𝔻 [ η B ∘ 𝔻 [ G .func→ f ∘ θ A ] ] ] ≡⟨ assoc ⟩
            𝔻 [ 𝔻 [ H .func→ g ∘ η B ] ∘ 𝔻 [ G .func→ f ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ φ ∘ 𝔻 [ G .func→ f ∘ θ A ] ]) (sym (ηNat g)) ⟩
            𝔻 [ 𝔻 [ η C ∘ G .func→ g ] ∘ 𝔻 [ G .func→ f ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ 𝔻 [ η C ∘ G .func→ g ] ∘ φ ]) (sym (θNat f)) ⟩
            𝔻 [ 𝔻 [ η C ∘ G .func→ g ] ∘ 𝔻 [ θ B ∘ F .func→ f ] ] ∎
            where
              open IsCategory (𝔻 .isCategory)
              open module H = IsFunctor (H .isFunctor)

      :eval: : Functor ((:obj: ×p ℂ) .Product.obj) 𝔻
      :eval: = record
        { func* = :func*:
        ; func→ = λ {dom} {cod} → :func→: {dom} {cod}
        ; isFunctor = record
          { ident = λ {o} → :ident: {o}
          ; distrib = λ {f u n k y} → :distrib: {f} {u} {n} {k} {y}
          }
        }

      module _ (𝔸 : Category ℓ ℓ) (F : Functor ((𝔸 ×p ℂ) .Product.obj) 𝔻) where
        open HasProducts (hasProducts {ℓ} {ℓ}) using (parallelProduct)

        postulate
          transpose : Functor 𝔸 :obj:
          eq : Catℓ [ :eval: ∘ (parallelProduct transpose (Catℓ .𝟙 {o = ℂ})) ] ≡ F

        catTranspose : ∃![ F~ ] (Catℓ [ :eval: ∘ (parallelProduct F~ (Catℓ .𝟙 {o = ℂ}))] ≡ F )
        catTranspose = transpose , eq

      :isExponential: : IsExponential Catℓ ℂ 𝔻 :obj: :eval:
      :isExponential: = catTranspose

      -- :exponent: : Exponential (Cat ℓ ℓ) A B
      :exponent: : Exponential Catℓ ℂ 𝔻
      :exponent: = record
        { obj = :obj:
        ; eval = :eval:
        ; isExponential = :isExponential:
        }

  hasExponentials : HasExponentials (Cat ℓ ℓ)
  hasExponentials = record { exponent = :exponent: }
