-- There is no category of categories in our interpretation
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cat.Categories.Cat where

open import Agda.Primitive
open import Cubical
open import Function
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.Product
open import Cat.Category.Exponential

open import Cat.Equality
open Equality.Data.Product

open Functor
open IsFunctor
open Category using (Object ; 𝟙)

-- The category of categories
module _ (ℓ ℓ' : Level) where
  private
    module _ {𝔸 𝔹 ℂ 𝔻 : Category ℓ ℓ'} {F : Functor 𝔸 𝔹} {G : Functor 𝔹 ℂ} {H : Functor ℂ 𝔻} where
      private
        eq* : func* (H ∘f (G ∘f F)) ≡ func* ((H ∘f G) ∘f F)
        eq* = refl
        eq→ : PathP
          (λ i → {A B : Object 𝔸} → 𝔸 [ A , B ] → 𝔻 [ eq* i A , eq* i B ])
          (func→ (H ∘f (G ∘f F))) (func→ ((H ∘f G) ∘f F))
        eq→ = refl
        postulate
          eqI
            : (λ i → ∀ {A : Object 𝔸} → eq→ i (𝟙 𝔸 {A}) ≡ 𝟙 𝔻 {eq* i A})
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
      assc = Functor≡ eq* eq→

    module _ {ℂ 𝔻 : Category ℓ ℓ'} {F : Functor ℂ 𝔻} where
      module _ where
        private
          eq* : (func* F) ∘ (func* (identity {C = ℂ})) ≡ func* F
          eq* = refl
          -- lemmm : func→ {C = A} {D = B} (f ∘f identity) ≡ func→ f
          eq→ : PathP
            (λ i →
            {x y : Object ℂ} → ℂ [ x , y ] → 𝔻 [ func* F x , func* F y ])
            (func→ (F ∘f identity)) (func→ F)
          eq→ = refl
          postulate
            eqI-r
              : (λ i → {c : Object ℂ} → (λ _ → 𝔻 [ func* F c , func* F c ])
                [ func→ F (𝟙 ℂ) ≡ 𝟙 𝔻 ])
              [(F ∘f identity) .isFunctor .ident ≡ F .isFunctor .ident ]
            eqD-r : PathP
                        (λ i →
                        {A B C : Object ℂ} {f : ℂ [ A , B ]} {g : ℂ [ B , C ]} →
                        eq→ i (ℂ [ g ∘ f ]) ≡ 𝔻 [ eq→ i g ∘ eq→ i f ])
                        ((F ∘f identity) .isFunctor .distrib) (F .isFunctor .distrib)
        ident-r : F ∘f identity ≡ F
        ident-r = Functor≡ eq* eq→
      module _ where
        private
          postulate
            eq* : func* (identity ∘f F) ≡ func* F
            eq→ : PathP
              (λ i → {x y : Object ℂ} → ℂ [ x , y ] → 𝔻 [ eq* i x , eq* i y ])
              (func→ (identity ∘f F)) (func→ F)
            eqI : (λ i → ∀ {A : Object ℂ} → eq→ i (𝟙 ℂ {A}) ≡ 𝟙 𝔻 {eq* i A})
                  [ ((identity ∘f F) .isFunctor .ident) ≡ (F .isFunctor .ident) ]
            eqD : PathP (λ i → {A B C : Object ℂ} {f : ℂ [ A , B ]} {g : ℂ [ B , C ]}
                 → eq→ i (ℂ [ g ∘ f ]) ≡ 𝔻 [ eq→ i g ∘ eq→ i f ])
                 ((identity ∘f F) .isFunctor .distrib) (F .isFunctor .distrib)
                 -- (λ z → eq* i z) (eq→ i)
        ident-l : identity ∘f F ≡ F
        ident-l = Functor≡ eq* eq→

  RawCat : RawCategory (lsuc (ℓ ⊔ ℓ')) (ℓ ⊔ ℓ')
  RawCat =
    record
      { Object = Category ℓ ℓ'
      ; Arrow = Functor
      ; 𝟙 = identity
      ; _∘_ = _∘f_
      -- What gives here? Why can I not name the variables directly?
      -- ; isCategory = record
      --   { assoc = λ {_ _ _ _ F G H} → assc {F = F} {G = G} {H = H}
      --   ; ident = ident-r , ident-l
      --   }
      }
  private
    open RawCategory
    assoc : IsAssociative RawCat
    assoc {f = F} {G} {H} = assc {F = F} {G = G} {H = H}
    -- TODO: Rename `ident'` to `ident` after changing how names are exposed in Functor.
    ident' : IsIdentity RawCat identity
    ident' = ident-r , ident-l
    -- NB! `ArrowsAreSets RawCat` is *not* provable. The type of functors,
    -- however, form a groupoid! Therefore there is no (1-)category of
    -- categories. There does, however, exist a 2-category of 1-categories.

  -- Because of the note above there is not category of categories.
  Cat : (unprovable : IsCategory RawCat) → Category (lsuc (ℓ ⊔ ℓ')) (ℓ ⊔ ℓ')
  Category.raw        (Cat _) = RawCat
  Category.isCategory (Cat unprovable) = unprovable
  -- Category.raw Cat _ = RawCat
  -- Category.isCategory Cat unprovable = unprovable

-- The following to some extend depends on the category of categories being a
-- category. In some places it may not actually be needed, however.
module _ {ℓ ℓ' : Level} (unprovable : IsCategory (RawCat ℓ ℓ')) where
  module _ (ℂ 𝔻 : Category ℓ ℓ') where
    private
      Catt = Cat ℓ ℓ' unprovable
      :Object: = Object ℂ × Object 𝔻
      :Arrow:  : :Object: → :Object: → Set ℓ'
      :Arrow: (c , d) (c' , d') = ℂ [ c , c' ] × 𝔻 [ d , d' ]
      :𝟙: : {o : :Object:} → :Arrow: o o
      :𝟙: = 𝟙 ℂ , 𝟙 𝔻
      _:⊕:_ :
        {a b c : :Object:} →
        :Arrow: b c →
        :Arrow: a b →
        :Arrow: a c
      _:⊕:_ = λ { (bc∈C , bc∈D) (ab∈C , ab∈D) → ℂ [ bc∈C ∘ ab∈C ] , 𝔻 [ bc∈D ∘ ab∈D ]}

      :rawProduct: : RawCategory ℓ ℓ'
      RawCategory.Object :rawProduct: = :Object:
      RawCategory.Arrow :rawProduct: = :Arrow:
      RawCategory.𝟙 :rawProduct: = :𝟙:
      RawCategory._∘_ :rawProduct: = _:⊕:_
      open RawCategory :rawProduct:

      module C = Category ℂ
      module D = Category 𝔻
      postulate
        issSet : {A B : RawCategory.Object :rawProduct:} → isSet (Arrow A B)
      ident' : IsIdentity :𝟙:
      ident'
        = Σ≡ (fst C.ident) (fst D.ident)
        , Σ≡ (snd C.ident) (snd D.ident)
      postulate univalent : Univalence.Univalent :rawProduct: ident'
      instance
        :isCategory: : IsCategory :rawProduct:
        IsCategory.assoc :isCategory: = Σ≡ C.assoc D.assoc
        IsCategory.ident :isCategory: = ident'
        IsCategory.arrowIsSet :isCategory: = issSet
        IsCategory.univalent :isCategory: = univalent

      :product: : Category ℓ ℓ'
      Category.raw :product: = :rawProduct:

      proj₁ : Catt [ :product: , ℂ ]
      proj₁ = record
        { raw = record { func* = fst ; func→ = fst }
        ; isFunctor = record { ident = refl ; distrib = refl }
        }

      proj₂ : Catt [ :product: , 𝔻 ]
      proj₂ = record
        { raw = record { func* = snd ; func→ = snd }
        ; isFunctor = record { ident = refl ; distrib = refl }
        }

      module _ {X : Object Catt} (x₁ : Catt [ X , ℂ ]) (x₂ : Catt [ X , 𝔻 ]) where
        open Functor

        postulate x : Functor X :product:
        -- x = record
        --   { func* = λ x → x₁ .func* x , x₂ .func* x
        --   ; func→ = λ x → func→ x₁ x , func→ x₂ x
        --   ; isFunctor = record
        --     { ident   = Σ≡ x₁.ident x₂.ident
        --     ; distrib = Σ≡ x₁.distrib x₂.distrib
        --     }
        --   }
        --   where
        --     open module x₁ = IsFunctor (x₁ .isFunctor)
        --     open module x₂ = IsFunctor (x₂ .isFunctor)

        -- Turned into postulate after:
        -- > commit e8215b2c051062c6301abc9b3f6ec67106259758 (HEAD -> dev, github/dev)
        -- > Author: Frederik Hanghøj Iversen <fhi.1990@gmail.com>
        -- > Date:   Mon Feb 5 14:59:53 2018 +0100
        postulate isUniqL : Catt [ proj₁ ∘ x ] ≡ x₁
        -- isUniqL = Functor≡ eq* eq→ {!!}
        --   where
        --     eq* : (Catt [ proj₁ ∘ x ]) .func* ≡ x₁ .func*
        --     eq* = {!refl!}
        --     eq→ : (λ i → {A : Object X} {B : Object X} → X [ A , B ] → ℂ [ eq* i A , eq* i B ])
        --             [ (Catt [ proj₁ ∘ x ]) .func→ ≡ x₁ .func→ ]
        --     eq→ = refl
            -- postulate eqIsF : (Catt [ proj₁ ∘ x ]) .isFunctor ≡ x₁ .isFunctor
            -- eqIsF = IsFunctor≡ {!refl!} {!!}

        postulate isUniqR : Catt [ proj₂ ∘ x ] ≡ x₂
        -- isUniqR = Functor≡ refl refl {!!} {!!}

        isUniq : Catt [ proj₁ ∘ x ] ≡ x₁ × Catt [ proj₂ ∘ x ] ≡ x₂
        isUniq = isUniqL , isUniqR

        uniq : ∃![ x ] (Catt [ proj₁ ∘ x ] ≡ x₁ × Catt [ proj₂ ∘ x ] ≡ x₂)
        uniq = x , isUniq

    instance
      isProduct : IsProduct Catt proj₁ proj₂
      isProduct = uniq

    product : Product {ℂ = Catt} ℂ 𝔻
    product = record
      { obj = :product:
      ; proj₁ = proj₁
      ; proj₂ = proj₂
      }

module _ {ℓ ℓ' : Level} (unprovable : IsCategory (RawCat ℓ ℓ')) where
  Catt = Cat ℓ ℓ' unprovable
  instance
    hasProducts : HasProducts Catt
    hasProducts = record { product = product unprovable }

-- Basically proves that `Cat ℓ ℓ` is cartesian closed.
module _ (ℓ : Level) (unprovable : IsCategory (RawCat ℓ ℓ)) where
  private
    open Data.Product
    open import Cat.Categories.Fun

    Catℓ : Category (lsuc (ℓ ⊔ ℓ)) (ℓ ⊔ ℓ)
    Catℓ = Cat ℓ ℓ unprovable
    module _ (ℂ 𝔻 : Category ℓ ℓ) where
      private
        :obj: : Object Catℓ
        :obj: = Fun {ℂ = ℂ} {𝔻 = 𝔻}

        :func*: : Functor ℂ 𝔻 × Object ℂ → Object 𝔻
        :func*: (F , A) = func* F A

      module _ {dom cod : Functor ℂ 𝔻 × Object ℂ} where
        private
          F : Functor ℂ 𝔻
          F = proj₁ dom
          A : Object ℂ
          A = proj₂ dom

          G : Functor ℂ 𝔻
          G = proj₁ cod
          B : Object ℂ
          B = proj₂ cod

        :func→: : (pobj : NaturalTransformation F G × ℂ [ A , B ])
          → 𝔻 [ func* F A , func* G B ]
        :func→: ((θ , θNat) , f) = result
          where
            θA : 𝔻 [ func* F A , func* G A ]
            θA = θ A
            θB : 𝔻 [ func* F B , func* G B ]
            θB = θ B
            F→f : 𝔻 [ func* F A , func* F B ]
            F→f = func→ F f
            G→f : 𝔻 [ func* G A , func* G B ]
            G→f = func→ G f
            l : 𝔻 [ func* F A , func* G B ]
            l = 𝔻 [ θB ∘ F→f ]
            r : 𝔻 [ func* F A , func* G B ]
            r = 𝔻 [ G→f ∘ θA ]
            -- There are two choices at this point,
            -- but I suppose the whole point is that
            -- by `θNat f` we have `l ≡ r`
            --     lem : 𝔻 [ θ B ∘ F .func→ f ] ≡ 𝔻 [ G .func→ f ∘ θ A ]
            --     lem = θNat f
            result : 𝔻 [ func* F A , func* G B ]
            result = l

      _×p_ = product unprovable

      module _ {c : Functor ℂ 𝔻 × Object ℂ} where
        private
          F : Functor ℂ 𝔻
          F = proj₁ c
          C : Object ℂ
          C = proj₂ c

        -- NaturalTransformation F G × ℂ .Arrow A B
        -- :ident: : :func→: {c} {c} (identityNat F , ℂ .𝟙) ≡ 𝔻 .𝟙
        -- :ident: = trans (proj₂ 𝔻.ident) (F .ident)
        --   where
        --     open module 𝔻 = IsCategory (𝔻 .isCategory)
        -- Unfortunately the equational version has some ambigous arguments.
        :ident: : :func→: {c} {c} (identityNat F , 𝟙 ℂ {A = proj₂ c}) ≡ 𝟙 𝔻
        :ident: = begin
          :func→: {c} {c} (𝟙 (Product.obj (:obj: ×p ℂ)) {c}) ≡⟨⟩
          :func→: {c} {c} (identityNat F , 𝟙 ℂ)             ≡⟨⟩
          𝔻 [ identityTrans F C ∘ func→ F (𝟙 ℂ)]           ≡⟨⟩
          𝔻 [ 𝟙 𝔻 ∘ func→ F (𝟙 ℂ)]                        ≡⟨ proj₂ 𝔻.ident ⟩
          func→ F (𝟙 ℂ)                                    ≡⟨ F.ident ⟩
          𝟙 𝔻                                               ∎
          where
            open module 𝔻 = Category 𝔻
            open module F = IsFunctor (F .isFunctor)

      module _ {F×A G×B H×C : Functor ℂ 𝔻 × Object ℂ} where
        F = F×A .proj₁
        A = F×A .proj₂
        G = G×B .proj₁
        B = G×B .proj₂
        H = H×C .proj₁
        C = H×C .proj₂
        -- Not entirely clear what this is at this point:
        _P⊕_ = Category._∘_ (Product.obj (:obj: ×p ℂ)) {F×A} {G×B} {H×C}
        module _
          -- NaturalTransformation F G × ℂ .Arrow A B
          {θ×f : NaturalTransformation F G × ℂ [ A , B ]}
          {η×g : NaturalTransformation G H × ℂ [ B , C ]} where
          private
            θ : Transformation F G
            θ = proj₁ (proj₁ θ×f)
            θNat : Natural F G θ
            θNat = proj₂ (proj₁ θ×f)
            f : ℂ [ A , B ]
            f = proj₂ θ×f
            η : Transformation G H
            η = proj₁ (proj₁ η×g)
            ηNat : Natural G H η
            ηNat = proj₂ (proj₁ η×g)
            g : ℂ [ B , C ]
            g = proj₂ η×g

            ηθNT : NaturalTransformation F H
            ηθNT = Category._∘_ Fun {F} {G} {H} (η , ηNat) (θ , θNat)

            ηθ = proj₁ ηθNT
            ηθNat = proj₂ ηθNT

          :distrib: :
              𝔻 [ 𝔻 [ η C ∘ θ C ] ∘ func→ F ( ℂ [ g ∘ f ] ) ]
            ≡ 𝔻 [ 𝔻 [ η C ∘ func→ G g ] ∘ 𝔻 [ θ B ∘ func→ F f ] ]
          :distrib: = begin
            𝔻 [ (ηθ C) ∘ func→ F (ℂ [ g ∘ f ]) ]
              ≡⟨ ηθNat (ℂ [ g ∘ f ]) ⟩
            𝔻 [ func→ H (ℂ [ g ∘ f ]) ∘ (ηθ A) ]
              ≡⟨ cong (λ φ → 𝔻 [ φ ∘ ηθ A ]) (H.distrib) ⟩
            𝔻 [ 𝔻 [ func→ H g ∘ func→ H f ] ∘ (ηθ A) ]
              ≡⟨ sym assoc ⟩
            𝔻 [ func→ H g ∘ 𝔻 [ func→ H f ∘ ηθ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ func→ H g ∘ φ ]) assoc ⟩
            𝔻 [ func→ H g ∘ 𝔻 [ 𝔻 [ func→ H f ∘ η A ] ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ func→ H g ∘ φ ]) (cong (λ φ → 𝔻 [ φ ∘ θ A ]) (sym (ηNat f))) ⟩
            𝔻 [ func→ H g ∘ 𝔻 [ 𝔻 [ η B ∘ func→ G f ] ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ func→ H g ∘ φ ]) (sym assoc) ⟩
            𝔻 [ func→ H g ∘ 𝔻 [ η B ∘ 𝔻 [ func→ G f ∘ θ A ] ] ]
              ≡⟨ assoc ⟩
            𝔻 [ 𝔻 [ func→ H g ∘ η B ] ∘ 𝔻 [ func→ G f ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ φ ∘ 𝔻 [ func→ G f ∘ θ A ] ]) (sym (ηNat g)) ⟩
            𝔻 [ 𝔻 [ η C ∘ func→ G g ] ∘ 𝔻 [ func→ G f ∘ θ A ] ]
              ≡⟨ cong (λ φ → 𝔻 [ 𝔻 [ η C ∘ func→ G g ] ∘ φ ]) (sym (θNat f)) ⟩
            𝔻 [ 𝔻 [ η C ∘ func→ G g ] ∘ 𝔻 [ θ B ∘ func→ F f ] ] ∎
            where
              open Category 𝔻
              module H = IsFunctor (H .isFunctor)

      :eval: : Functor ((:obj: ×p ℂ) .Product.obj) 𝔻
      :eval: = record
        { raw = record
          { func* = :func*:
          ; func→ = λ {dom} {cod} → :func→: {dom} {cod}
          }
        ; isFunctor = record
          { ident = λ {o} → :ident: {o}
          ; distrib = λ {f u n k y} → :distrib: {f} {u} {n} {k} {y}
          }
        }

      module _ (𝔸 : Category ℓ ℓ) (F : Functor ((𝔸 ×p ℂ) .Product.obj) 𝔻) where
        open HasProducts (hasProducts {ℓ} {ℓ} unprovable) renaming (_|×|_ to parallelProduct)

        postulate
          transpose : Functor 𝔸 :obj:
          eq : Catℓ [ :eval: ∘ (parallelProduct transpose (𝟙 Catℓ {A = ℂ})) ] ≡ F
          -- eq : Catℓ [ :eval: ∘ (HasProducts._|×|_ hasProducts transpose (𝟙 Catℓ {o = ℂ})) ] ≡ F
          -- eq' : (Catℓ [ :eval: ∘
          --   (record { product = product } HasProducts.|×| transpose)
          --   (𝟙 Catℓ)
          --   ])
          --   ≡ F

        -- For some reason after `e8215b2c051062c6301abc9b3f6ec67106259758`
        -- `catTranspose` makes Agda hang. catTranspose : ∃![ F~ ] (Catℓ [
        -- :eval: ∘ (parallelProduct F~ (𝟙 Catℓ {o = ℂ}))] ≡ F) catTranspose =
        -- transpose , eq

      postulate :isExponential: : IsExponential Catℓ ℂ 𝔻 :obj: :eval:
      -- :isExponential: : IsExponential Catℓ ℂ 𝔻 :obj: :eval:
      -- :isExponential: = {!catTranspose!}
      --   where
      --     open HasProducts (hasProducts {ℓ} {ℓ} unprovable) using (_|×|_)
      -- :isExponential: = λ 𝔸 F → transpose 𝔸 F , eq' 𝔸 F

      -- :exponent: : Exponential (Cat ℓ ℓ) A B
      :exponent: : Exponential Catℓ ℂ 𝔻
      :exponent: = record
        { obj = :obj:
        ; eval = :eval:
        ; isExponential = :isExponential:
        }

  hasExponentials : HasExponentials Catℓ
  hasExponentials = record { exponent = :exponent: }
