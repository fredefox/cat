{-# OPTIONS --cubical --caching #-}
module Cat.Category.Product where

open import Cat.Prelude as P hiding (_×_ ; fst ; snd)
open import Cat.Equivalence

open import Cat.Category

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  open Category ℂ

  module _ (A B : Object) where
    record RawProduct : Set (ℓa ⊔ ℓb) where
    --  no-eta-equality
      field
        object : Object
        fst  : ℂ [ object , A ]
        snd  : ℂ [ object , B ]

    record IsProduct (raw : RawProduct) : Set (ℓa ⊔ ℓb) where
      open RawProduct raw public
      field
        ump : ∀ {X : Object} (f : ℂ [ X , A ]) (g : ℂ [ X , B ])
          → ∃![ f×g ] ((ℂ [ fst ∘ f×g ] ≡ f) P.× (ℂ [ snd ∘ f×g ] ≡ g))

      -- | Arrow product
      _P[_×_] : ∀ {X} → (π₁ : ℂ [ X , A ]) (π₂ : ℂ [ X , B ])
        → ℂ [ X , object ]
      _P[_×_] π₁ π₂ = P.fst (ump π₁ π₂)

    record Product : Set (ℓa ⊔ ℓb) where
      field
        raw        : RawProduct
        isProduct  : IsProduct raw

      open IsProduct isProduct public

  record HasProducts : Set (ℓa ⊔ ℓb) where
    field
      product : ∀ (A B : Object) → Product A B

    _×_ : Object → Object → Object
    A × B = Product.object (product A B)

    -- | Parallel product of arrows
    --
    -- The product mentioned in awodey in Def 6.1 is not the regular product of
    -- arrows. It's a "parallel" product
    module _ {A A' B B' : Object} where
      open Product using (_P[_×_])
      open Product (product A B) hiding (_P[_×_]) renaming (fst to fst ; snd to snd)
      _|×|_ : ℂ [ A , A' ] → ℂ [ B , B' ] → ℂ [ A × B , A' × B' ]
      f |×| g = product A' B'
        P[ ℂ [ f ∘ fst ]
        ×  ℂ [ g ∘ snd ]
        ]

module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb}
  (let module ℂ = Category ℂ) {𝒜 ℬ : ℂ.Object} where
  private
    module _ (raw : RawProduct ℂ 𝒜 ℬ) where
      private
        open Category ℂ hiding (raw)
        module _ (x y : IsProduct ℂ 𝒜 ℬ raw) where
          private
            module x = IsProduct x
            module y = IsProduct y

          module _ {X : Object} (f : ℂ [ X , 𝒜 ]) (g : ℂ [ X , ℬ ]) where
            module _ (f×g : Arrow X y.object) where
              help : isProp (∀{y} → (ℂ [ y.fst ∘ y ] ≡ f) P.× (ℂ [ y.snd ∘ y ] ≡ g) → f×g ≡ y)
              help = propPiImpl (propPi (λ _ → arrowsAreSets _ _))

            res = ∃-unique (x.ump f g) (y.ump f g)

            prodAux : x.ump f g ≡ y.ump f g
            prodAux = lemSig ((λ f×g → propSig (propSig (arrowsAreSets _ _) λ _ → arrowsAreSets _ _) (λ _ → help f×g))) res

          propIsProduct' : x ≡ y
          propIsProduct' i = record { ump = λ f g → prodAux f g i }

      propIsProduct : isProp (IsProduct ℂ 𝒜 ℬ raw)
      propIsProduct = propIsProduct'

    Product≡ : {x y : Product ℂ 𝒜 ℬ} → (Product.raw x ≡ Product.raw y) → x ≡ y
    Product≡ {x} {y} p i = record { raw = p i ; isProduct = q i }
      where
      q : (λ i → IsProduct ℂ 𝒜 ℬ (p i)) [ Product.isProduct x ≡ Product.isProduct y ]
      q = lemPropF propIsProduct _ _ p

    open P
    open import Cat.Categories.Span

    open Category (span ℂ 𝒜 ℬ)

    lemma : Terminal ≃ Product ℂ 𝒜 ℬ
    lemma = fromIsomorphism Terminal (Product ℂ 𝒜 ℬ) (f , g , inv)
      where
      f : Terminal → Product ℂ 𝒜 ℬ
      f ((X , x0 , x1) , uniq) = p
        where
        rawP : RawProduct ℂ 𝒜 ℬ
        rawP = record
          { object = X
          ; fst = x0
          ; snd = x1
          }
        -- open RawProduct rawP renaming (fst to x0 ; snd to x1)
        module _ {Y : ℂ.Object} (p0 : ℂ [ Y , 𝒜 ]) (p1 : ℂ [ Y , ℬ ]) where
          uy : isContr (Arrow (Y , p0 , p1) (X , x0 , x1))
          uy = uniq {Y , p0 , p1}
          open Σ uy renaming (fst to Y→X ; snd to contractible)
          open Σ Y→X renaming (fst to p0×p1 ; snd to cond)
          ump : ∃![ f×g ] ((ℂ [ x0 ∘ f×g ] ≡ p0) P.× (ℂ [ x1 ∘ f×g ] ≡ p1))
          ump = p0×p1 , cond , λ {f} cond-f → cong fst (contractible (f , cond-f))
        isP : IsProduct ℂ 𝒜 ℬ rawP
        isP = record { ump = ump }
        p : Product ℂ 𝒜 ℬ
        p = record
          { raw = rawP
          ; isProduct = isP
          }
      g : Product ℂ 𝒜 ℬ → Terminal
      g p = 𝒳 , t
        where
        open Product p renaming (object to X ; fst to x₀ ; snd to x₁) using ()
        module p = Product p
        module isp = IsProduct p.isProduct
        𝒳 : Object
        𝒳 = X , x₀ , x₁
        module _ {𝒴 : Object} where
          open Σ 𝒴 renaming (fst to Y)
          open Σ (snd 𝒴) renaming (fst to y₀ ; snd to y₁)
          ump = p.ump y₀ y₁
          open Σ ump renaming (fst to f')
          open Σ (snd ump) renaming (fst to f'-cond)
          𝒻 : Arrow 𝒴 𝒳
          𝒻 = f' , f'-cond
          contractible : (f : Arrow 𝒴 𝒳) → 𝒻 ≡ f
          contractible ff@(f , f-cond) = res
            where
            k : f' ≡ f
            k = snd (snd ump) f-cond
            prp : (a : ℂ.Arrow Y X) → isProp
              ( (ℂ [ x₀ ∘ a ] ≡ y₀)
              × (ℂ [ x₁ ∘ a ] ≡ y₁)
              )
            prp f f0 f1 = Σ≡
              ( ℂ.arrowsAreSets _ _ (fst f0) (fst f1)
              , ℂ.arrowsAreSets _ _ (snd f0) (snd f1))
            h :
              ( λ i
                → (ℂ [ x₀ ∘ k i ] ≡ y₀)
                × (ℂ [ x₁ ∘ k i ] ≡ y₁)
              ) [ f'-cond ≡ f-cond ]
            h = lemPropF prp _ _ k
            res : (f' , f'-cond) ≡ (f , f-cond)
            res = Σ≡ (k , h)
        t : IsTerminal 𝒳
        t {𝒴} = 𝒻 , contractible
      ve-re : ∀ x → g (f x) ≡ x
      ve-re x = Propositionality.propTerminal _ _
      re-ve : ∀ p → f (g p) ≡ p
      re-ve p = Product≡ e
        where
        module p = Product p
        -- RawProduct does not have eta-equality.
        e : Product.raw (f (g p)) ≡ Product.raw p
        RawProduct.object (e i) = p.object
        RawProduct.fst (e i) = p.fst
        RawProduct.snd (e i) = p.snd
      inv : AreInverses f g
      inv = funExt ve-re , funExt re-ve

  propProduct : isProp (Product ℂ 𝒜 ℬ)
  propProduct = equivPreservesNType 1 lemma Propositionality.propTerminal

module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} {A B : Category.Object ℂ} where
  open Category ℂ
  private
    module _ (x y : HasProducts ℂ) where
      private
        module x = HasProducts x
        module y = HasProducts y

      productEq : x.product ≡ y.product
      productEq = funExt λ A → funExt λ B → propProduct _ _

  propHasProducts : isProp (HasProducts ℂ)
  propHasProducts x y i = record { product = productEq x y i }
