{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Category.Product where

open import Cubical.NType.Properties
open import Cat.Prelude as P hiding (_×_ ; fst ; snd)
-- module P = Cat.Prelude

open import Cat.Category

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where

  open Category ℂ

  module _ (A B : Object) where
    record RawProduct : Set (ℓa ⊔ ℓb) where
      no-eta-equality
      field
        object : Object
        fst  : ℂ [ object , A ]
        snd  : ℂ [ object , B ]

    -- FIXME Not sure this is actually a proposition - so this name is
    -- misleading.
    record IsProduct (raw : RawProduct) : Set (ℓa ⊔ ℓb) where
      open RawProduct raw public
      field
        ump : ∀ {X : Object} (f : ℂ [ X , A ]) (g : ℂ [ X , B ])
          → ∃![ f×g ] (ℂ [ fst ∘ f×g ] ≡ f P.× ℂ [ snd ∘ f×g ] ≡ g)

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

module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} {A B : Category.Object ℂ} where
  private
    open Category ℂ
    module _ (raw : RawProduct ℂ A B) where
      module _ (x y : IsProduct ℂ A B raw) where
        private
          module x = IsProduct x
          module y = IsProduct y

        module _ {X : Object} (f : ℂ [ X , A ]) (g : ℂ [ X , B ]) where
          module _ (f×g : Arrow X y.object) where
            help : isProp (∀{y} → (ℂ [ y.fst ∘ y ] ≡ f) P.× (ℂ [ y.snd ∘ y ] ≡ g) → f×g ≡ y)
            help = propPiImpl (λ _ → propPi (λ _ → arrowsAreSets _ _))

          res = ∃-unique (x.ump f g) (y.ump f g)

          prodAux : x.ump f g ≡ y.ump f g
          prodAux = lemSig ((λ f×g → propSig (propSig (arrowsAreSets _ _) λ _ → arrowsAreSets _ _) (λ _ → help f×g))) _ _ res

        propIsProduct' : x ≡ y
        propIsProduct' i = record { ump = λ f g → prodAux f g i }

      propIsProduct : isProp (IsProduct ℂ A B raw)
      propIsProduct = propIsProduct'

  Product≡ : {x y : Product ℂ A B} → (Product.raw x ≡ Product.raw y) → x ≡ y
  Product≡ {x} {y} p i = record { raw = p i ; isProduct = q i }
    where
    q : (λ i → IsProduct ℂ A B (p i)) [ Product.isProduct x ≡ Product.isProduct y ]
    q = lemPropF propIsProduct p

module Try0 {ℓa ℓb : Level} {ℂ : Category ℓa ℓb}
  (let module ℂ = Category ℂ) {A B : ℂ.Object} where

  open P

  module _ where
    raw : RawCategory _ _
    raw = record
      { Object = Σ[ X ∈ ℂ.Object ] ℂ.Arrow X A × ℂ.Arrow X B
      ; Arrow = λ{ (X , x0 , x1) (Y , y0 , y1)
        → Σ[ f ∈ ℂ.Arrow X Y ]
            ℂ [ y0 ∘ f ] ≡ x0
          × ℂ [ y1 ∘ f ] ≡ x1
          }
      ; identity = λ{ {X , f , g} → ℂ.identity {X} , ℂ.rightIdentity , ℂ.rightIdentity}
      ; _∘_ = λ { {_ , a0 , a1} {_ , b0 , b1} {_ , c0 , c1} (f , f0 , f1) (g , g0 , g1)
        → (f ℂ.∘ g)
          , (begin
              ℂ [ c0 ∘ ℂ [ f ∘ g ] ] ≡⟨ ℂ.isAssociative ⟩
              ℂ [ ℂ [ c0 ∘ f ] ∘ g ] ≡⟨ cong (λ φ → ℂ [ φ ∘ g ]) f0 ⟩
              ℂ [ b0 ∘ g ] ≡⟨ g0 ⟩
              a0 ∎
            )
          , (begin
             ℂ [ c1 ∘ ℂ [ f ∘ g ] ] ≡⟨ ℂ.isAssociative ⟩
             ℂ [ ℂ [ c1 ∘ f ] ∘ g ] ≡⟨ cong (λ φ → ℂ [ φ ∘ g ]) f1 ⟩
             ℂ [ b1 ∘ g ] ≡⟨ g1 ⟩
              a1 ∎
            )
        }
      }

    module _ where
      private
        open RawCategory raw

        propEqs : ∀ {X' : Object}{Y' : Object} (let X , xa , xb = X') (let Y , ya , yb = Y')
                  → (xy : ℂ.Arrow X Y) → isProp (ℂ [ ya ∘ xy ] ≡ xa × ℂ [ yb ∘ xy ] ≡ xb)
        propEqs xs = propSig (ℂ.arrowsAreSets _ _) (\ _ → ℂ.arrowsAreSets _ _)

        isAssociative : IsAssociative
        isAssociative {A'@(A , a0 , a1)} {B , _} {C , c0 , c1} {D'@(D , d0 , d1)} {ff@(f , f0 , f1)} {gg@(g , g0 , g1)} {hh@(h , h0 , h1)} i
          = s0 i , lemPropF propEqs s0 {P.snd l} {P.snd r} i
          where
          l = hh ∘ (gg ∘ ff)
          r = hh ∘ gg ∘ ff
          -- s0 : h ℂ.∘ (g ℂ.∘ f) ≡ h ℂ.∘ g ℂ.∘ f
          s0 : fst l ≡ fst r
          s0 = ℂ.isAssociative {f = f} {g} {h}


        isIdentity : IsIdentity identity
        isIdentity {AA@(A , a0 , a1)} {BB@(B , b0 , b1)} {f , f0 , f1} = leftIdentity , rightIdentity
          where
          leftIdentity : identity ∘ (f , f0 , f1) ≡ (f , f0 , f1)
          leftIdentity i = l i , lemPropF propEqs l {snd L} {snd R} i
            where
            L = identity ∘ (f , f0 , f1)
            R : Arrow AA BB
            R = f , f0 , f1
            l : fst L ≡ fst R
            l = ℂ.leftIdentity
          rightIdentity : (f , f0 , f1) ∘ identity ≡ (f , f0 , f1)
          rightIdentity i = l i , lemPropF propEqs l {snd L} {snd R} i
            where
            L = (f , f0 , f1) ∘ identity
            R : Arrow AA BB
            R = (f , f0 , f1)
            l : ℂ [ f ∘ ℂ.identity ] ≡ f
            l = ℂ.rightIdentity

        arrowsAreSets : ArrowsAreSets
        arrowsAreSets {X , x0 , x1} {Y , y0 , y1}
          = sigPresNType {n = ⟨0⟩} ℂ.arrowsAreSets λ a → propSet (propEqs _)

      isPreCat : IsPreCategory raw
      IsPreCategory.isAssociative isPreCat = isAssociative
      IsPreCategory.isIdentity    isPreCat = isIdentity
      IsPreCategory.arrowsAreSets isPreCat = arrowsAreSets

    open IsPreCategory isPreCat

    univalent : Univalent
    univalent {(X , xa , xb)} {(Y , ya , yb)} = univalenceFromIsomorphism res
      where
      open import Cat.Equivalence using (composeIso) renaming (_≅_ to _≈_)
      -- open import Relation.Binary.PreorderReasoning (Cat.Equivalence.preorder≅ {!!}) using ()
      --   renaming
      --     ( _∼⟨_⟩_ to _≈⟨_⟩_
      --     ; begin_ to begin!_
      --     ; _∎ to _∎! )
      -- lawl
      --   : ((X , xa , xb) ≡ (Y , ya , yb))
      --   ≈ (Σ[ iso ∈ (X ℂ.≅ Y) ] let p = ℂ.iso-to-id iso in (PathP (λ i → ℂ.Arrow (p i) A) xa ya) × (PathP (λ i → ℂ.Arrow (p i) B) xb yb))
      -- lawl = {!begin! ? ≈⟨ ? ⟩ ? ∎!!}
      -- Problem with the above approach: Preorders only work for heterogeneous equaluties.

      -- (X , xa , xb) ≡ (Y , ya , yb)
      -- ≅
      -- Σ[ p ∈ (X ≡ Y) ] (PathP (λ i → ℂ.Arrow (p i) A) xa ya) × (PathP (λ i → ℂ.Arrow (p i) B) xb yb)
      -- ≅
      -- Σ (X ℂ.≅ Y) (λ iso
      --   → let p = ℂ.iso-to-id iso
      --   in
      --   ( PathP (λ i → ℂ.Arrow (p i) A) xa ya)
      --   × PathP (λ i → ℂ.Arrow (p i) B) xb yb
      --   )
      -- ≅
      -- (X , xa , xb) ≅ (Y , ya , yb)
      step0
        : ((X , xa , xb) ≡ (Y , ya , yb))
        ≈ (Σ[ p ∈ (X ≡ Y) ] (PathP (λ i → ℂ.Arrow (p i) A) xa ya) × (PathP (λ i → ℂ.Arrow (p i) B) xb yb))
      step0
        = (λ p → (λ i → fst (p i)) , (λ i → fst (snd (p i))) , (λ i → snd (snd (p i))))
        , (λ x  → λ i → fst x i , (fst (snd x) i) , (snd (snd x) i))
        , record
          { verso-recto = {!!}
          ; recto-verso = {!!}
          }
      step1
        : (Σ[ p ∈ (X ≡ Y) ] (PathP (λ i → ℂ.Arrow (p i) A) xa ya) × (PathP (λ i → ℂ.Arrow (p i) B) xb yb))
        ≈ Σ (X ℂ.≅ Y) (λ iso
          → let p = ℂ.iso-to-id iso
          in
          ( PathP (λ i → ℂ.Arrow (p i) A) xa ya)
          × PathP (λ i → ℂ.Arrow (p i) B) xb yb
          )
      step1
        = (λ{ (p , x) → (ℂ.idToIso _ _ p) , {!snd x!}})
        -- Goal is:
        --
        --     φ x
        --
        -- where `x` is
        --
        --   ℂ.iso-to-id (ℂ.idToIso _ _ p)
        --
        -- I have `φ p` in scope, but surely `p` and `x` are the same - though
        -- perhaps not definitonally.
        , (λ{ (iso , x) → ℂ.iso-to-id iso , x})
        , record { verso-recto = {!!} ; recto-verso = {!!} }
      lemA : {A B : Object} {f g : Arrow A B} → fst f ≡ fst g → f ≡ g
      lemA {A} {B} {f = f} {g} p i = p i , h i
        where
        h : PathP (λ i →
            (ℂ [ fst (snd B) ∘ p i ]) ≡ fst (snd A) ×
            (ℂ [ snd (snd B) ∘ p i ]) ≡ snd (snd A)
          ) (snd f) (snd g)
        h = lemPropF (λ a → propSig
          (ℂ.arrowsAreSets (ℂ [ fst (snd B) ∘ a ]) (fst (snd A)))
          λ _ → ℂ.arrowsAreSets (ℂ [ snd (snd B) ∘ a ]) (snd (snd A)))
          p
      step2
        : Σ (X ℂ.≅ Y) (λ iso
          → let p = ℂ.iso-to-id iso
          in
          ( PathP (λ i → ℂ.Arrow (p i) A) xa ya)
          × PathP (λ i → ℂ.Arrow (p i) B) xb yb
          )
        ≈ ((X , xa , xb) ≅ (Y , ya , yb))
      step2
        = ( λ{ ((f , f~ , inv-f) , x)
            → ( f , {!!})
            , ( (f~ , {!!})
              , lemA {!!}
              , lemA {!!}
              )
            }
          )
        , (λ x → {!!})
        , {!!}
      -- One thing to watch out for here is that the isomorphisms going forwards
      -- must compose to give idToIso
      iso
        : ((X , xa , xb) ≡ (Y , ya , yb))
        ≈ ((X , xa , xb) ≅ (Y , ya , yb))
      iso = step0 ⊙ step1 ⊙ step2
        where
        infixl 5 _⊙_
        _⊙_ = composeIso
      res : TypeIsomorphism (idToIso (X , xa , xb) (Y , ya , yb))
      res = {!snd iso!}

    isCat : IsCategory raw
    IsCategory.isPreCategory isCat = isPreCat
    IsCategory.univalent     isCat = univalent

    cat : Category _ _
    cat = record
      { raw = raw
      ; isCategory = isCat
      }

  open Category cat

  open import Cat.Equivalence

  lemma : Terminal ≃ Product ℂ A B
  lemma = Equiv≃.fromIsomorphism Terminal (Product ℂ A B) (f , g , inv)
    where
    f : Terminal → Product ℂ A B
    f ((X , x0 , x1) , uniq) = p
      where
      rawP : RawProduct ℂ A B
      rawP = record
        { object = X
        ; fst = x0
        ; snd = x1
        }
      -- open RawProduct rawP renaming (fst to x0 ; snd to x1)
      module _ {Y : ℂ.Object} (p0 : ℂ [ Y , A ]) (p1 : ℂ [ Y , B ]) where
        uy : isContr (Arrow (Y , p0 , p1) (X , x0 , x1))
        uy = uniq {Y , p0 , p1}
        open Σ uy renaming (fst to Y→X ; snd to contractible)
        open Σ Y→X renaming (fst to p0×p1 ; snd to cond)
        ump : ∃![ f×g ] (ℂ [ x0 ∘ f×g ] ≡ p0 P.× ℂ [ x1 ∘ f×g ] ≡ p1)
        ump = p0×p1 , cond , λ {y} x → let k = contractible (y , x) in λ i → fst (k i)
      isP : IsProduct ℂ A B rawP
      isP = record { ump = ump }
      p : Product ℂ A B
      p = record
        { raw = rawP
        ; isProduct = isP
        }
    g : Product ℂ A B → Terminal
    g p = o , t
      where
      module p = Product p
      module isp = IsProduct p.isProduct
      o : Object
      o = p.object , p.fst , p.snd
      module _ {Xx : Object} where
        open Σ Xx renaming (fst to X ; snd to x)
        ℂXo : ℂ [ X , isp.object ]
        ℂXo = isp._P[_×_] (fst x) (snd x)
        ump = p.ump (fst x) (snd x)
        Xoo = fst (snd ump)
        Xo : Arrow Xx o
        Xo = ℂXo , Xoo
        contractible : ∀ y → Xo ≡ y
        contractible (y , yy) = res
          where
          k : ℂXo ≡ y
          k = snd (snd ump) (yy)
          prp : ∀ a → isProp
            ( (ℂ [ p.fst ∘ a ] ≡ fst x)
            × (ℂ [ p.snd ∘ a ] ≡ snd x)
            )
          prp ab ac ad i
            = ℂ.arrowsAreSets _ _ (fst ac) (fst ad) i
            , ℂ.arrowsAreSets _ _ (snd ac) (snd ad) i
          h :
            ( λ i
              → ℂ [ p.fst ∘ k i ] ≡ fst x
              × ℂ [ p.snd ∘ k i ] ≡ snd x
            ) [ Xoo ≡ yy ]
          h = lemPropF prp k
          res : (ℂXo , Xoo) ≡ (y , yy)
          res i = k i , h i
      t : IsTerminal o
      t {Xx} = Xo , contractible
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
    inv = record
      { verso-recto = funExt ve-re
      ; recto-verso = funExt re-ve
      }

  propProduct : isProp (Product ℂ A B)
  propProduct = equivPreservesNType {n = ⟨-1⟩} lemma Propositionality.propTerminal

module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} {A B : Category.Object ℂ} where
  open Category ℂ
  private
    module _ (x y : HasProducts ℂ) where
      private
        module x = HasProducts x
        module y = HasProducts y

      productEq : x.product ≡ y.product
      productEq = funExt λ A → funExt λ B → Try0.propProduct _ _

  propHasProducts : isProp (HasProducts ℂ)
  propHasProducts x y i = record { product = productEq x y i }

fmap≡ : {A : Set} {a0 a1 : A} {B : Set} → (f : A → B) → Path a0 a1 → Path (f a0) (f a1)
fmap≡ = cong
