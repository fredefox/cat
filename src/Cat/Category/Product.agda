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

    -- module _ (X : Object) where
    --   center : Σ Object (X ≅_)
    --   center = X , idIso X

    --   module _ (y : Σ Object (X ≅_)) where
    --     open Σ y renaming (fst to Y ; snd to X≅Y)

    --     contractible : (X , idIso X) ≡ (Y , X≅Y)
    --     contractible = {!!}

    --   univalent[Contr] : isContr (Σ Object (X ≅_))
    --   univalent[Contr] = center , contractible
    --   module _ (y : Σ Object (X ≡_)) where
    --     open Σ y renaming (fst to Y ; snd to p)
    --     a0 : X ≡ Y
    --     a0 = {!!}
    --     a1 : PathP (λ i → X ≡ a0 i) refl p
    --     a1 = {!!}
    --       where
    --       P : (Z : Object) → X ≡ Z → Set _
    --       P Z p = PathP (λ i → X ≡ Z)

    --     alt' : (X , refl) ≡ y
    --     alt' i = a0 i , a1 i
    --   alt : isContr (Σ Object (X ≡_))
    --   alt = (X , refl) , alt'

    univalent : Univalent
    univalent {X , x} {Y , y} = {!res!}
      where
      open import Cat.Equivalence as E hiding (_≅_)
      open import Cubical.Univalence
      module _ (c : (X , x) ≅ (Y , y)) where
      -- module _ (c : _ ≅ _) where
        open Σ c renaming (fst to f_c ; snd to inv_c)
        open Σ inv_c renaming (fst to g_c ; snd to ainv_c)
        open Σ ainv_c renaming (fst to left ; snd to right)
        c0 : X ℂ.≅ Y
        c0 = fst f_c , fst g_c , (λ i → fst (left i)) , (λ i → fst (right i))
        f0 : X ≡ Y
        f0 = ℂ.iso-to-id c0
        module _ {A : ℂ.Object} (α : ℂ.Arrow X A) where
          coedom : ℂ.Arrow Y A
          coedom = coe (λ i → ℂ.Arrow (f0 i) A) α
        coex : ℂ.Arrow Y A × ℂ.Arrow Y B
        coex = coe (λ i → ℂ.Arrow (f0 i) A × ℂ.Arrow (f0 i) B) x
        f1 : PathP (λ i → ℂ.Arrow (f0 i) A × ℂ.Arrow (f0 i) B) x coex
        f1 = {!sym!}
        f2 : coex ≡ y
        f2 = {!!}
        f : (X , x) ≡ (Y , y)
        f i = f0 i , {!f1 i!}
      prp : isSet (ℂ.Object × ℂ.Arrow Y A × ℂ.Arrow Y B)
      prp = setSig {sA = {!!}} {(λ _ → setSig {sA = ℂ.arrowsAreSets} {λ _ → ℂ.arrowsAreSets})}
      ve-re : (p : (X , x) ≡ (Y , y)) → f (idToIso _ _ p) ≡ p
      -- ve-re p i j = {!ℂ.arrowsAreSets!} , ℂ.arrowsAreSets _ _ (let k = fst (snd (p i)) in {!!}) {!!} {!!} {!!} , {!!}
      ve-re p = let k = prp {!!} {!!} {!!} {!p!} in {!!}
      re-ve : (iso : (X , x) ≅ (Y , y)) → idToIso _ _ (f iso) ≡ iso
      re-ve = {!!}
      iso : E.Isomorphism (idToIso (X , x) (Y , y))
      iso = f , record { verso-recto = funExt ve-re ; recto-verso = funExt re-ve }
      res : isEquiv ((X , x) ≡ (Y , y)) ((X , x) ≅ (Y , y)) (idToIso (X , x) (Y , y))
      res = Equiv≃.fromIso _ _ iso

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
