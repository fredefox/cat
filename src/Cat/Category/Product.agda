{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Category.Product where

open import Cubical.NType.Properties
open import Cat.Prelude hiding (_×_ ; proj₁ ; proj₂)
import Data.Product as P

open import Cat.Category

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where

  open Category ℂ

  module _ (A B : Object) where
    record RawProduct : Set (ℓa ⊔ ℓb) where
      no-eta-equality
      field
        object : Object
        proj₁  : ℂ [ object , A ]
        proj₂  : ℂ [ object , B ]

    -- FIXME Not sure this is actually a proposition - so this name is
    -- misleading.
    record IsProduct (raw : RawProduct) : Set (ℓa ⊔ ℓb) where
      open RawProduct raw public
      field
        ump : ∀ {X : Object} (f : ℂ [ X , A ]) (g : ℂ [ X , B ])
          → ∃![ f×g ] (ℂ [ proj₁ ∘ f×g ] ≡ f P.× ℂ [ proj₂ ∘ f×g ] ≡ g)

      -- | Arrow product
      _P[_×_] : ∀ {X} → (π₁ : ℂ [ X , A ]) (π₂ : ℂ [ X , B ])
        → ℂ [ X , object ]
      _P[_×_] π₁ π₂ = P.proj₁ (ump π₁ π₂)

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
      open Product
      open Product (product A B) hiding (_P[_×_]) renaming (proj₁ to fst ; proj₂ to snd)
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
          prodAux : x.ump f g ≡ y.ump f g
          prodAux = {!!}

        propIsProduct' : x ≡ y
        propIsProduct' i = record { ump = λ f g → prodAux f g i }

      propIsProduct : isProp (IsProduct ℂ A B raw)
      propIsProduct = propIsProduct'

  Product≡ : {x y : Product ℂ A B} → (Product.raw x ≡ Product.raw y) → x ≡ y
  Product≡ {x} {y} p i = record { raw = p i ; isProduct = q i }
    where
    q : (λ i → IsProduct ℂ A B (p i)) [ Product.isProduct x ≡ Product.isProduct y ]
    q = lemPropF propIsProduct p

module _ {ℓa ℓb : Level} {ℂ : Category ℓa ℓb} {A B : Category.Object ℂ} where
  open Category ℂ
  private
    module _ (x y : HasProducts ℂ) where
      private
        module x = HasProducts x
        module y = HasProducts y
      module _ (A B : Object) where
        module pX = Product (x.product A B)
        module pY = Product (y.product A B)
        objEq : pX.object ≡ pY.object
        objEq = {!!}
        proj₁Eq : (λ i → ℂ [ objEq i , A ]) [ pX.proj₁ ≡ pY.proj₁ ]
        proj₁Eq = {!!}
        proj₂Eq : (λ i → ℂ [ objEq i , B ]) [ pX.proj₂ ≡ pY.proj₂ ]
        proj₂Eq = {!!}
        rawEq : pX.raw ≡ pY.raw
        RawProduct.object (rawEq i) = objEq i
        RawProduct.proj₁  (rawEq i) = {!!}
        RawProduct.proj₂  (rawEq i) = {!!}

        isEq : (λ i → IsProduct ℂ A B (rawEq i)) [ pX.isProduct ≡ pY.isProduct ]
        isEq = {!!}

        appEq : x.product A B ≡ y.product A B
        appEq = Product≡ rawEq

      productEq : x.product ≡ y.product
      productEq i = λ A B → appEq A B i

      propHasProducts' : x ≡ y
      propHasProducts' i = record { product = productEq i }

  propHasProducts : isProp (HasProducts ℂ)
  propHasProducts = propHasProducts'

module Try0 {ℓa ℓb : Level} {ℂ : Category ℓa ℓb}
  (let module ℂ = Category ℂ) {A B : ℂ.Object} where

  open import Data.Product

  module _ where
    raw : RawCategory _ _
    raw = record
      { Object = Σ[ X ∈ ℂ.Object ] ℂ.Arrow X A × ℂ.Arrow X B
      ; Arrow = λ{ (X , xa , xb) (Y , ya , yb)
        → Σ[ xy ∈ ℂ.Arrow X Y ]
          ( ℂ [ ya ∘ xy ] ≡ xa)
          × ℂ [ yb ∘ xy ] ≡ xb
          }
      ; identity = λ{ {A , f , g} → ℂ.identity {A} , ℂ.rightIdentity , ℂ.rightIdentity}
      ; _∘_ = λ { {A , a0 , a1} {B , b0 , b1} {C , c0 , c1} (f , f0 , f1) (g , g0 , g1)
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

    open RawCategory raw

    propEqs : ∀ {X' : Object}{Y' : Object} (let X , xa , xb = X') (let Y , ya , yb = Y')
              → (xy : ℂ.Arrow X Y) → isProp (ℂ [ ya ∘ xy ] ≡ xa × ℂ [ yb ∘ xy ] ≡ xb)
    propEqs xs = propSig (ℂ.arrowsAreSets _ _) (\ _ → ℂ.arrowsAreSets _ _)

    isAssocitaive : IsAssociative
    isAssocitaive {A'@(A , a0 , a1)} {B , _} {C , c0 , c1} {D'@(D , d0 , d1)} {ff@(f , f0 , f1)} {gg@(g , g0 , g1)} {hh@(h , h0 , h1)} i
      = s0 i , lemPropF propEqs s0 {proj₂ l} {proj₂ r} i
      where
      l = hh ∘ (gg ∘ ff)
      r = hh ∘ gg ∘ ff
      -- s0 : h ℂ.∘ (g ℂ.∘ f) ≡ h ℂ.∘ g ℂ.∘ f
      s0 : proj₁ l ≡ proj₁ r
      s0 = ℂ.isAssociative {f = f} {g} {h}


    isIdentity : IsIdentity identity
    isIdentity {AA@(A , a0 , a1)} {BB@(B , b0 , b1)} {f , f0 , f1} = leftIdentity , rightIdentity
      where
      leftIdentity : identity ∘ (f , f0 , f1) ≡ (f , f0 , f1)
      leftIdentity i = l i , lemPropF propEqs l {proj₂ L} {proj₂ R} i
        where
        L = identity ∘ (f , f0 , f1)
        R : Arrow AA BB
        R = f , f0 , f1
        l : proj₁ L ≡ proj₁ R
        l = ℂ.leftIdentity
      rightIdentity : (f , f0 , f1) ∘ identity ≡ (f , f0 , f1)
      rightIdentity i = l i , lemPropF propEqs l {proj₂ L} {proj₂ R} i
        where
        L = (f , f0 , f1) ∘ identity
        R : Arrow AA BB
        R = (f , f0 , f1)
        l : ℂ [ f ∘ ℂ.identity ] ≡ f
        l = ℂ.rightIdentity

    arrowsAreSets : ArrowsAreSets
    arrowsAreSets {X , x0 , x1} {Y , y0 , y1} (f , f0 , f1) (g , g0 , g1) p q = {!!}
      where
      prop : ∀ {X Y} (x y : ℂ.Arrow X Y) → isProp (x ≡ y)
      prop = ℂ.arrowsAreSets
      a0 a1 : f ≡ g
      a0 i = proj₁ (p i)
      a1 i = proj₁ (q i)
      a : a0 ≡ a1
      a = ℂ.arrowsAreSets _ _ a0 a1
      res : p ≡ q
      res i j = a i j , {!b i j!} , {!!}
        where
        -- b0 b1 : (λ j → (ℂ [ y0 ∘ a i j ]) ≡ x0) [ f0 ≡ g0 ]
        -- b0 = lemPropF (λ x → prop (ℂ [ y0 ∘ x ]) x0) (a i)
        -- b1 = lemPropF (λ x → prop (ℂ [ y0 ∘ x ]) x0) (a i)
        b0 : (λ j → (ℂ [ y0 ∘ a0 j ]) ≡ x0) [ f0 ≡ g0 ]
        b0 = lemPropF (λ x → prop (ℂ [ y0 ∘ x ]) x0) a0
        b1 : (λ j → (ℂ [ y0 ∘ a1 j ]) ≡ x0) [ f0 ≡ g0 ]
        b1 = lemPropF (λ x → prop (ℂ [ y0 ∘ x ]) x0) a1
        -- b : b0 ≡ b1
        -- b = {!!}

    isCat : IsCategory raw
    isCat = record
      { isAssociative = isAssocitaive
      ; isIdentity    = isIdentity
      ; arrowsAreSets = arrowsAreSets
      ; univalent     = {!!}
      }

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
        ; proj₁ = x0
        ; proj₂ = x1
        }
      -- open RawProduct rawP renaming (proj₁ to x0 ; proj₂ to x1)
      module _ {Y : ℂ.Object} (p0 : ℂ [ Y , A ]) (p1 : ℂ [ Y , B ]) where
        uy : isContr (Arrow (Y , p0 , p1) (X , x0 , x1))
        uy = uniq {Y , p0 , p1}
        open Σ uy renaming (proj₁ to Y→X ; proj₂ to contractible)
        open Σ Y→X renaming (proj₁ to p0×p1 ; proj₂ to cond)
        ump : ∃![ f×g ] (ℂ [ x0 ∘ f×g ] ≡ p0 P.× ℂ [ x1 ∘ f×g ] ≡ p1)
        ump = p0×p1 , cond , λ {y} x → let k = contractible (y , x) in λ i → proj₁ (k i)
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
      o = p.object , p.proj₁ , p.proj₂
      module _ {Xx : Object} where
        open Σ Xx renaming (proj₁ to X ; proj₂ to x)
        ℂXo : ℂ [ X , isp.object ]
        ℂXo = isp._P[_×_] (proj₁ x) (proj₂ x)
        ump = p.ump (proj₁ x) (proj₂ x)
        Xoo = proj₁ (proj₂ ump)
        Xo : Arrow Xx o
        Xo = ℂXo , Xoo
        contractible : ∀ y → Xo ≡ y
        contractible (y , yy) = res
          where
          k : ℂXo ≡ y
          k = proj₂ (proj₂ ump) (yy)
          prp : ∀ a → isProp
            ( (ℂ [ p.proj₁ ∘ a ] ≡ proj₁ x)
            × (ℂ [ p.proj₂ ∘ a ] ≡ proj₂ x)
            )
          prp ab ac ad i
            = ℂ.arrowsAreSets _ _ (proj₁ ac) (proj₁ ad) i
            , ℂ.arrowsAreSets _ _ (proj₂ ac) (proj₂ ad) i
          h :
            ( λ i
              → ℂ [ p.proj₁ ∘ k i ] ≡ proj₁ x
              × ℂ [ p.proj₂ ∘ k i ] ≡ proj₂ x
            ) [ Xoo ≡ yy ]
          h = lemPropF prp k
          res : (ℂXo , Xoo) ≡ (y , yy)
          res i = k i , h i
      t : IsTerminal o
      t {Xx} = Xo , contractible
    ve-re : ∀ x → g (f x) ≡ x
    ve-re x = Propositionality.propTerminal _ _
    re-ve : ∀ x → f (g x) ≡ x
    re-ve x = {!!}
    inv : AreInverses f g
    inv = record
      { verso-recto = funExt ve-re
      ; recto-verso = funExt re-ve
      }

  thm : isProp (Product ℂ A B)
  thm = equivPreservesNType {n = ⟨-1⟩} lemma Propositionality.propTerminal
