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
          module _ (f×g : Arrow X y.object) where
            help : isProp (∀{y} → (ℂ [ y.proj₁ ∘ y ] ≡ f) P.× (ℂ [ y.proj₂ ∘ y ] ≡ g) → f×g ≡ y)
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

  open import Data.Product

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
    arrowsAreSets {X , x0 , x1} {Y , y0 , y1}
      = sigPresNType {n = ⟨0⟩} ℂ.arrowsAreSets λ a → propSet (propEqs _)

    open Univalence isIdentity

    module _ (A : Object) where
      c : Σ Object (A ≅_)
      c = A , {!!}
      univalent[Contr] : isContr (Σ Object (A ≅_))
      univalent[Contr] = {!!} , {!!}

    univalent' : Univalent[Contr]
    univalent' = univalence-lemma p q
      where
      module _ {𝕏 : Object} where
        open Σ 𝕏    renaming (proj₁ to X ; proj₂ to x0x1)
        open Σ x0x1 renaming (proj₁ to x0 ; proj₂ to x1)
        -- x0 : X → A in ℂ
        -- x1 : X → B in ℂ
        module _ (𝕐-isoY : Σ Object (𝕏 ≅_)) where
          open Σ 𝕐-isoY  renaming (proj₁ to 𝕐  ; proj₂ to isoY)
          open Σ 𝕐       renaming (proj₁ to Y  ; proj₂ to y0y1)
          open Σ y0y1    renaming (proj₁ to y0 ; proj₂ to y1)
          open Σ isoY    renaming (proj₁ to 𝓯  ; proj₂ to iso-𝓯)
          open Σ iso-𝓯   renaming (proj₁ to 𝓯~ ; proj₂ to inv-𝓯)
          open Σ 𝓯       renaming (proj₁ to f  ; proj₂ to inv-f)
          open Σ 𝓯~      renaming (proj₁ to f~ ; proj₂ to inv-f~)
          open Σ inv-𝓯   renaming (proj₁ to left ; proj₂ to right)
          -- y0 : Y → A in ℂ
          -- y1 : Y → B in ℂ
          -- f  : X → Y in ℂ
          -- inv-f : ℂ [ y0 ∘ f ] ≡ x0 × ℂ [ y1 ∘ f ] ≡ x1
          -- left  : 𝓯~ ∘ 𝓯  ≡ identity
          -- left~ : 𝓯  ∘ 𝓯~ ≡ identity
          isoℂ : X ℂ.≅ Y
          isoℂ
            = f
            , f~
            , ( begin
                ℂ [ f~ ∘ f ] ≡⟨ (λ i → proj₁ (left i)) ⟩
                ℂ.identity ∎
              )
            , ( begin
                ℂ [ f ∘ f~ ] ≡⟨ (λ i → proj₁ (right i)) ⟩
                ℂ.identity ∎
              )
          p0 : X ≡ Y
          p0 = ℂ.iso-to-id isoℂ
          -- I note `left2` and right2` here as a reminder.
          left2 : PathP
            (λ i → ℂ [ x0 ∘ proj₁ (left i) ] ≡ x0 × ℂ [ x1 ∘ proj₁ (left i) ] ≡ x1)
            (proj₂ (𝓯~ ∘ 𝓯)) (proj₂ identity)
          left2 i = proj₂ (left i)
          right2 : PathP
            (λ i → ℂ [ y0 ∘ proj₁ (right i) ] ≡ y0 × ℂ [ y1 ∘ proj₁ (right i) ] ≡ y1)
            (proj₂ (𝓯 ∘ 𝓯~)) (proj₂ identity)
          right2 i = proj₂ (right i)
          -- My idea:
          --
          -- x0, x1 and y0 and y1 are product arrows as in the diagram
          --
          --     X
          --   ↙  ↘
          -- A  ⇣ ⇡  B
          --   ↖  ↗
          --     Y    (All hail unicode)
          --
          -- The dotted lines indicate the unique product arrows. Since they are
          -- unique they necessarily be each others inverses. Alas, more than
          -- this we must show that they are actually (heterogeneously)
          -- identical as in `p1`:
          p1 : PathP (λ i → ℂ.Arrow (p0 i) A × ℂ.Arrow (p0 i) B) x0x1 y0y1
          p1 = {!!}
            where
            -- This, however, should probably somehow follow from them being
            -- inverses on objects that are propositionally equal cf. `p0`.
            helper : {A B : Object} {f : Arrow A B} {g : Arrow B A}
              → IsInverseOf f g
              → (p : A ≡ B)
              → PathP (λ i → Arrow (p i) (p (~ i))) f g
            helper = {!!}

          p : (X , x0x1) ≡ (Y , y0y1)
          p i = p0 i , {!!}
        module _ (iso : 𝕏 ≅ 𝕏) where
          open Σ iso renaming (proj₁ to 𝓯 ; proj₂ to inv-𝓯)
          open Σ inv-𝓯 renaming (proj₁ to 𝓯~) using ()
          open Σ 𝓯  renaming (proj₁ to f  ; proj₂ to inv-f)
          open Σ 𝓯~ renaming (proj₁ to f~ ; proj₂ to inv-f~)
          q0' : ℂ.identity ≡ f
          q0' i = {!!}
          prop : ∀ x → isProp (ℂ [ x0 ∘ x ] ≡ x0 × ℂ [ x1 ∘ x ] ≡ x1)
          prop x = propSig
            (      ℂ.arrowsAreSets (ℂ [ x0 ∘ x ]) x0)
            (λ _ → ℂ.arrowsAreSets (ℂ [ x1 ∘ x ]) x1)
          q0'' : PathP (λ i → ℂ [ x0 ∘ q0' i ] ≡ x0 × ℂ [ x1 ∘ q0' i ] ≡ x1) (proj₂ identity) inv-f
          q0'' = lemPropF prop q0'
          q0 : identity ≡ 𝓯
          q0 i = q0' i , q0'' i
          q1' : ℂ.identity ≡ f~
          q1' = {!!}
          q1'' : PathP (λ i → (ℂ [ x0 ∘ q1' i ]) ≡ x0 × (ℂ [ x1 ∘ q1' i ]) ≡ x1) (proj₂ identity) inv-f~
          q1'' = lemPropF prop q1'
          q1 : identity ≡ 𝓯~
          q1 i = q1' i , {!!}
          q : (identity , identity) ≡ (𝓯 , 𝓯~)
          q i = q0 i , q1 i

    univalent : Univalent
    univalent {X , x} {Y , y} = {!res!}
      where
      open import Cat.Equivalence as E hiding (_≅_)
      open import Cubical.Univalence
      module _ (c : (X , x) ≅ (Y , y)) where
      -- module _ (c : _ ≅ _) where
        open Σ c renaming (proj₁ to f_c ; proj₂ to inv_c)
        open Σ inv_c renaming (proj₁ to g_c ; proj₂ to ainv_c)
        open Σ ainv_c renaming (proj₁ to left ; proj₂ to right)
        c0 : X ℂ.≅ Y
        c0 = proj₁ f_c , proj₁ g_c , (λ i → proj₁ (left i)) , (λ i → proj₁ (right i))
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
      ve-re : (p : (X , x) ≡ (Y , y)) → f (id-to-iso _ _ p) ≡ p
      -- ve-re p i j = {!ℂ.arrowsAreSets!} , ℂ.arrowsAreSets _ _ (let k = proj₁ (proj₂ (p i)) in {!!}) {!!} {!!} {!!} , {!!}
      ve-re p = let k = prp {!!} {!!} {!!} {!p!} in {!!}
      re-ve : (iso : (X , x) ≅ (Y , y)) → id-to-iso _ _ (f iso) ≡ iso
      re-ve = {!!}
      iso : E.Isomorphism (id-to-iso (X , x) (Y , y))
      iso = f , record { verso-recto = funExt ve-re ; recto-verso = funExt re-ve }
      res : isEquiv ((X , x) ≡ (Y , y)) ((X , x) ≅ (Y , y)) (id-to-iso (X , x) (Y , y))
      res = Equiv≃.fromIso _ _ iso

    isCat : IsCategory raw
    isCat = record
      { isAssociative = isAssocitaive
      ; isIdentity    = isIdentity
      ; arrowsAreSets = arrowsAreSets
      ; univalent     = univalent
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
    re-ve : ∀ p → f (g p) ≡ p
    re-ve p = Product≡ e
      where
      module p = Product p
      -- RawProduct does not have eta-equality.
      e : Product.raw (f (g p)) ≡ Product.raw p
      RawProduct.object (e i) = p.object
      RawProduct.proj₁ (e i) = p.proj₁
      RawProduct.proj₂ (e i) = p.proj₂
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
