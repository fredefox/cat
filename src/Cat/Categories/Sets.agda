-- | The category of homotopy sets
{-# OPTIONS --allow-unsolved-metas --cubical #-}
module Cat.Categories.Sets where

open import Agda.Primitive
open import Data.Product
open import Function using (_∘_)

-- open import Cubical using (funExt ; refl ; isSet ; isProp ; _≡_ ; isEquiv ; sym ; trans ; _[_≡_] ; I ; Path ; PathP)
open import Cubical hiding (_≃_)
open import Cubical.Univalence using (univalence ; con ; _≃_ ; idtoeqv)
open import Cubical.GradLemma

open import Cat.Category
open import Cat.Category.Functor
open import Cat.Category.Product
open import Cat.Wishlist
open import Cat.Equivalence as Eqv renaming (module NoEta to Eeq) using (AreInverses)

module Equivalence = Eeq.Equivalence′
postulate
  _⊙_ : {ℓa ℓb ℓc : Level} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} → (A ≃ B) → (B ≃ C) → A ≃ C
  sym≃ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → A ≃ B → B ≃ A
infixl 10 _⊙_

module _ (ℓ : Level) where
  private
    open import Cubical.NType.Properties
    open import Cubical.Universe

    SetsRaw : RawCategory (lsuc ℓ) ℓ
    RawCategory.Object SetsRaw = hSet {ℓ}
    RawCategory.Arrow  SetsRaw (T , _) (U , _) = T → U
    RawCategory.𝟙      SetsRaw = Function.id
    RawCategory._∘_    SetsRaw = Function._∘′_

    open RawCategory SetsRaw hiding (_∘_)
    open Univalence  SetsRaw

    isIdentity : IsIdentity Function.id
    proj₁ isIdentity = funExt λ _ → refl
    proj₂ isIdentity = funExt λ _ → refl

    arrowsAreSets : ArrowsAreSets
    arrowsAreSets {B = (_ , s)} = setPi λ _ → s

    isIso = Eqv.Isomorphism
    module _ {hA hB : hSet {ℓ}} where
      open Σ hA renaming (proj₁ to A ; proj₂ to sA)
      open Σ hB renaming (proj₁ to B ; proj₂ to sB)
      lem1 : (f : A → B) → isSet A → isSet B → isProp (isIso f)
      lem1 f sA sB = res
        where
        module _ (x y : isIso f) where
          module x = Σ x renaming (proj₁ to inverse ; proj₂ to areInverses)
          module y = Σ y renaming (proj₁ to inverse ; proj₂ to areInverses)
          module xA = AreInverses x.areInverses
          module yA = AreInverses y.areInverses
          -- I had a lot of difficulty using the corresponding proof where
          -- AreInverses is defined. This is sadly a bit anti-modular. The
          -- reason for my troubles is probably related to the type of objects
          -- being hSet's rather than sets.
          p : ∀ {f} g → isProp (AreInverses {A = A} {B} f g)
          p {f} g xx yy i = record
            { verso-recto = ve-re
            ; recto-verso = re-ve
            }
            where
            module xxA = AreInverses xx
            module yyA = AreInverses yy
            ve-re : g ∘ f ≡ Function.id
            ve-re = arrowsAreSets {A = hA} {B = hA} _ _ xxA.verso-recto yyA.verso-recto i
            re-ve : f ∘ g ≡ Function.id
            re-ve = arrowsAreSets {A = hB} {B = hB} _ _ xxA.recto-verso yyA.recto-verso i
          1eq : x.inverse ≡ y.inverse
          1eq = begin
            x.inverse                   ≡⟨⟩
            x.inverse ∘ Function.id     ≡⟨ cong (λ φ → x.inverse ∘ φ) (sym yA.recto-verso) ⟩
            x.inverse ∘ (f ∘ y.inverse) ≡⟨⟩
            (x.inverse ∘ f) ∘ y.inverse ≡⟨ cong (λ φ → φ ∘ y.inverse) xA.verso-recto ⟩
            Function.id ∘ y.inverse     ≡⟨⟩
            y.inverse                   ∎
          2eq : (λ i → AreInverses f (1eq i)) [ x.areInverses ≡ y.areInverses ]
          2eq = lemPropF p 1eq
          res : x ≡ y
          res i = 1eq i , 2eq i
    module _ {ℓa ℓb : Level} {A : Set ℓa} {P : A → Set ℓb} where
      postulate
        lem2 : ((x : A) → isProp (P x)) → (p q : Σ A P)
          → (p ≡ q) ≃ (proj₁ p ≡ proj₁ q)
        lem3 : {Q : A → Set ℓb} → ((x : A) → P x ≃ Q x)
          → Σ A P ≃ Σ A Q

    module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
      postulate
        lem4 : isSet A → isSet B → (f : A → B)
          → isEquiv A B f ≃ isIso f

    module _ {hA hB : Object} where
      private
        A = proj₁ hA
        sA = proj₂ hA
        B = proj₁ hB
        sB = proj₂ hB

      postulate
        -- lem3 and the equivalence from lem4
        step0 : Σ (A → B) isIso ≃ Σ (A → B) (isEquiv A B)
        -- univalence
        step1 : Σ (A → B) (isEquiv A B) ≃ (A ≡ B)
        -- lem2 with propIsSet
        step2 : (A ≡ B) ≃ (hA ≡ hB)
      -- Go from an isomorphism on sets to an isomorphism on homotopic sets
      trivial? : (hA ≅ hB) ≃ Σ (A → B) isIso
      trivial? = sym≃ (Eeq.fromIsomorphism res)
        where
        fwd : Σ (A → B) isIso → hA ≅ hB
        fwd (f , g , inv) = f , g , inv.toPair
          where
          module inv = AreInverses inv
        bwd : hA ≅ hB → Σ (A → B) isIso
        bwd (f , g , x , y) = f , g , record { verso-recto = x ; recto-verso = y }
        res : Σ (A → B) isIso Eqv.≅ (hA ≅ hB)
        res = fwd , bwd , record { verso-recto = refl ; recto-verso = refl }
      conclusion : (hA ≅ hB) ≃ (hA ≡ hB)
      conclusion = trivial? ⊙ step0 ⊙ step1 ⊙ step2
      t : (hA ≡ hB) ≃ (hA ≅ hB)
      t = sym≃ conclusion
      -- TODO Is the morphism `(_≃_.eqv conclusion)` the same as
      -- `(id-to-iso (λ {A} {B} → isIdentity {A} {B}) hA hB)` ?
      res : isEquiv (hA ≡ hB) (hA ≅ hB) (_≃_.eqv t)
      res = _≃_.isEqv t
    module _ {hA hB : hSet {ℓ}} where
      univalent : isEquiv (hA ≡ hB) (hA ≅ hB) (id-to-iso (λ {A} {B} → isIdentity {A} {B}) hA hB)
      univalent = let k = _≃_.isEqv (sym≃ conclusion) in {!!}

    SetsIsCategory : IsCategory SetsRaw
    IsCategory.isAssociative SetsIsCategory = refl
    IsCategory.isIdentity    SetsIsCategory {A} {B} = isIdentity    {A} {B}
    IsCategory.arrowsAreSets SetsIsCategory {A} {B} = arrowsAreSets {A} {B}
    IsCategory.univalent     SetsIsCategory = univalent

  𝓢𝓮𝓽 Sets : Category (lsuc ℓ) ℓ
  Category.raw 𝓢𝓮𝓽 = SetsRaw
  Category.isCategory 𝓢𝓮𝓽 = SetsIsCategory
  Sets = 𝓢𝓮𝓽

module _ {ℓ : Level} where
  private
    𝓢 = 𝓢𝓮𝓽 ℓ
    open Category 𝓢
    open import Cubical.Sigma

    module _ (0A 0B : Object) where
      private
        A : Set ℓ
        A = proj₁ 0A
        sA : isSet A
        sA = proj₂ 0A
        B : Set ℓ
        B = proj₁ 0B
        sB : isSet B
        sB = proj₂ 0B
        0A×0B : Object
        0A×0B = (A × B) , sigPresSet sA λ _ → sB

        module _ {X A B : Set ℓ} (f : X → A) (g : X → B) where
          _&&&_ : (X → A × B)
          _&&&_ x = f x , g x
        module _ {0X : Object} where
          X = proj₁ 0X
          module _ (f : X → A ) (g : X → B) where
            lem : proj₁ Function.∘′ (f &&& g) ≡ f × proj₂ Function.∘′ (f &&& g) ≡ g
            proj₁ lem = refl
            proj₂ lem = refl

        rawProduct : RawProduct 𝓢 0A 0B
        RawProduct.object rawProduct = 0A×0B
        RawProduct.proj₁  rawProduct = Data.Product.proj₁
        RawProduct.proj₂  rawProduct = Data.Product.proj₂

        isProduct : IsProduct 𝓢 _ _ rawProduct
        IsProduct.ump isProduct {X = X} f g
          = (f &&& g) , lem {0X = X} f g

      product : Product 𝓢 0A 0B
      Product.raw       product = rawProduct
      Product.isProduct product = isProduct

  instance
    SetsHasProducts : HasProducts 𝓢
    SetsHasProducts = record { product = product }

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) where
  -- Covariant Presheaf
  Representable : Set (ℓa ⊔ lsuc ℓb)
  Representable = Functor ℂ (𝓢𝓮𝓽 ℓb)

  -- Contravariant Presheaf
  Presheaf : Set (ℓa ⊔ lsuc ℓb)
  Presheaf = Functor (opposite ℂ) (𝓢𝓮𝓽 ℓb)

  open Category ℂ

  -- The "co-yoneda" embedding.
  representable : Category.Object ℂ → Representable
  representable A = record
    { raw = record
      { omap = λ B → ℂ [ A , B ] , arrowsAreSets
      ; fmap = ℂ [_∘_]
      }
    ; isFunctor = record
      { isIdentity = funExt λ _ → proj₂ isIdentity
      ; isDistributive = funExt λ x → sym isAssociative
      }
    }

  -- Alternate name: `yoneda`
  presheaf : Category.Object (opposite ℂ) → Presheaf
  presheaf B = record
    { raw = record
      { omap = λ A → ℂ [ A , B ] , arrowsAreSets
      ; fmap = λ f g → ℂ [ g ∘ f ]
    }
    ; isFunctor = record
      { isIdentity = funExt λ x → proj₁ isIdentity
      ; isDistributive = funExt λ x → isAssociative
      }
    }
