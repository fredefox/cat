{-# OPTIONS --cubical #-}
-- | Custom prelude for this module
module Cat.Prelude where

open import Agda.Primitive public

open import Cubical.Foundations.Prelude public
  renaming ( fromPathP to coe-lem
           ; isGroupoid to isGrpd
           ; isPropIsContr to propIsContr
           ; isProp→isSet to propSet
           ; J to pathJ
           ; JRefl to pathJprop
           ; substRefl to subst-neutral
           ; toPathP to coe-lem-inv
           ; transport to coe
           ; transportRefl to coe-neutral
           ; _∙_ to trans
           )
open import Cubical.Foundations.Equiv public
  renaming ( isPropIsEquiv to propIsEquiv
           )
open import Cubical.Foundations.Equiv.Fiberwise public
open import Cubical.Foundations.Function public
  renaming ( idfun to idFun
           )
open import Cubical.Foundations.HLevels public
  renaming ( isGroupoidΣ to grpdSig
           ; isGroupoidΠ to grpdPi
           ; isOfHLevel to HasLevel
           ; isOfHLevelRespectEquiv to equivPreservesNType
           ; isOfHLevelΠ to HasLevelPi
           ; isPropIsSet to isSetIsProp
           ; isPropΣ to propSig
           ; isPropΠ to propPi
           ; isSet→isGroupoid to setGrpd
           ; isSetΣ to setSig
           ; isSetΠ to setPi
           )
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport public
  renaming ( transport⁻-filler to transp-iso'
           )
open import Cubical.Foundations.Univalence public
  using    ( ua
           ; univalence
           )

open import Cubical.Data.Nat
  renaming ( ℕ to TLevel
           ; suc to S
           )
open import Cubical.Data.Sigma public
  renaming ( congΣEquiv to equivSig
           ; ΣPathP to Σ≡
           ; ΣProp≡ to lemSig
           ; Σ≡ to Σ≡-equiv
           )

open import Relation.Binary public
  using    ( IsEquivalence
           ; Preorder
           ; Rel
           ; Setoid
           ; Transitive
           )

-----------------
-- * Utilities --
-----------------

∃-syntax : ∀ {a b} {A : Type a} → (A → Type b) → Type (a ⊔ b)
∃-syntax = Σ _

syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- | Unique existentials.
∃! : ∀ {a b} {A : Type a}
  → (A → Type b) → Type (a ⊔ b)
∃! B = ∃[ x ] (B x × (∀ {y} → B y → x ≡ y))

∃!-syntax : ∀ {a b} {A : Type a} → (A → Type b) → Type (a ⊔ b)
∃!-syntax = ∃!

syntax ∃!-syntax (λ x → B) = ∃![ x ] B

module _ {ℓa ℓb} {A : Type ℓa} {P : A → Type ℓb} (f g : ∃! P) where
  ∃-unique : fst f ≡ fst g
  ∃-unique = (snd (snd f)) (fst (snd g))

equalityIsEquivalence : {ℓ : Level} {A : Type ℓ} → IsEquivalence {A = A} _≡_
IsEquivalence.refl  equalityIsEquivalence = refl
IsEquivalence.sym   equalityIsEquivalence = sym
IsEquivalence.trans equalityIsEquivalence = trans

IsPreorder
  : {a ℓ : Level} {A : Type a}
  → (_∼_ : Rel A ℓ) -- The relation.
  → Type _
IsPreorder _~_ = Relation.Binary.IsPreorder _≡_ _~_

-- | Prelude
infix  1 begin_
begin_ : {ℓ : Level} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
begin x≡y = x≡y

infixr 2 _≡⟨⟩_
_≡⟨⟩_ : {ℓ : Level} {A : Type ℓ} {y : A} → (x : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ y≡z = y≡z

-- | Function
_∘′_ : {a b c : Level} {A : Type a} {B : Type b} {C : Type c}
    → (B → C) → (A → B) → (A → C)
f ∘′ g = f ∘ g

_$_ : {a b : Level} {A : Type a} {B : A → Type b}
    → ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

flip : {a b c : Level} {A : Type a} {B : Type b} {C : A → B → Type c}
     → ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

swap : {a b : Level} {A : Type a} {B : Type b} → A × B → B × A
swap = swapΣEquiv _ _ .fst

-- | Isomorphism
-- FIXME rename `gradLemma` to `fromIsomorphism` - perhaps just use wrapper
-- module.
gradLemma : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  → ∀ (f : A → B) (inv : B → A) (rightInv : section f inv) (leftInv : retract f inv) → isEquiv f
gradLemma f inv rightInv leftInv = isoToIsEquiv (iso f inv rightInv leftInv)

-- | HLevels
module _ (ℓ : Level) where
  -- FIXME Ask if we can push upstream.
  -- A redefinition of `Cubical.Universe` with an explicit parameter
  _-type : TLevel → Type (lsuc ℓ)
  n -type = Σ (Type ℓ) (HasLevel n)

module _ {ℓa : Level} {A : Type ℓa} where
  module _ {ℓb : Level} {B : A → Type ℓb} where
    piImpl : (n : TLevel)
      → ({a : A} → HasLevel n (B a)) → HasLevel n ({a : A} → (B a))
    piImpl n g = equivPreservesNType {A = Expl} {B = Impl} n e (HasLevelPi n (λ a → g))
      where
      Impl = {a : A} → B a
      Expl = (a : A) → B a
      expl : Impl → Expl
      expl f a = f {a}
      impl : Expl → Impl
      impl f {a} = f a
      e : Expl ≃ Impl
      e = impl , gradLemma impl expl (λ f → refl) (λ f → refl)

    propPiImpl : ({a : A} → isProp (B a)) → isProp ({a : A} → (B a))
    propPiImpl = piImpl 1

    grpdPiImpl : ({a : A} → isGrpd (B a)) → isGrpd ({a : A} → (B a))
    grpdPiImpl = piImpl 3

    lemPropF : (h : ∀ (x : A) → isProp (B x)) → ∀ {x y : A} (b : B x) (b' : B y) (p : x ≡ y) → PathP (λ i → B (p i)) b b'
    lemPropF = isOfHLevel→isOfHLevelDep 1

  propGrpd : isProp A → isGrpd A
  propGrpd = isProp→isOfHLevelSuc 2

-- | Sigma
lemSigP : {ℓ ℓ' : Level} {A : Type ℓ} {B : (i : I) → A → Type ℓ'}
  → (h : ∀ i → (x : A) → isProp (B i x))
  → ∀ (u : Σ A (B i0)) (v : Σ A (B i1)) (p : fst u ≡ fst v) → PathP (λ i → Σ A (B i)) u v
lemSigP h u v p i = p i , isProp→PathP (λ i → h i (p i)) (snd u) (snd v) i

equivSigProp : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'}
  → (h : ∀ (x : A) → isProp (B x))
  → ∀ {u v : Σ A B} → (u ≡ v) ≃ (fst u ≡ fst v)
equivSigProp h = invEquiv (_ , ΣProp≡-equiv h)
