{-# OPTIONS --cubical #-}
module Cat where

open import Agda.Primitive
open import Prelude.Function
open import PathPrelude
open ≡-Reasoning

-- Questions:
--
-- Is there a canonical `postulate trustme : {l : Level} {A : Set l} -> A`
-- in Agda (like undefined in Haskell).
--
-- Does Agda have a way to specify local submodules?
--
-- Can I open parts of a record, like say:
--
--     open Functor {{...}} ( fmap )

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field
    -- morphisms
    fmap : ∀ {A B} → (A → B) → F A → F B
    -- laws
    identity : { A : Set a }
      -> id ≡ fmap (id { A = A })
    fusion : { A B C : Set a } ( f : B -> C ) ( g : A -> B )
      -> fmap f ∘ fmap g ≡ fmap (f ∘ g)

open Functor {{ ... }} hiding ( identity )

_<$>_ : {a b : Level} {F : Set a → Set b} {{r : Functor F}} {A B : Set a} → (A → B) → F A → F B
_<$>_ = fmap

record Identity (A : Set) : Set where
  constructor identity
  field
    runIdentity : A

open Identity {{...}}

instance
  IdentityFunctor : Functor Identity
  IdentityFunctor = record
    { fmap = λ { f (identity a) -> identity (f a) }
    ; identity = refl
    ; fusion = λ { f g -> refl }
    }

data Maybe ( A : Set ) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

instance
  MaybeFunctor : Functor Maybe
  Functor.fmap MaybeFunctor f nothing = nothing
  Functor.fmap MaybeFunctor f (just x) = just (f x)
  Functor.identity MaybeFunctor = fun-ext (λ { nothing → refl ; (just x) → refl })
  Functor.fusion MaybeFunctor f g = fun-ext (λ
    -- QUESTION: Why does inlining `lem₀` give rise to an error?
    { nothing → lem₀
    ; (just x) → {! refl!}
{-    ; (just x) → begin
      (fmap f ∘ fmap g) (just x)  ≡⟨⟩
      (fmap f (fmap g (just x)))  ≡⟨⟩
      (fmap f (just (g x)))       ≡⟨⟩
      (just (f (g x)))            ≡⟨⟩
      just ((f ∘ g) x)              ∎-}
    })
    where
      lem₀ : nothing ≡ nothing
      lem₀ = refl
      -- `lem₁` and `fusionjust` are the same.
      lem₁ : {A B C : Set} {f : B → C} {g : A → B} {x : A}
        → just (f (g x)) ≡ just (f (g x))
      lem₁ = refl
      fusionjust : { A B C : Set } { x : A } { f : B -> C } { g : A -> B }
        -> (fmap f ∘ fmap g) (just x) ≡ just ((f ∘ g) x)
      fusionjust {x = x} {f = f} {g = g} = begin
        (fmap f ∘ fmap g) (just x)  ≡⟨⟩
        (fmap f (fmap g (just x)))  ≡⟨⟩
        (fmap f (just (g x)))       ≡⟨⟩
        (just (f (g x)))            ≡⟨⟩
        just ((f ∘ g) x)              ∎


record Applicative {a} (F : Set a -> Set a) : Set (lsuc a) where
  field
    -- morphisms
    pure : { A : Set a } -> A -> F A
    ap   : { A B : Set a } -> F (A -> B) -> F A -> F B
    -- laws
    -- `ap-identity` is paraphrased from the documentation for Applicative on hackage.
    ap-identity : { A : Set a } -> ap (pure (id { A = A })) ≡ id
    composition : { A B C : Set a } ( u : F (B -> C) ) ( v : F (A -> B) ) ( w : F A )
      -> ap (ap (ap (pure _∘′_) u) v) w ≡ ap u (ap v w)
    homomorphism : { A B : Set a } { a : A } { f : A -> B }
      -> ap (pure f) (pure a) ≡ pure (f a)
    interchange : { A B : Set a } ( u : F (A -> B) ) ( a : A )
      -> ap u (pure a) ≡ ap (pure (_$ a)) u

open Applicative {{...}}
_<*>_ = ap

instance
  IdentityApplicative : Applicative Identity
  Applicative.pure IdentityApplicative = identity
  Applicative.ap IdentityApplicative (identity f) (identity a) = identity (f a)
  Applicative.ap-identity IdentityApplicative = refl
  Applicative.composition IdentityApplicative _ _ _ = refl
  Applicative.homomorphism IdentityApplicative = refl
  Applicative.interchange IdentityApplicative _ _ = refl

-- QUESTION: Is this provable? How?
-- I suppose this would be `≡`'s functor-instance.
equiv-app : {A B : Set} -> {f g : A -> B} -> {a : A} -> f ≡ g -> f a ≡ g a
equiv-app f≡g = {!!}

instance
  MaybeApplicative : Applicative Maybe
  Applicative.pure MaybeApplicative = just
  Applicative.ap MaybeApplicative nothing _ = nothing
  Applicative.ap MaybeApplicative (just f) x = fmap f x
  -- QUESTION: Why does termination-check fail when I use `refl` in both cases below?
  Applicative.ap-identity MaybeApplicative = fun-ext (λ
    { nothing → {!refl!}
    ; (just x) → {!refl!}
    })
  Applicative.composition MaybeApplicative nothing v w = refl
  Applicative.composition MaybeApplicative (just x) nothing w = refl
  -- Easy-mode:
  --  Applicative.composition MaybeApplicative {u = just f} {just g} {nothing} = refl
  --  Applicative.composition MaybeApplicative {u = just f} {just g} {just x} = refl
  -- Re-use mode:
  -- QUESTION: What's wrong here?
  Applicative.composition MaybeApplicative (just f) (just g) w = sym (equiv-app lem)
    where
    lem : ∀ {A B C} {f : B → C} {g : A → B} {w : Maybe A} →
      (fmap f) ∘ (fmap g) ≡
      (Functor.fmap MaybeFunctor (f ∘ g))
    lem = Functor.fusion MaybeFunctor _ _
{-
  Applicative.composition MaybeApplicative { u = u } { v = v } { w = w } = begin
    ap (ap (ap (pure _∘′_) u) v) w ≡⟨⟩
    ap (ap (fmap _∘′_      u) v) w ≡⟨ {!!} ⟩
    {!!} ∎
-}
  Applicative.homomorphism MaybeApplicative = refl
  Applicative.interchange MaybeApplicative nothing a = refl
  Applicative.interchange MaybeApplicative (just x) a = refl
