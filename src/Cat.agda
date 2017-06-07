{-# OPTIONS --cubical #-}
module Cat where

open import Agda.Primitive
open import Prelude.Function
import Prelude.Equality
open import PathPrelude

-- Questions:
--
-- Is there a canonical `postulate trustme : {l : Level} {A : Set l} -> A`
-- in Agda (like undefined in Haskell).
--
-- Does Agda have a way to specify local submodules?
record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field
    -- morphisms
    fmap : ∀ {A B} → (A → B) → F A → F B
    -- laws
    identity : { A : Set a } -> id ≡ fmap (id { A = A })
    -- Why does PathPrelude.≡ not agree with Prelude.Equality.≡
    fusion : { A B C : Set a } ( f : B -> C ) ( g : A -> B ) -> fmap f ∘ fmap g ≡ fmap (f ∘ g)
--    fusion : { A B C : Set a } ( f : B -> C ) ( g : A -> B ) -> fmap f ∘ fmap g Prelude.Equality.≡ fmap (f ∘ g)

-- PathPrelude._≡_      : {a : Level} {A : Set a} → A → A → Set a
-- Prelude.Equality._≡_ : {a : Level} {A : Set a} → A → A → Set a
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

-- postulate
--   fun-ext : ∀ {a b} {A : Set a} {B : A → Set b} → {f g : (x : A) → B x}
--     → (∀ x → (f x) ≡ (g x)) → f ≡ g
-- fun-ext p = λ i → \ x → p x i

instance
  MaybeFunctor : Functor Maybe
  Functor.fmap MaybeFunctor f nothing = nothing
  Functor.fmap MaybeFunctor f (just x) = just (f x)
  -- how the heck can I use `fun-ext` which produces `Path id (fmap id)` wheras the type of the whole is `id ≡ fmap id`.
  Functor.identity MaybeFunctor = (fun-ext (λ { nothing → refl ; (just x) → refl }))
  -- Why can I not use `fun-ext` here?
  Functor.fusion MaybeFunctor f g = {!!} -- fun-ext (λ { nothing -> refl ; (just x) -> refl })

record Applicative {a} (F : Set a -> Set a) : Set (lsuc a) where
  field
    -- morphisms
    pure : { A : Set a } -> A -> F A
    ap   : { A B : Set a } -> F (A -> B) -> F A -> F B
    -- laws
    -- `ap-identity` is paraphrased from the documentation for Applicative on hackage.
    ap-identity : { A : Set a } -> ap (pure (id { A = A })) ≡ id
    composition : { A B C : Set a } { u : F (B -> C) } { v : F (A -> B) } { w : F A }
      -> ap (ap (ap (pure _∘′_) u) v) w ≡ ap u (ap v w)
    homomorphism : { A B : Set a } { a : A } { f : A -> B }
      -> ap (pure f) (pure a) ≡ pure (f a)
    interchange : { A B : Set a } { u : F (A -> B) } { a : A }
      -> ap u (pure a) ≡ ap (pure (_$ a)) u

instance
  IdentityApplicative : Applicative Identity
  Applicative.pure IdentityApplicative = identity
  Applicative.ap IdentityApplicative (identity f) (identity a) = identity (f a)
  Applicative.ap-identity IdentityApplicative = refl
  Applicative.composition IdentityApplicative = refl
  Applicative.homomorphism IdentityApplicative = refl
  Applicative.interchange IdentityApplicative = refl
