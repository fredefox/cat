{-# OPTIONS --cubical #-}
module PathPrelude where

  open import Primitives public
  open import Level
  open import Data.Product using (Σ; _,_) renaming (proj₁ to fst; proj₂ to snd)

  refl : ∀ {a} {A : Set a} {x : A} → Path x x
  refl {x = x} = λ i → x

  sym : ∀ {a} {A : Set a} → {x y : A} → Path x y → Path y x
  sym p = \ i → p (~ i)

  pathJ : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Path x y → Set p) → P x ((\ i -> x)) → ∀ y (p : Path x y) → P y p
  pathJ P d _ p = primComp (λ i → P (p i) (\ j → p (i ∧ j))) i0 (\ _ → empty) d


  pathJprop : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Path x y → Set p) → (d : P x ((\ i -> x))) → pathJ P d _ refl ≡ d
  pathJprop {x = x} P d i = primComp (λ _ → P x refl) i (\ { j (i = i1) → d }) d


  trans : ∀ {a} {A : Set a} → {x y z : A} → Path x y → Path y z → Path x z
  trans {A = A} {x} {y} p q = \ i → primComp (λ j → A) (i ∨ ~ i)
                                             (\ j → \ { (i = i1) → q j
                                                      ; (i = i0) → x
                                                      }
                                             )
                                             (p i)

  fun-ext : ∀ {a b} {A : Set a} {B : A → Set b} → {f g : (x : A) → B x}
            → (∀ x → Path (f x) (g x)) → Path f g
  fun-ext p = λ i x → p x i


  -- comp using only Path
  compP : ∀ {a : Level} {A0 A1 : Set a} (A : Path A0 A1) → {φ : I} → (a0 : A i0) → (Partial (Σ A1 \ y → PathP (\ i → A i) a0 y) φ) → A i1
  compP A {φ} a0 p = primComp (λ i → A i) φ (\ i o → p o .snd i) a0

  -- fill using only Path

  fillP : ∀ {a : Level} {A0 A1 : Set a} (A : Path A0 A1) → {φ : I} → (a0 : A i0) → (Partial (Σ A1 \ y → PathP (\ i → A i) a0 y) φ) → ∀ i → A i
  fillP A {φ} a0 p j = primComp (λ i → A (i ∧ j)) (φ ∨ ~ j) (\ { i (φ = i1) → p itIsOne .snd (i ∧ j); i (j = i0) → a0 }) a0


  reflId : ∀ {a} {A : Set a}{x : A} → Id x x
  reflId {x = x} = conid i1 (λ _ → x)

  Jdef : ∀ {a}{p}{A : Set a}{x : A}(P : ∀ y → Id x y → Set p) → (d : P x reflId) → J P d reflId ≡ d
  Jdef P d = refl

  fromPath : ∀ {A : Set}{x y : A} → Path x y -> Id x y
  fromPath p = conid i0 (\ i → p i)

  transId : ∀ {a} {A : Set a} → {x y z : A} → Id x y → Id y z → Id x z
  transId {A = A} {x} {y} p = J (λ y _ → Id x y) p

  congId :  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → ∀ {x y} → Id x y → Id (f x) (f y)
  congId f {x} {y} = J (λ y _ → Id (f x) (f y)) reflId

















  fill : ∀ {a : I -> Level} (A : (i : I) → Set (a i)) (φ : I) → ((i : I) → Partial (A i) φ) → A i0 → (i : I) → A i
  fill A φ u a0 i = unsafeComp (\ j → A (i ∧ j)) (φ ∨ ~ i) (\ j → unsafePOr φ (~ i) (u (i ∧ j)) \ { _ → a0 }) a0

  singl : ∀ {l} {A : Set l} (a : A) -> Set l
  singl {A = A} a = Σ A (\ x → a ≡ x)

  contrSingl : ∀ {l} {A : Set l} {a b : A} (p : a ≡ b) → Path {A = singl a} (a , refl) (b , p)
  contrSingl p = \ i → ((p i) , \ j →  p (i ∧ j))


  module Contr where

    isContr : ∀ {a} → (A : Set a) → Set a
    isContr A = Σ A (\ x → ∀ y → x ≡ y)

    contr : ∀ {a} {A : Set a} → isContr A → (φ : I) → (u : Partial A φ) → A
    contr {A = A} (c , p) φ u = primComp (\ _ → A) φ (λ i → \ o → p (u o) i) c

    lemma : ∀ {a} {A : Set a}
            → (contr1 : ∀ φ → Partial A φ → A)
            → (contr2 : ∀ u → u ≡ (contr1 i1 \{_ → u}))
            → isContr A
    lemma {A = A} contr1 contr2 = x , (λ y → let module M = R y in trans (contr2 x) (trans (\ i → M.v i) (sym (contr2 y)))) where
          x = contr1 i0 empty
          module R (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial A φ
            u = primPOr (~ i) i (\{_ → x}) (\{_ → y})
            v = contr1 φ u

    isContrProp : ∀ {a} {A : Set a} (h : isContr A) -> ∀ (x y : A) → x ≡ y
    isContrProp {A = A} h a b = \ i → primComp (\ _ → A) _ (\ j → [ (~ i) ↦ (\{_ → snd h a j}) , i ↦ (\{_ → snd h b j}) ]) (fst h)

  module Pres {la lb : I → _} {T : (i : I) → Set (lb i)}{A : (i : I) → Set (la i)} (f : ∀ i → T i → A i) (φ : I) (t : ∀ i → Partial (T i) φ)
                  (t0 : T i0 {- [ φ ↦ t i0 ] -}) where

   c1 c2 : A i1
   c1 = unsafeComp A φ (λ i → (\{_ → f i (t i itIsOne) })) (f i0 t0)
   c2 = f i1 (unsafeComp T φ t t0)

   a0 = f i0 t0

   a : ∀ i → Partial (A i) φ
   a i = (\{_ → f i ((t i) itIsOne) })

   u : ∀ i → A i
   u = fill A φ a a0

   v : ∀ i → T i
   v = fill T φ t t0

   pres : Path c1 c2
   pres = \ j → unsafeComp A (φ ∨ (j ∨ ~ j)) (λ i → primPOr φ ((j ∨ ~ j)) (a i) (primPOr j (~ j)  (\{_ →  f i (v i)  }) (\{_ →  u i  }))) a0

  module Equiv {l l'} (A : Set l)(B : Set l') where
    isEquiv : (A -> B) → Set (l' ⊔ l)
    isEquiv f = ∀ y → Contr.isContr (Σ A \ x → y ≡ f x)

    Equiv = Σ _ isEquiv

    equiv : (f : Equiv) → ∀ φ (t : Partial A φ) (a : B {- [ φ ↦ f t ] -}) → PartialP φ (\ o → Path a (fst f (t o)))
             -> Σ A \ x → a ≡ fst f x -- [ φ ↦ (t , \ j → a) ]
    equiv (f , [f]) φ t a p = Contr.contr ([f] a) φ \ o → t o , (\ i → p o i)

    equiv1 : (f : Equiv) → ∀ φ (t : Partial A φ) (a : B {- [ φ ↦ f t ] -}) → PartialP φ (\ o → Path a (fst f (t o))) -> A
    equiv1 f φ t a p = fst (equiv f φ t a p)

    equiv2 : (f : Equiv) → ∀ φ (t : Partial A φ) (a : B {- [ φ ↦ f t ] -}) → (p : PartialP φ (\ o → Path a (fst f (t o))))
             → a ≡ fst f (equiv1 f φ t a p)
    equiv2 f φ t a p = snd (equiv f φ t a p)

  open Equiv public

  {-# BUILTIN ISEQUIV isEquiv #-}

  idEquiv : ∀ {a} {A : Set a} → Equiv A A
  idEquiv = (λ x → x) , (λ y → (y , refl) , (λ y₁ → contrSingl (snd y₁)))


  pathToEquiv : ∀ {l : I → _} (E : (i : I) → Set (l i)) → Equiv (E i0) (E i1)
  pathToEquiv E = f
                , (λ y → (g y
                         , (\ j → primComp E (~ j ∨ j) (\ i → [ ~ j ↦  (\{_ → v i y })  , j ↦  (\{_ → u i (g y) })  ]) (g y))) ,
                                          prop-f-image y _ )
    where
      A = E i0
      B = E i1
      transp : ∀ {l : I → _} (E : (i : I) → Set (l i)) → E i0 → E i1
      transp E x = primComp E i0 (\ _ → empty) x
      f : A → B
      f = transp E
      g : B → A
      g = transp (\ i → E (~ i))
      u : (i : I) → A → E i
      u i x = fill E i0 (\ _ → empty) x i
      v : (i : I) → B → E i
      v i y = fill (\ i → E (~ i)) i0 (\ _ → empty) y (~ i)
      prop-f-image : (y : B) → (a b : Σ _ \ x → y ≡ f x) → a ≡ b
      prop-f-image y (x0 , b0) (x1 , b1) = \ k → (w k) , (\ j → d j k)
         where
           w0 = \ (j : I) → primComp (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  (\{_ → v (~ i) y })  , j ↦  (\{_ → u (~ i) x0 })  ])) (b0 j)
           w1 = \ (j : I) → primComp (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  (\{_ → v (~ i) y })  , j ↦  (\{_ → u (~ i) x1 })  ])) (b1 j)
           t0 = \ (j : I) → fill (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  (\{_ → v (~ i) y })  , j ↦  (\{_ → u (~ i) x0 })  ])) (b0 j)
           t1 = \ (j : I) → fill (\ i → E (~ i)) (~ j ∨ j) ((\ i → [ ~ j ↦  (\{_ → v (~ i) y })  , j ↦  (\{_ → u (~ i) x1 })  ])) (b1 j)
           w = \ (k : I) → primComp (λ _ → A) (~ k ∨ k) (\ j → [ ~ k ↦ (\{_ → w0 j }) , k ↦ (\{_ → w1 j }) ]) (g y)
           t = \ (j k : I) → fill (λ _ → A) (~ k ∨ k) (\ j → [ ~ k ↦ (\{_ → w0 j }) , k ↦ (\{_ → w1 j }) ]) (g y) j
           d = \ (j k : I) → primComp E ((~ k ∨ k) ∨ (~ j ∨ j)) ((\ i → [ ~ k ∨ k ↦ [ ~ k ↦  (\{_ →  t0 j (~ i)  })  , k ↦  (\{_ → t1 j (~ i) })  ]
                                                     , ~ j ∨ j ↦ [ ~ j ↦  (\{_ → v (i) y })  , j ↦  (\{_ → u (i) (w k) })  ] ])) (t j k)

  pathToEquiv2 : ∀ {l : I → _} (E : (i : I) → Set (l i)) → _
  pathToEquiv2 {l} E = snd (pathToEquiv E)

  {-# BUILTIN PATHTOEQUIV pathToEquiv2 #-}

  module GluePrims where
   primitive
    primGlue : ∀ {a b} (A : Set a) → ∀ φ → (T : Partial (Set b) φ) → (f : PartialP φ (λ o → T o → A))
                                           → (pf : PartialP φ (λ o → isEquiv (T o) A (f o))) → Set b
    prim^glue : ∀ {a b} {A : Set a} {φ : I} {T : Partial (Set b) φ}
                  {f : PartialP φ (λ o → T o → A)}
                  {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                  PartialP φ T → A → primGlue A φ T f pf
    prim^unglue : ∀ {a b} {A : Set a} {φ : I} {T : Partial (Set b) φ}
                    {f : PartialP φ (λ o → T o → A)}
                    {pf : PartialP φ (λ o → isEquiv (T o) A (f o))} →
                    primGlue A φ T f pf → A


  module GluePrims' (dummy : Set₁) = GluePrims
  open GluePrims' Set using () renaming (prim^glue to unsafeGlue) public

  open GluePrims public renaming (prim^glue to glue; prim^unglue to unglue)

  Glue : ∀ {a b} (A : Set a) → ∀ φ → (T : Partial (Set b) φ) (f : (PartialP φ \ o → Equiv (T o) A))  → Set _
  Glue A φ T f = primGlue A φ T (\ o → fst (f o)) (\ o → snd (f o))

  eqToPath' : ∀ {l} {A B : Set l} → Equiv A B → Path A B
  eqToPath' {l} {A} {B} f = \ i → Glue B (~ i ∨ i) ([ ~ i ↦ (\ _ → A) , i ↦ (\ _ → B) ]) ([ ~ i ↦ (\{_ → f }) , i ↦ (\{_ → idEquiv }) ])

  primitive
    primFaceForall : (I → I) → I

  module FR (φ : I -> I) where
     δ = primFaceForall φ
     postulate
         ∀e : IsOne δ → ∀ i → IsOne (φ i)
         ∀∨ : ∀ i → IsOne (φ i) → IsOne ((δ ∨ (φ i0 ∧ ~ i)) ∨ (φ i1 ∧ i))

  module GlueIso {a b} {A : Set a} {φ : I} {T : Partial (Set b) φ} {f : (PartialP φ \ o → Equiv (T o) A)} where
    going : PartialP φ (\ o → Glue A φ T f → T o)
    going = (\{_ → (\ x → x) })
    back : PartialP φ (\ o → T o → Glue A φ T f)
    back = (\{_ → (\ x → x) })

    lemma : ∀ (b : PartialP φ (\ _ → Glue A φ T f)) → PartialP φ \ o → Path (unglue {φ = φ} (b o)) (fst (f o) (going o (b o)))
    lemma b = (\{_ → refl })

  module CompGlue {la lb : I → _} (A : (i : I) → Set (la i)) (φ : I -> I) (T : ∀ i → Partial (Set (lb i)) (φ i))
                           (f : ∀ i → PartialP (φ i) \ o → Equiv (T i o) (A i)) where
     B : (i : I) -> Set (lb i)
     B = \ i → Glue (A i) (φ i) (T i) (f i)
     module Local (ψ : I) (b : ∀ i → Partial (B i) ψ) (b0 : B i0 {- [ ψ ↦ b i0 ] -}) where
       a : ∀ i → Partial (A i) ψ
       a i = \ o → unglue {φ = φ i} (b i o)
       module Forall (δ : I) (∀e : IsOne δ → ∀ i → IsOne (φ i)) where
         a0 : A i0
         a0 = unglue {φ = φ i0} b0
         a₁' = unsafeComp A ψ a a0
         t₁' : PartialP δ (\ o → T i1 (∀e o i1))
         t₁' = \ o → unsafeComp (λ i → T i (∀e o i)) ψ (\ i o' → GlueIso.going {φ = φ i} (∀e o i) (b i o')) (GlueIso.going {φ = φ i0} (∀e o i0) b0)
         w : PartialP δ _
         w = \ o → Pres.pres (\ i → fst (f i (∀e o i))) ψ (λ i x → GlueIso.going {φ = φ i} (∀e o i) (b i x)) (GlueIso.going {φ = φ i0} (∀e o i0) b0)
         a₁'' = unsafeComp (\ _ → A i1) (δ ∨ ψ) (\ j → unsafePOr δ ψ (\ o → w o j) (a i1)) a₁'
         g : PartialP (φ i1) _
         g o = (equiv (T i1 _) (A i1) (f i1 o) (δ ∨ ψ) (unsafePOr δ ψ t₁' (\ o' → GlueIso.going {φ = φ i1} o (b i1 o'))) a₁''
                          ( (unsafePOr δ ψ (\{ (δ = i1) → refl })  ((\{ (ψ = i1) → GlueIso.lemma {φ = φ i1} (\ _ → b i1 itIsOne) o })  ) ) ))
                          -- TODO figure out why we need (δ = i1) and (ψ = i1) here
         t₁ : PartialP (φ i1) _
         t₁ o = fst (g o)
         α : PartialP (φ i1) _
         α o = snd (g o)
         a₁ = unsafeComp (\ j → A i1) (φ i1 ∨ ψ) (\ j → unsafePOr (φ i1) ψ (\ o → α o j) (a i1)) a₁''
         b₁ : Glue _ (φ i1) (T i1) (f i1)
         b₁ = unsafeGlue {φ = φ i1} t₁ a₁
       b1 = Forall.b₁ (FR.δ φ) (FR.∀e φ)

  compGlue : {la lb : I → _} (A : (i : I) → Set (la i)) (φ : I -> I) (T : ∀ i → Partial (Set (lb i)) (φ i))
                           (f : ∀ i → PartialP (φ i) \ o → (T i o) → (A i)) →
                           (pf : ∀ i → PartialP (φ i) (λ o → isEquiv (T i o) (A i) (f i o))) →
             let
                B : (i : I) -> Set (lb i)
                B = \ i → primGlue (A i) (φ i) (T i) (f i) (pf i)
             in  (ψ : I) (b : ∀ i → Partial (B i) ψ) (b0 : B i0) → B i1
  compGlue A φ T f pf ψ b b0 = CompGlue.Local.b1 A φ T (λ i p → (f i p) , (pf i p)) ψ b b0


  {-# BUILTIN COMPGLUE compGlue #-}

  module ≡-Reasoning {a} {A : Set a} where

    infix  3 _∎
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_ -- _≅⟨_⟩_
    infix  1 begin_

    begin_ : ∀{x y : A} → x ≡ y → x ≡ y
    begin_ x≡y = x≡y

    _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
    _ ≡⟨⟩ x≡y = x≡y

    _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
    _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

    -- _≅⟨_⟩_ : ∀ (x {y z} : A) → x ≅ y → y ≡ z → x ≡ z
    -- _ ≅⟨ x≅y ⟩ y≡z = trans (H.≅-to-≡ x≅y) y≡z

    _∎ : ∀ (x : A) → x ≡ x
    _∎ _ = refl
