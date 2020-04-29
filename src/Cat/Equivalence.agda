{-# OPTIONS --cubical #-}
module Cat.Equivalence where

open import Cat.Prelude

module _ {ℓa ℓb : Level} where
  private
    ℓ = ℓa ⊔ ℓb

  module _ {A : Set ℓa} {B : Set ℓb} where
    -- Quasi-inverse in [HoTT] §2.4.6
    -- FIXME Maybe rename?
    AreInverses : (f : A → B) (g : B → A) → Set ℓ
    AreInverses f g = (g ∘ f ≡ idFun A) × (f ∘ g ≡ idFun B)

    module AreInverses {f : A → B} {g : B → A}
      (inv : AreInverses f g) where
      open Σ inv renaming (fst to verso-recto ; snd to recto-verso) public
      obverse = f
      reverse = g
      inverse = reverse

    Isomorphism : (f : A → B) → Set _
    Isomorphism f = Σ (B → A) λ g → AreInverses f g

  _≅_ : Set ℓa → Set ℓb → Set _
  A ≅ B = Σ (A → B) Isomorphism

symIso : ∀ {ℓa ℓb} {A : Set ℓa}{B : Set ℓb} → A ≅ B → B ≅ A
symIso (f , g , p , q)= g , f , q , p

module _ {ℓa ℓb ℓc} {A : Set ℓa} {B : Set ℓb} (sB : isSet B) {Q : B → Set ℓc} (f : A → B)  where

  Σ-fst-map : Σ A (\ a → Q (f a)) → Σ B Q
  Σ-fst-map (x , q) = f x , q

  isoSigFst : Isomorphism f → Σ A (Q ∘ f) ≅ Σ B Q
  isoSigFst (g , g-f , f-g) = Σ-fst-map
    , (\ { (b , q) → g b , coe (\ i → Q (f-g (~ i) b)) q })
    , funExt (\ { (a , q) → Σ≡ ((\ i → g-f i a)
        , let r = symP (transp-iso' ((λ i → Q (f-g (i) (f a)))) q) in
          coe (\ i → PathP (\ j → Q (sB _ _ (λ j₁ → f-g j₁ (f a)) (λ j₁ → f (g-f j₁ a)) i j)) (coe (λ i₁ → Q (f-g (~ i₁) (f a))) q) q) r )})
    , funExt (\ { (b , q) → Σ≡ ((\ i → f-g i b) , symP (transp-iso' (λ i → Q (f-g i b)) q))})


module _ {ℓ : Level} {A B : Set ℓ} {f : A → B}
  (g : B → A) (s : {A B : Set ℓ} → isSet (A → B)) where

  propAreInverses : isProp (AreInverses {A = A} {B} f g)
  propAreInverses x y i = ve-re , re-ve
    where
    ve-re : g ∘ f ≡ idFun A
    ve-re = s (g ∘ f) (idFun A) (fst x) (fst y) i
    re-ve : f ∘ g ≡ idFun B
    re-ve = s (f ∘ g) (idFun B) (snd x) (snd y) i

module _ {ℓ : Level} {A B : Set ℓ} (f : A → B)
  (sA : isSet A) (sB : isSet B) where

  propIsIso : isProp (Isomorphism f)
  propIsIso = res
        where
        module _ (x y : Isomorphism f) where
          module x = Σ x renaming (fst to inverse ; snd to areInverses)
          module y = Σ y renaming (fst to inverse ; snd to areInverses)
          module xA = AreInverses {f = f} {x.inverse} x.areInverses
          module yA = AreInverses {f = f} {y.inverse} y.areInverses
          -- I had a lot of difficulty using the corresponding proof where
          -- AreInverses is defined. This is sadly a bit anti-modular. The
          -- reason for my troubles is probably related to the type of objects
          -- being hSet's rather than sets.
          p : ∀ {f} g → isProp (AreInverses {A = A} {B} f g)
          p {f} g xx yy i = ve-re , re-ve
            where
            module xxA = AreInverses {f = f} {g} xx
            module yyA = AreInverses {f = f} {g} yy
            setPiB : ∀ {X : Set ℓ} → isSet (X → B)
            setPiB = setPi (λ _ → sB)
            setPiA : ∀ {X : Set ℓ} → isSet (X → A)
            setPiA = setPi (λ _ → sA)
            ve-re : g ∘ f ≡ idFun _
            ve-re = setPiA _ _ xxA.verso-recto yyA.verso-recto i
            re-ve : f ∘ g ≡ idFun _
            re-ve = setPiB _ _ xxA.recto-verso yyA.recto-verso i
          1eq : x.inverse ≡ y.inverse
          1eq = begin
            x.inverse                   ≡⟨⟩
            x.inverse ∘ idFun _         ≡⟨ cong (λ φ → x.inverse ∘ φ) (sym yA.recto-verso) ⟩
            x.inverse ∘ (f ∘ y.inverse) ≡⟨⟩
            (x.inverse ∘ f) ∘ y.inverse ≡⟨ cong (λ φ → φ ∘ y.inverse) xA.verso-recto ⟩
            idFun _ ∘ y.inverse         ≡⟨⟩
            y.inverse                   ∎
          2eq : (λ i → AreInverses f (1eq i)) [ x.areInverses ≡ y.areInverses ]
          2eq = lemPropF p _ _ 1eq
          res : x ≡ y
          res i = 1eq i , 2eq i

-- In HoTT they generalize an equivalence to have the following 3 properties:
module _ {ℓa ℓb ℓ : Level} (A : Set ℓa) (B : Set ℓb) where
  record Equiv (iseqv : (A → B) → Set ℓ) : Set (ℓa ⊔ ℓb ⊔ ℓ) where
    field
      fromIso      : {f : A → B} → Isomorphism f → iseqv f
      toIso        : {f : A → B} → iseqv f → Isomorphism f
      propIseqv    : (f : A → B) → isProp (iseqv f)

    -- You're alerady assuming here that we don't need eta-equality on the
    -- equivalence!
    _~_ : Set ℓa → Set ℓb → Set _
    A ~ B = Σ _ iseqv

    inverse-from-to-iso : ∀ {f} (x : _) → (fromIso {f} ∘ toIso {f}) x ≡ x
    inverse-from-to-iso x = begin
      (fromIso ∘ toIso) x ≡⟨⟩
      fromIso (toIso x)   ≡⟨ propIseqv _ (fromIso (toIso x)) x ⟩
      x ∎

    -- | The other inverse law does not hold in general, it does hold, however,
    -- | if `A` and `B` are sets.
    module _ (sA : isSet A) (sB : isSet B) where
      module _ {f : A → B} where
        module _ (iso-x iso-y : Isomorphism f) where
          open Σ iso-x renaming (fst to x ; snd to inv-x)
          open Σ iso-y renaming (fst to y ; snd to inv-y)

          fx≡fy : x ≡ y
          fx≡fy = begin
            x             ≡⟨ cong (λ φ → x ∘ φ) (sym (snd inv-y)) ⟩
            x ∘ (f ∘ y)   ≡⟨⟩
            (x ∘ f) ∘ y   ≡⟨ cong (λ φ → φ ∘ y) (fst inv-x) ⟩
            y ∎

          propInv : ∀ g → isProp (AreInverses f g)
          propInv g t u = λ i → a i , b i
            where
            a : (fst t) ≡ (fst u)
            a i = funExt hh
              where
              hh : ∀ a → (g ∘ f) a ≡ a
              hh a = sA ((g ∘ f) a) a (λ i → (fst t) i a) (λ i → (fst u) i a) i
            b : (snd t) ≡ (snd u)
            b i = funExt hh
              where
              hh : ∀ b → (f ∘ g) b ≡ b
              hh b = sB _ _ (λ i → snd t i b) (λ i → snd u i b) i

          inx≡iny : (λ i → AreInverses f (fx≡fy i)) [ inv-x ≡ inv-y ]
          inx≡iny = lemPropF propInv _ _ fx≡fy

          propIso : iso-x ≡ iso-y
          propIso i = fx≡fy i , inx≡iny i

        module _ (iso : Isomorphism f) where
          inverse-to-from-iso : (toIso {f} ∘ fromIso {f}) iso ≡ iso
          inverse-to-from-iso = begin
            (toIso ∘ fromIso) iso ≡⟨⟩
            toIso (fromIso iso)   ≡⟨ propIso _ _ ⟩
            iso ∎

    fromIsomorphism : A ≅ B → A ~ B
    fromIsomorphism (f , iso) = f , fromIso iso

    toIsomorphism : A ~ B → A ≅ B
    toIsomorphism (f , eqv) = f , toIso eqv

module _ {ℓa ℓb : Level} (A : Set ℓa) (B : Set ℓb) where
  -- A wrapper around Prelude.≃
  private
    module _ {obverse : A → B} (e : isEquiv obverse) where
      inverse : B → A
      inverse b = fst (fst (e .equiv-proof b))

      reverse : B → A
      reverse = inverse

      areInverses : AreInverses obverse inverse
      areInverses = funExt verso-recto , funExt recto-verso
        where
        recto-verso : ∀ b → (obverse ∘ inverse) b ≡ b
        recto-verso b = begin
          (obverse ∘ inverse) b ≡⟨ μ b ⟩
          b ∎
          where
          μ : (b : B) → obverse (inverse b) ≡ b
          μ b = snd (fst (e .equiv-proof b))
        verso-recto : ∀ a → (inverse ∘ obverse) a ≡ a
        verso-recto a = begin
          (inverse ∘ obverse) a ≡⟨ sym h ⟩
          a'                    ≡⟨ u' ⟩
          a ∎
          where
          c : isContr (fiber obverse (obverse a))
          c = e .equiv-proof (obverse a)
          fbr : fiber obverse (obverse a)
          fbr = fst c
          a' : A
          a' = fst fbr
          allC : (y : fiber obverse (obverse a)) → fbr ≡ y
          allC = snd c
          k : fbr ≡ (inverse (obverse a), _)
          k = allC (inverse (obverse a) , recto-verso (obverse a))
          h : a' ≡ inverse (obverse a)
          h i = fst (k i)
          u : fbr ≡ (a , refl)
          u = allC (a , refl)
          u' : a' ≡ a
          u' i = fst (u i)

      iso : Isomorphism obverse
      iso = reverse , areInverses

    toIsomorphism : {f : A → B} → isEquiv f → Isomorphism f
    toIsomorphism = iso

    ≃isEquiv : Equiv A B isEquiv
    Equiv.fromIso     ≃isEquiv {f} (f~ , iso) = gradLemma f f~ rv vr
      where
      rv : (b : B) → _ ≡ b
      rv b i = snd iso i b
      vr : (a : A) → _ ≡ a
      vr a i = fst iso i a
    Equiv.toIso        ≃isEquiv = toIsomorphism
    Equiv.propIseqv    ≃isEquiv = propIsEquiv

  open Equiv ≃isEquiv public

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  module _ {ℓc : Level} {C : Set ℓc} {f : A → B} {g : B → C} where

    composeIsomorphism : Isomorphism f → Isomorphism g → Isomorphism (g ∘ f)
    composeIsomorphism a b = f~ ∘ g~ , inv
      where
      open Σ a renaming (fst to f~ ; snd to inv-a)
      open Σ b renaming (fst to g~ ; snd to inv-b)
      inv : AreInverses (g ∘ f) (f~ ∘ g~)
      inv = record
        { fst = begin
          (f~ ∘ g~) ∘ (g ∘ f) ≡⟨⟩
          f~ ∘ (g~ ∘ g) ∘ f   ≡⟨ cong (λ φ → f~ ∘ φ ∘ f) (fst inv-b) ⟩
          f~ ∘ idFun _ ∘ f    ≡⟨⟩
          f~ ∘ f              ≡⟨ (fst inv-a) ⟩
          idFun A             ∎
        ; snd = begin
          (g ∘ f) ∘ (f~ ∘ g~) ≡⟨⟩
          g ∘ (f ∘ f~) ∘ g~   ≡⟨ cong (λ φ → g ∘ φ ∘ g~) (snd inv-a) ⟩
          g ∘ g~              ≡⟨ (snd inv-b) ⟩
          idFun C             ∎
        }

  composeIso : {ℓc : Level} {C : Set ℓc} → (A ≅ B) → (B ≅ C) → A ≅ C
  composeIso {C = C} (f , iso-f) (g , iso-g) = g ∘ f , composeIsomorphism iso-f iso-g

  symmetryIso : (A ≅ B) → B ≅ A
  symmetryIso (inverse , obverse , verso-recto , recto-verso)
    = obverse
    , inverse
    , recto-verso
    , verso-recto

preorder≅ : (ℓ : Level) → Preorder _ _ _
preorder≅ ℓ = record
  { Carrier = Set ℓ ; _≈_ = _≡_ ; _∼_ = _≅_
  ; isPreorder = record
    { isEquivalence = equalityIsEquivalence
    ; reflexive = λ p
      → coe p
      , coe (sym p)
      , funExt (λ x → inv-coe p)
      , funExt (λ x → inv-coe' p)
    ; trans = composeIso
    }
  }
  where
  module _ {ℓ : Level} {A B : Set ℓ} {a : A} where
    inv-coe : (p : A ≡ B) → coe (sym p) (coe p a) ≡ a
    inv-coe p =
      let
        D : (y : Set ℓ) → _ ≡ y → Set _
        D _ q = coe (sym q) (coe q a) ≡ a
        d : D A refl
        d = begin
          coe (sym refl) (coe refl a) ≡⟨⟩
          coe refl (coe refl a)       ≡⟨ coe-neutral _ ⟩
          coe refl a                  ≡⟨ coe-neutral _ ⟩
          a ∎
      in pathJ D d p
    inv-coe' : (p : B ≡ A) → coe p (coe (sym p) a) ≡ a
    inv-coe' p =
      let
        D : (y : Set ℓ) → _ ≡ y → Set _
        D _ q = coe (sym q) (coe q a) ≡ a
        k : coe p (coe (sym p) a) ≡ a
        k = pathJ D (trans (coe-neutral _) (coe-neutral _)) (sym p)
      in k

setoid≅ : (ℓ : Level) → Setoid _ _
setoid≅ ℓ = record
  { Carrier = Set ℓ
  ; _≈_ = _≅_
  ; isEquivalence = record
    { refl = idFun _ , idFun _ , (funExt λ _ → refl) , (funExt λ _ → refl)
    ; sym = symmetryIso
    ; trans = composeIso
    }
  }

setoid≃ : (ℓ : Level) → Setoid _ _
setoid≃ ℓ = record
  { Carrier = Set ℓ
  ; _≈_ = _≃_
  ; isEquivalence = record
    { refl = idEquiv _
    ; sym = invEquiv
    ; trans = compEquiv
    }
  }

module _ {ℓ : Level} {A B : Set ℓ} where
  isoToPath : (A ≅ B) → (A ≡ B)
  isoToPath = ua ∘ fromIsomorphism _ _

  -- Equivalence is equivalent to isomorphism when the equivalence (resp.
  -- isomorphism) acts on sets.
  module _ (sA : isSet A) (sB : isSet B) where
    equiv≃iso : (f : A → B) → isEquiv f ≃ Isomorphism f
    equiv≃iso f =
      let
        obv : isEquiv f → Isomorphism f
        obv = toIso A B
        inv : Isomorphism f → isEquiv f
        inv = fromIso A B
        re-ve : (x : isEquiv f) → (inv ∘ obv) x ≡ x
        re-ve = inverse-from-to-iso A B
        ve-re : (x : Isomorphism f) → (obv ∘ inv) x ≡ x
        ve-re = inverse-to-from-iso A B sA sB
        iso : isEquiv f ≅ Isomorphism f
        iso = obv , inv , funExt re-ve , funExt ve-re
      in fromIsomorphism _ _ iso

module _ {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb} where
  -- Equivalence is equivalent to isomorphism when the domain and codomain of
  -- the equivalence is a set.
  equivSetIso : isSet A → isSet B → (f : A → B)
    → isEquiv f ≃ Isomorphism f
  equivSetIso sA sB f =
    let
      obv : isEquiv f → Isomorphism f
      obv = toIso A B
      inv : Isomorphism f → isEquiv f
      inv = fromIso A B
      re-ve : (x : isEquiv f) → (inv ∘ obv) x ≡ x
      re-ve = inverse-from-to-iso A B
      ve-re : (x : Isomorphism f)       → (obv ∘ inv) x ≡ x
      ve-re = inverse-to-from-iso A B sA sB
      iso : isEquiv f ≅ Isomorphism f
      iso = obv , inv , funExt re-ve , funExt ve-re
    in fromIsomorphism _ _ iso
