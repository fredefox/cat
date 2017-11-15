{-# OPTIONS --cubical #-}
module Category.Rel where

open import Data.Product
open import Cubical.PathPrelude
open import Cubical.GradLemma
open import Agda.Primitive
open import Category

-- Subsets are predicates over some type.
Subset : {ℓ : Level} → ( A : Set ℓ ) → Set (ℓ ⊔ lsuc lzero)
Subset A = A → Set
-- Subset : {ℓ ℓ' : Level} → ( A : Set ℓ ) → Set (ℓ ⊔ lsuc ℓ')
-- Subset {ℓ' = ℓ'} A = A → Set ℓ'
-- {a ∈ A | P a}

-- subset-syntax : {ℓ ℓ' : Level} → (A : Set ℓ) → (P : A → Set ℓ') → ( a : A ) → Set ℓ'
-- subset-syntax A P a = P a
-- infix 2 subset-syntax

-- syntax subset P a = << a ∈ A >>>
-- syntax subset P = ⦃ a ∈ A | P a ⦄
-- syntax subset-syntax A (λ a → B) = ⟨ a foo A ∣ B ⟩

-- Membership is function applicatiom.
_∈_ : {ℓ : Level} {A : Set ℓ} → A → Subset A → Set
s ∈ S = S s

infixl 45 _∈_

-- The diagnoal of a set is a synonym for equality.
Diag : ∀ S → Subset (S × S)
Diag S (s₀ , s₁) = s₀ ≡ s₁
-- Diag S = subset (S × S) (λ {(p , q) → p ≡ q})
-- Diag S = ⟨ ? foo ? ∣ ? ⟩
-- Diag S (s₀ , s₁) = ⦃ (s₀ , s₁) ∈ S | s₀ ≡ s₁ ⦄

module _ {A B : Set} {S : Subset (A × B)} (ab : A × B) where
  private
    a : A
    a = fst ab
    b : B
    b = snd ab

  module _ where
    private
      forwards : ((a , b) ∈ S)
        → (Σ[ a' ∈ A ] (a , a') ∈ Diag A × (a' , b) ∈ S)
      forwards ab∈S = a , (refl , ab∈S)

      backwards : (Σ[ a' ∈ A ] (a , a') ∈ Diag A × (a' , b) ∈ S)
        → (a , b) ∈ S
      backwards (a' , (a=a' , a'b∈S)) = subst (sym a=a') a'b∈S

      fwd-bwd : (x : (a , b) ∈ S) → (backwards ∘ forwards) x ≡ x
      -- isbijective x = pathJ (λ y x₁ → (backwards ∘ forwards) x ≡ x) {!!} {!!} {!!}
      fwd-bwd x = pathJprop (λ y _ → y) x

      bwd-fwd : (x : Σ[ a' ∈ A ] (a , a') ∈ Diag A × (a' , b) ∈ S)
          → (forwards ∘ backwards) x ≡ x
      -- bwd-fwd (y , a≡y , z) = ?
      bwd-fwd (a' , a≡y , z) = pathJ lem0 lem1 a' a≡y z
        where
          lem0 = (λ a'' a≡a'' → ∀ a''b∈S → (forwards ∘ backwards) (a'' , a≡a'' , a''b∈S) ≡ (a'' , a≡a'' , a''b∈S))
          lem1 = (λ z₁ → cong (\ z → a , refl , z) (pathJprop (\ y _ → y) z₁))

      isequiv : isEquiv
        (Σ[ a' ∈ A ] (a , a') ∈ Diag A × (a' , b) ∈ S)
        ((a , b) ∈ S)
        backwards
      isequiv y = gradLemma backwards forwards fwd-bwd bwd-fwd y

      equi : (Σ[ a' ∈ A ] (a , a') ∈ Diag A × (a' , b) ∈ S)
        ≃ (a , b) ∈ S
      equi = backwards , isequiv

    ident-l : (Σ[ a' ∈ A ] (a , a') ∈ Diag A × (a' , b) ∈ S)
      ≡ (a , b) ∈ S
    ident-l = equivToPath equi

  module _ where
    private
      forwards : ((a , b) ∈ S)
        → (Σ[ b' ∈ B ] (a , b') ∈ S × (b' , b) ∈ Diag B)
      forwards proof = b , (proof , refl)

      backwards : (Σ[ b' ∈ B ] (a , b') ∈ S × (b' , b) ∈ Diag B)
        → (a , b) ∈ S
      backwards (b' , (ab'∈S , b'=b)) = subst b'=b ab'∈S

      bwd-fwd : (x : (a , b) ∈ S) → (backwards ∘ forwards) x ≡ x
      bwd-fwd x = pathJprop (λ y _ → y) x

      fwd-bwd : (x : Σ[ b' ∈ B ] (a , b') ∈ S × (b' , b) ∈ Diag B)
        → (forwards ∘ backwards) x ≡ x
      fwd-bwd (b' , (ab'∈S , b'≡b)) = pathJ lem0 lem1 b' (sym b'≡b) ab'∈S
        where
          lem0 = (λ b'' b≡b'' → (ab''∈S : (a , b'') ∈ S) → (forwards ∘ backwards) (b'' , ab''∈S , sym b≡b'') ≡ (b'' , ab''∈S , sym b≡b''))
          lem1 = (λ ab''∈S → cong (λ φ → b , φ , refl) (pathJprop (λ y _ → y) ab''∈S))

      isequiv : isEquiv
        (Σ[ b' ∈ B ] (a , b') ∈ S × (b' , b) ∈ Diag B)
        ((a , b) ∈ S)
        backwards
      isequiv ab∈S = gradLemma backwards forwards bwd-fwd fwd-bwd ab∈S

      equi : (Σ[ b' ∈ B ] (a , b') ∈ S × (b' , b) ∈ Diag B)
        ≃ ab ∈ S
      equi = backwards , isequiv

    ident-r : (Σ[ b' ∈ B ] (a , b') ∈ S × (b' , b) ∈ Diag B)
      ≡ ab ∈ S
    ident-r = equivToPath equi

module _ {A B C D : Set} {S : Subset (A × B)} {R : Subset (B × C)} {Q : Subset (C × D)} (ad : A × D) where
  private
    a : A
    a = fst ad
    d : D
    d = snd ad

    Q⊕⟨R⊕S⟩ : Set
    Q⊕⟨R⊕S⟩ = Σ[ c ∈ C ] (Σ[ b ∈ B ] (a , b) ∈ S × (b , c) ∈ R) × (c , d) ∈ Q
    ⟨Q⊕R⟩⊕S : Set
    ⟨Q⊕R⟩⊕S = Σ[ b ∈ B ] (a , b) ∈ S × (Σ[ c ∈ C ] (b , c) ∈ R × (c , d) ∈ Q)

    fwd : Q⊕⟨R⊕S⟩ → ⟨Q⊕R⟩⊕S
    fwd (c , (b , (ab∈S , bc∈R)) , cd∈Q) = b , (ab∈S , (c , (bc∈R , cd∈Q)))

    bwd : ⟨Q⊕R⟩⊕S → Q⊕⟨R⊕S⟩
    bwd (b , (ab∈S , (c , (bc∈R , cd∈Q)))) = c , (b , ab∈S , bc∈R) , cd∈Q

    fwd-bwd : (x : ⟨Q⊕R⟩⊕S) → (fwd ∘ bwd) x ≡ x
    fwd-bwd x = refl

    bwd-fwd : (x : Q⊕⟨R⊕S⟩) → (bwd ∘ fwd) x ≡ x
    bwd-fwd x = refl

    isequiv : isEquiv
      (Σ[ c ∈ C ] (Σ[ b ∈ B ] (a , b) ∈ S × (b , c) ∈ R) × (c , d) ∈ Q)
      (Σ[ b ∈ B ] (a , b) ∈ S × (Σ[ c ∈ C ] (b , c) ∈ R × (c , d) ∈ Q))
      fwd
    isequiv = gradLemma fwd bwd fwd-bwd bwd-fwd

    equi : (Σ[ c ∈ C ] (Σ[ b ∈ B ] (a , b) ∈ S × (b , c) ∈ R) × (c , d) ∈ Q)
      ≃ (Σ[ b ∈ B ] (a , b) ∈ S × (Σ[ c ∈ C ] (b , c) ∈ R × (c , d) ∈ Q))
    equi = fwd , isequiv

    -- assocc : Q + (R + S) ≡ (Q + R) + S
  assocc : (Σ[ c ∈ C ] (Σ[ b ∈ B ] (a , b) ∈ S × (b , c) ∈ R) × (c , d) ∈ Q)
         ≡ (Σ[ b ∈ B ] (a , b) ∈ S × (Σ[ c ∈ C ] (b , c) ∈ R × (c , d) ∈ Q))
  assocc = equivToPath equi

Rel : Category
Rel = record
  { Object = Set
  ; Arrow = λ S R → Subset (S × R)
  ; 𝟙 = λ {S} → Diag S
  ; _⊕_ = λ {A B C} S R → λ {( a , c ) → Σ[ b ∈ B ] ( (a , b) ∈ R × (b , c) ∈ S )}
  ; assoc = funExt assocc
  ; ident = funExt ident-l , funExt ident-r
  }
