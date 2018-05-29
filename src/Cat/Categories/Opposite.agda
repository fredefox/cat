{-# OPTIONS --cubical #-}
module Cat.Categories.Opposite where

open import Cat.Prelude
open import Cat.Equivalence
open import Cat.Category

-- | The opposite category
--
-- The opposite category is the category where the direction of the arrows are
-- flipped.
module _ {ℓa ℓb : Level} where
  module _ (ℂ : Category ℓa ℓb) where
    private
      module _ where
        module ℂ = Category ℂ
        opRaw : RawCategory ℓa ℓb
        RawCategory.Object   opRaw = ℂ.Object
        RawCategory.Arrow    opRaw = flip ℂ.Arrow
        RawCategory.identity opRaw = ℂ.identity
        RawCategory._<<<_    opRaw = ℂ._>>>_

        open RawCategory opRaw

        isPreCategory : IsPreCategory opRaw
        IsPreCategory.isAssociative isPreCategory = sym ℂ.isAssociative
        IsPreCategory.isIdentity    isPreCategory = swap ℂ.isIdentity
        IsPreCategory.arrowsAreSets isPreCategory = ℂ.arrowsAreSets

      open IsPreCategory isPreCategory

      module _ {A B : ℂ.Object} where
        open Σ (toIso _ _ (ℂ.univalent {A} {B}))
          renaming (fst to idToIso* ; snd to inv*)
        open AreInverses {f = ℂ.idToIso A B} {idToIso*} inv*

        shuffle : A ≊ B → A ℂ.≊ B
        shuffle (f , g , inv) = g , f , inv

        shuffle~ : A ℂ.≊ B → A ≊ B
        shuffle~ (f , g , inv) = g , f , inv

        lem : (p : A ≡ B) → idToIso A B p ≡ shuffle~ (ℂ.idToIso A B p)
        lem p = isoEq refl

        isoToId* : A ≊ B → A ≡ B
        isoToId* = idToIso* ∘ shuffle

        inv : AreInverses (idToIso A B) isoToId*
        inv =
          ( funExt (λ x → begin
            (isoToId* ∘ idToIso A B) x
              ≡⟨⟩
            (idToIso*  ∘ shuffle ∘ idToIso A B) x
              ≡⟨ cong (λ φ → φ x) (cong (λ φ → idToIso* ∘ shuffle ∘ φ) (funExt lem)) ⟩
            (idToIso*  ∘ shuffle ∘ shuffle~ ∘ ℂ.idToIso A B) x
              ≡⟨⟩
            (idToIso*  ∘ ℂ.idToIso A B) x
              ≡⟨ (λ i → verso-recto i x) ⟩
            x ∎)
          , funExt (λ x → begin
            (idToIso A B ∘ idToIso* ∘ shuffle) x
              ≡⟨ cong (λ φ → φ x) (cong (λ φ → φ ∘ idToIso* ∘ shuffle) (funExt lem)) ⟩
            (shuffle~ ∘ ℂ.idToIso A B ∘ idToIso* ∘ shuffle) x
              ≡⟨ cong (λ φ → φ x) (cong (λ φ → shuffle~ ∘ φ ∘ shuffle) recto-verso) ⟩
            (shuffle~ ∘ shuffle) x
              ≡⟨⟩
            x ∎)
          )

      isCategory : IsCategory opRaw
      IsCategory.isPreCategory isCategory = isPreCategory
      IsCategory.univalent     isCategory
        = univalenceFromIsomorphism (isoToId* , inv)

    opposite : Category ℓa ℓb
    Category.raw        opposite = opRaw
    Category.isCategory opposite = isCategory

  -- As demonstrated here a side-effect of having no-eta-equality on constructors
  -- means that we need to pick things apart to show that things are indeed
  -- definitionally equal. I.e; a thing that would normally be provable in one
  -- line now takes 13!! Admittedly it's a simple proof.
  module _ {ℂ : Category ℓa ℓb} where
    open Category ℂ
    private
      -- Since they really are definitionally equal we just need to pick apart
      -- the data-type.
      rawInv : Category.raw (opposite (opposite ℂ)) ≡ raw
      RawCategory.Object   (rawInv _) = Object
      RawCategory.Arrow    (rawInv _) = Arrow
      RawCategory.identity (rawInv _) = identity
      RawCategory._<<<_    (rawInv _) = _<<<_

    oppositeIsInvolution : opposite (opposite ℂ) ≡ ℂ
    oppositeIsInvolution = Category≡ rawInv
