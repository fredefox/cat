{-# OPTIONS --allow-unsolved-metas --cubical --caching #-}
module Cat.Categories.Fun where


open import Cat.Prelude
open import Cat.Equivalence
open import Cat.Category
open import Cat.Category.Functor
import Cat.Category.NaturalTransformation
  as NaturalTransformation
open import Cat.Categories.Opposite

module Fun {ℓc ℓc' ℓd ℓd' : Level} (ℂ : Category ℓc ℓc') (𝔻 : Category ℓd ℓd') where
  open NaturalTransformation ℂ 𝔻 public hiding (module Properties)
  private
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻

    module _ where
      -- Functor categories. Objects are functors, arrows are natural transformations.
      raw : RawCategory (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
      RawCategory.Object   raw = Functor ℂ 𝔻
      RawCategory.Arrow    raw = NaturalTransformation
      RawCategory.identity raw {F} = identity F
      RawCategory._<<<_    raw {F} {G} {H} = NT[_∘_] {F} {G} {H}

    module _ where
      open RawCategory raw hiding (identity)
      open NaturalTransformation.Properties ℂ 𝔻

      isPreCategory : IsPreCategory raw
      IsPreCategory.isAssociative isPreCategory {A} {B} {C} {D} = isAssociative {A} {B} {C} {D}
      IsPreCategory.isIdentity    isPreCategory {A} {B} = isIdentity {A} {B}
      IsPreCategory.arrowsAreSets isPreCategory {F} {G} = naturalTransformationIsSet {F} {G}

    open IsPreCategory isPreCategory hiding (identity)

    module _ {F G : Functor ℂ 𝔻} (p : F ≡ G) where
      private
        module F = Functor F
        module G = Functor G
        p-omap : F.omap ≡ G.omap
        p-omap = cong Functor.omap p
        pp : {C : ℂ.Object} → 𝔻 [ Functor.omap F C , Functor.omap F C ] ≡ 𝔻 [ Functor.omap F C , Functor.omap G C ]
        pp {C} = cong (λ f → 𝔻 [ Functor.omap F C , f C ]) p-omap
        module _ {C : ℂ.Object} where
          p* : F.omap C ≡ G.omap C
          p* = cong (_$ C) p-omap
          iso : F.omap C 𝔻.≊ G.omap C
          iso = 𝔻.idToIso _ _ p*
          open Σ iso renaming (fst to f→g) public
          open Σ (snd iso) renaming (fst to g→f ; snd to inv) public
          lem : coe (pp {C}) 𝔻.identity ≡ f→g
          lem = trans (𝔻.9-1-9-right {b = Functor.omap F C} 𝔻.identity p*) 𝔻.rightIdentity

      -- idToNatTrans : NaturalTransformation F G
      -- idToNatTrans = (λ C → coe pp 𝔻.identity) , λ f → begin
      --   coe pp 𝔻.identity 𝔻.<<< F.fmap f ≡⟨ cong (𝔻._<<< F.fmap f) lem ⟩
      --   -- Just need to show that f→g is a natural transformation
      --   -- I know that it has an inverse; g→f
      --   f→g 𝔻.<<< F.fmap f ≡⟨ {!lem!} ⟩
      --   G.fmap f 𝔻.<<< f→g ≡⟨ cong (G.fmap f 𝔻.<<<_) (sym lem) ⟩
      --   G.fmap f 𝔻.<<< coe pp 𝔻.identity ∎

    module _ {A B : Functor ℂ 𝔻} where
      module A = Functor A
      module B = Functor B
      module _ (iso : A ≊ B) where
        omapEq : A.omap ≡ B.omap
        omapEq = funExt eq
          where
          module _ (C : ℂ.Object) where
            f : 𝔻.Arrow (A.omap C) (B.omap C)
            f = fst (fst iso) C
            g : 𝔻.Arrow (B.omap C) (A.omap C)
            g = fst (fst (snd iso)) C
            inv : 𝔻.IsInverseOf f g
            inv
              = ( begin
               g 𝔻.<<< f ≡⟨ cong (λ x → fst x $ C) (fst (snd (snd iso))) ⟩
                𝔻.identity ∎
                )
              , ( begin
                f 𝔻.<<< g ≡⟨ cong (λ x → fst x $ C) (snd (snd (snd iso))) ⟩
                𝔻.identity ∎
                )
            isoC : A.omap C 𝔻.≊ B.omap C
            isoC = f , g , inv
            eq : A.omap C ≡ B.omap C
            eq = 𝔻.isoToId isoC


        U : (F : ℂ.Object → 𝔻.Object) → Set _
        U F = {A B : ℂ.Object} → ℂ [ A , B ] → 𝔻 [ F A , F B ]

      --   module _
      --     (omap : ℂ.Object → 𝔻.Object)
      --     (p    : A.omap ≡ omap)
      --     where
      --     D : Set _
      --     D = ( fmap : U omap)
      --       → ( let
      --            raw-B : RawFunctor ℂ 𝔻
      --            raw-B = record { omap = omap ; fmap = fmap }
      --         )
      --       → (isF-B' : IsFunctor ℂ 𝔻 raw-B)
      --       → ( let
      --           B' : Functor ℂ 𝔻
      --           B' = record { raw = raw-B ; isFunctor = isF-B' }
      --         )
      --       → (iso' : A ≊ B') → PathP (λ i → U (p i)) A.fmap fmap
      --     -- D : Set _
      --     -- D = PathP (λ i → U (p i)) A.fmap fmap
      --     -- eeq : (λ f → A.fmap f) ≡ fmap
      --     -- eeq = funExtImp (λ A → funExtImp (λ B → funExt (λ f → isofmap {A} {B} f)))
      --     --   where
      --     --   module _ {X : ℂ.Object} {Y : ℂ.Object} (f : ℂ [ X , Y ]) where
      --     --     isofmap : A.fmap f ≡ fmap f
      --     --     isofmap = {!ap!}
      --   d : D A.omap refl
      --   d = res
      --     where
      --     module _
      --       ( fmap : U A.omap )
      --       ( let
      --         raw-B : RawFunctor ℂ 𝔻
      --         raw-B = record { omap = A.omap ; fmap = fmap }
      --       )
      --       ( isF-B' : IsFunctor ℂ 𝔻 raw-B )
      --       ( let
      --         B' : Functor ℂ 𝔻
      --         B' = record { raw = raw-B ; isFunctor = isF-B' }
      --       )
      --       ( iso' : A ≊ B' )
      --       where
      --       module _ {X Y : ℂ.Object} (f : ℂ [ X , Y ]) where
      --         step : {!!} 𝔻.≊ {!!}
      --         step = {!!}
      --         resres : A.fmap {X} {Y} f ≡ fmap {X} {Y} f
      --         resres = {!!}
      --       res : PathP (λ i → U A.omap) A.fmap fmap
      --       res i {X} {Y} f = resres f i

      --   fmapEq : PathP (λ i → U (omapEq i)) A.fmap B.fmap
      --   fmapEq = pathJ D d B.omap omapEq B.fmap B.isFunctor iso

      --   rawEq : A.raw ≡ B.raw
      --   rawEq i = record { omap = omapEq i ; fmap = fmapEq i }

      -- private
      --   f : (A ≡ B) → (A ≊ B)
      --   f p = idToNatTrans p , idToNatTrans (sym p) , NaturalTransformation≡ A A (funExt (λ C → {!!})) , {!!}
      --   g : (A ≊ B) → (A ≡ B)
      --   g = Functor≡ ∘ rawEq
      --   inv : AreInverses f g
      --   inv = {!funExt λ p → ?!} , {!!}
      postulate
        iso : (A ≡ B) ≅ (A ≊ B)
--      iso = f , g , inv

      univ : (A ≡ B) ≃ (A ≊ B)
      univ = fromIsomorphism _ _ iso

    -- There used to be some work-in-progress on this theorem, please go back to
    -- this point in time to see it:
    --
    -- commit 6b7d66b7fc936fe3674b2fd9fa790bd0e3fec12f
    -- Author: Frederik Hanghøj Iversen <fhi.1990@gmail.com>
    -- Date:   Fri Apr 13 15:26:46 2018 +0200
    univalent : Univalent
    univalent = univalenceFrom≃ univ

    isCategory : IsCategory raw
    IsCategory.isPreCategory isCategory = isPreCategory
    IsCategory.univalent     isCategory = univalent

  Fun : Category (ℓc ⊔ ℓc' ⊔ ℓd ⊔ ℓd') (ℓc ⊔ ℓc' ⊔ ℓd')
  Category.raw        Fun = raw
  Category.isCategory Fun = isCategory

module _ {ℓ ℓ' : Level} (ℂ : Category ℓ ℓ') where
  private
    open import Cat.Categories.Sets
    open NaturalTransformation (opposite ℂ) (𝓢𝓮𝓽 ℓ')
    module K = Fun (opposite ℂ) (𝓢𝓮𝓽 ℓ')
    module F = Category K.Fun

    -- Restrict the functors to Presheafs.
    raw : RawCategory (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
    raw = record
      { Object = Presheaf ℂ
      ; Arrow = NaturalTransformation
      ; identity = λ {F} → identity F
      ; _<<<_ = λ {F G H} → NT[_∘_] {F = F} {G = G} {H = H}
      }

  --   isCategory : IsCategory raw
  --   isCategory = record
  --     { isAssociative =
  --       λ{ {A} {B} {C} {D} {f} {g} {h}
  --       → F.isAssociative {A} {B} {C} {D} {f} {g} {h}
  --       }
  --     ; isIdentity =
  --       λ{ {A} {B} {f}
  --       → F.isIdentity {A} {B} {f}
  --       }
  --     ; arrowsAreSets =
  --       λ{ {A} {B}
  --       → F.arrowsAreSets {A} {B}
  --       }
  --     ; univalent =
  --       λ{ {A} {B}
  --       → F.univalent {A} {B}
  --       }
  --     }

  -- Presh : Category (ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  -- Category.raw        Presh = raw
  -- Category.isCategory Presh = isCategory
