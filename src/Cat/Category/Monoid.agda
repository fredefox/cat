{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --cubical              #-}
module Cat.Category.Monoid where

open import Agda.Primitive

open import Cat.Category
open import Cat.Category.Product
open import Cat.Category.Functor
import Cat.Categories.Cat as Cat
open import Cat.Prelude hiding (_×_ ; empty)

-- TODO: Incorrect!
module _ {ℓa ℓb : Level} where
  private
    ℓ = lsuc (ℓa ⊔ ℓb)

    -- *If* the category of categories existed `_×_` would be equivalent to the
    -- one brought into scope by doing:
    --
    --     open HasProducts (Cat.hasProducts unprovable) using (_×_)
    --
    -- Since it doesn't we'll make the following (definitionally equivalent) ad-hoc definition.
    _×_ : ∀ {ℓa ℓb} → Category ℓa ℓb → Category ℓa ℓb → Category ℓa ℓb
    ℂ × 𝔻 = Cat.CatProduct.object ℂ 𝔻

  record RawMonoidalCategory (ℂ : Category ℓa ℓb) : Set ℓ where
    open Category ℂ public hiding (IsAssociative)
    field
      empty  : Object
      -- aka. tensor product, monoidal product.
      append : Functor (ℂ × ℂ) ℂ

    module F = Functor append

    _⊗_ = append
    mappend = F.fmap

    IsAssociative : Set _
    IsAssociative = {A B : Object} → (f g h : Arrow A A) → mappend ({!mappend!} , {!mappend!}) ≡ mappend (f , mappend (g , h))

  record MonoidalCategory (ℂ : Category ℓa ℓb) : Set ℓ where
    field
      raw : RawMonoidalCategory ℂ
    open RawMonoidalCategory raw public

module _ {ℓa ℓb : Level} (ℂ : Category ℓa ℓb) {monoidal : MonoidalCategory ℂ} {hasProducts : HasProducts ℂ} where
  private
    ℓ = ℓa ⊔ ℓb

  open MonoidalCategory monoidal public hiding (mappend)
  open HasProducts hasProducts

  record MonoidalObject (M : Object) : Set ℓ where
    field
      mempty  : Arrow empty M
      mappend : Arrow (M × M) M
