module Cat.Category.Monoid where

open import Agda.Primitive

open import Cat.Category
open import Cat.Category.Product
open import Cat.Category.Functor
import Cat.Categories.Cat as Cat

-- TODO: Incorrect!
module _ (ℓa ℓb : Level) where
  private
    ℓ = lsuc (ℓa ⊔ ℓb)

    -- *If* the category of categories existed `_×_` would be equivalent to the
    -- one brought into scope by doing:
    --
    --     open HasProducts (Cat.hasProducts unprovable) using (_×_)
    --
    -- Since it doesn't we'll make the following (definitionally equivalent) ad-hoc definition.
    _×_ : ∀ {ℓa ℓb} → Category ℓa ℓb → Category ℓa ℓb → Category ℓa ℓb
    ℂ × 𝔻 = Cat.CatProduct.obj ℂ 𝔻

  record RawMonoidalCategory : Set ℓ where
    field
      category : Category ℓa ℓb
    open Category category public
    field
      {{hasProducts}} : HasProducts category
      mempty  : Object
      -- aka. tensor product, monoidal product.
      mappend : Functor (category × category) category

  record MonoidalCategory : Set ℓ where
    field
      raw : RawMonoidalCategory
    open RawMonoidalCategory raw public

module _ {ℓa ℓb : Level} (ℂ : MonoidalCategory ℓa ℓb) where
  private
    ℓ = ℓa ⊔ ℓb

  module MC = MonoidalCategory ℂ
  open HasProducts MC.hasProducts
  record Monoid : Set ℓ where
    field
      carrier : MC.Object
      mempty  : MC.Arrow (carrier × carrier)  carrier
      mappend : MC.Arrow MC.mempty carrier
