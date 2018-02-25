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

  -- Might not need this to be able to form products of categories!
  postulate unprovable : IsCategory (Cat.RawCat ℓa ℓb)

  open HasProducts (Cat.hasProducts unprovable)

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
