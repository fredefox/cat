Backlog
=======

Prove postulates in `Cat.Wishlist`:
 * `ntypeCommulative : n ≤ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A`

Prove that these two formulations of univalence are equivalent:

    ∀ A B → isEquiv (A ≡ B) (A ≅ B) (idToIso A B)
    ∀ A   → isContr (Σ[ X ∈ Object ] A ≅ X)

Prove univalence for the category of
  * functors and natural transformations

Prove:
  * `isProp (Product ...)`
  * `isProp (HasProducts ...)`

Rename composition in categories

In stead of using AreInverses, just use a sigma-type

Ideas for future work
---------------------

It would be nice if my formulation of monads is not so "stand-alone" as it is at
the moment.

We can built up the notion of monads and related concept in multiple ways as
demonstrated in the two equivalent formulations of monads (kleisli/monoidal):
There seems to be a category-theoretic approach and an approach more in the
style of functional programming as e.g. the related typeclasses in the
standard library of Haskell.

It would be nice to build up this hierarchy in two ways: The
"category-theoretic" way and the "functional programming" way.

Here is an overview of some of the concepts that need to be developed to acheive
this:

* Functor ✓
* Applicative Functor ✗
  * Lax monoidal functor ✗
    * Monoidal functor ✗
  * Tensorial strength ✗
* Category ✓
  * Monoidal category ✗
* Monad
  * Monoidal monad ✓
  * Kleisli monad ✓
  * Kleisli ≃ Monoidal ✓
  * Problem 2.3 in [voe] ✓
    * 1st contruction ~ monoidal ✓
    * 2nd contruction ~ klesli ✓
      * 1st ≃ 2nd ✓
