Backlog
=======

Prove postulates in `Cat.Wishlist`:
 * `ntypeCommulative : n ≤ m → HasLevel ⟨ n ⟩₋₂ A → HasLevel ⟨ m ⟩₋₂ A`

Prove univalence for the category of
  * the opposite category
  * sets
    This does not follow trivially from `Cubical.Univalence.univalence` because
    objects are not `Set` but `hSet`
  * functors and natural transformations

Prove:
  * `isProp (Product ...)`
  * `isProp (HasProducts ...)`

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
  * Problem 2.3 in [voe]
    * 1st contruction ~ monoidal ✓
    * 2nd contruction ~ klesli ✓
      * 1st ≃ 2nd ✗
        I've managed to set this up so I should be able to reuse the proof that
        Kleisli ≃ Monoidal, but I don't know why it doesn't typecheck.
