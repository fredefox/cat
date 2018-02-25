Changelog
=========

Version 1.3.0
-------------

Removed unused modules and streamlined things more: All specific categories are
in the namespace `Cat.Categories`.

Lemmas about categories are now in the appropriate record e.g. `IsCategory`.
Also changed how category reexports stuff.

Rename the module Properties to Yoneda - because that's all it talks about now.

Rename Opposite to opposite

Add documentation in Category-module

Formulation of monads in two ways; the "monoidal-" and "kleisli-" form.

WIP: Equivalence of these two formulations

Also use hSets in a few concrete categories rather than just pure `Set`.

Version 1.2.0
-------------
This version is mainly a huge refactor.

I've renamed

* `distrib` to `isDistributive`
* `arrowIsSet` to `arrowsAreSets`
* `ident` to `isIdentity`
* `assoc` to `isAssociative`

And added "type-synonyms" for all of these. Their names should now match their
type. So e.g. `isDistributive` has type `IsDistributive`.

I've also changed how names are exported in `Functor` to be in line with
`Category`.

Version 1.1.0
-------------
In this version categories have been refactored - there's now a notion of a raw
category, and a proper category which has the data (raw category) as well as
the laws.

Furthermore the type of arrows must be homotopy sets and they must satisfy univalence.

I've made a module `Cat.Wishlist` where I just postulate things that I hope to
implement upstream in `cubical`.

I have proven that `IsCategory` is a mere proposition.

I've also updated the category of sets to adhere to this new definition.
