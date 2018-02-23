Changelog
=========

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
