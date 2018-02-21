Changelog
=========

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
