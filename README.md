Description
===========
This project aims to formalize some parts of category theory using cubical agda
&mdash; an extension to agda permitting univalence. To learn more about this
[read the docs](https://agda.readthedocs.io/en/latest/language/cubical.html).

This project draws a lot of inspiration from [the
HoTT-book](https://homotopytypetheory.org/book/).

Installation
============

Dependencies
------------
To succesfully compile the following is needed:

* The Agda release candidate 2.5.4[^1]
* [Agda Standard Library](https://github.com/agda/agda-stdlib)
* [Cubical](https://github.com/Saizan/cubical-demo/)

[^1]: At least version >= [`707ce6042b6a3bdb26521f3fe8dfe5d8a8470a43`](https://github.com/agda/agda/commit/707ce6042b6a3bdb26521f3fe8dfe5d8a8470a43)

The version of the libraries that this depends on can be shown by
executing the following command in the root directory of the project:

    git submodule foreach git rev-parse HEAD

Unfortunately Agda's module system does not allow us to automatically
add these dependencies. So you'll have to make sure you're using
versions of these libraries that are compatible with this
project. Since this information is only provided as documentation it
may also noot be up-to-date so beware.

You can let Agda know about these libraries by appending them to your global
libraries file like so: (NB!: There is a good reason this is not in a
makefile. So please verify that you know what you are doing, you probably
already have standard-library in you libraries)

    AGDA_LIB=~/.agda
    readlink -f libs/*/*.agda-lib | tee -a $AGDA_LIB/libraries

Anyways, assuming you have this set up you should be good to go.
