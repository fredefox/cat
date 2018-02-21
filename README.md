Description
===========
This project aims to formalize some parts of category theory using cubical agda
&mdash; an extension to agda permitting univalence. To learn more about this
[readthedocs](https://agda.readthedocs.io/en/latest/language/cubical.html).

This project draws a lot of inspiration from [the
HoTT-book](https://homotopytypetheory.org/book/).

Installation
============

Dependencies
------------
To succesfully compile the following is needed:

* Agda version >= `707ce6042b6a3bdb26521f3fe8dfe5d8a8470a43`.
* [Agda Standard Library](https://github.com/agda/agda-stdlib)
* [Cubical](https://github.com/Saizan/cubical-demo/)

It's important to have the right version of these - but which one is the right
is in constant flux. It's most likely the newest one.

I've used git submodules to manage dependencies. Unfortunately Agda does not
allow specifying libraries to be used only as local dependencies. So the
submodules are mostly used for documentation.

You can let Agda know about these libraries by appending them to your global
libraries file like so: (NB!: There is a good reason this is not in a
makefile. So please verify that you know what you are doing, you probably
already have standard-library in you libraries)

    AGDA_LIB=~/.agda
    readlink -f libs/*/*.agda-lib | tee -a $AGDA_LIB/libraries

Anyways, assuming you have this set up you should be good to go.
