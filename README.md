Description
===========
This project aims to formalize some parts of category theory using cubical agda
&mdash; an extension to agda permitting univalence.  To learn more about this
[read the docs](https://agda.readthedocs.io/en/latest/language/cubical.html).

This project draws a lot of inspiration from [the
HoTT-book](https://homotopytypetheory.org/book/).

If you want more information about this project, then you're in luck.
This is my masters thesis.  Go ahead and read it
[here](http://web.student.chalmers.se/~hanghj/papers/univalent-categories.pdf)
or alternative like so:

    cd doc/
    make

Dependencies
============
To successfully compile the following is needed:

* [Agda](https://github.com/agda/agda)
* [Agda Standard Library](https://github.com/agda/agda-stdlib)
* [Agda Cubical Library](https://github.com/agda/cubical)

Has been tested with:

  * Agda versions 2.6.1 and 2.6.2[^1]
  * Agda Standard Library version v1.3-9f454e23
  * Agda Cubical Library version v0.1-acabbd9

[^1]: Revisions `02cb18a` and `61ea3a3`.

Building
========
You can build the library with

    git submodule update --init
    make

The library file `.agda-lib` takes care of using the right
dependencies, which are cloned as "submodules" into the `libs`
directory by the first command line.
