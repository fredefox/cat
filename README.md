Description
===========
This project includes code as well as my masters thesis (currently just
consisting of the proposal for the thesis).

Installation
============
You probably need a very recent version of the Agda compiler. At the time
of writing the solution has been tested with Agda version 2.6.0-9af3e07.

Dependencies
------------
I've used git submodules to manage dependencies. Unfortunately Agda does not
allow specifying libraries to be used only as local dependencies.

You can let Agda know about these libraries by appending them to your global
libraries file like so: (NB!: There is a good reason this is not in a
makefile. So please verify that you know what you are doing, you probably
already have standard-library in you libraries)

    AGDA_LIB=~/.agda
    readlink -f libs/*/*.agda-lib | tee -a $AGDA_LIB/libraries

Anyways, assuming you have this set up you should be good to go.
