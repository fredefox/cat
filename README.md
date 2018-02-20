Description
===========
This project includes code as well as my masters thesis (currently just
consisting of the proposal for the thesis).

Installation
============

Dependencies
------------
To succesfully compile the following is needed:

* Agda version >= `707ce6042b6a3bdb26521f3fe8dfe5d8a8470a43`.
* Agda Standard Library >= `87d28d7d753f73abd20665d7bbb88f9d72ed88aa`.

I've used git submodules to manage dependencies. Unfortunately Agda does not
allow specifying libraries to be used only as local dependencies.

You can let Agda know about these libraries by appending them to your global
libraries file like so: (NB!: There is a good reason this is not in a
makefile. So please verify that you know what you are doing, you probably
already have standard-library in you libraries)

    AGDA_LIB=~/.agda
    readlink -f libs/*/*.agda-lib | tee -a $AGDA_LIB/libraries

Anyways, assuming you have this set up you should be good to go.
