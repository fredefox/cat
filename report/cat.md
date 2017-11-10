---
title: Formalizing category theory in Agda - Project description
date: May 27th 2017
author: Frederik Hanghøj Iversen `<hanghj@student.chalmers.se>`
bibliography: refs.bib
---

Background
==========

Functional extensionality gives rise to a notion of equality of functions not
present in intensional dependent type theory. A type-system called cubical
type-theory is outlined in [@cohen-2016] that recovers the computational
interprtation of the univalence theorem.

Keywords: The category of sets, limits, colimits, functors, natural
transformations, kleisly category, yoneda lemma, closed cartesian categories,
propositional logic.

<!--
"[...] These foundations promise to resolve several seemingly unconnected
problems-provide a support for categorical and higher categorical arguments
directly on the level of the language, make formalizations of usual mathematics
much more concise and much better adapted to the use with existing proof
assistants such as Coq [...]"

From "Univalent Foundations of Mathematics" by "Voevodsky".

-->

Aim
===

The aim of the project is two-fold. The first part of the project will be
concerned with formalizing some concepts from category theory in Agda's
type-system. This formalization should aim to incorporate definitions and
theorems that allow us to express the correpondence in the second part: Namely
showing the correpondence between well-typed terms in cubical type theory as
presented in Huber and Thierry's paper and with that of some concepts from Category Theory.

This latter part is not entirely clear for me yet, I know that all these are relevant keywords:

  * The category, C, of names and substitutions
  * Cubical Sets, i.e.: Functors from C to Set (the category of sets)
  * Presheaves
  * Fibers and fibrations

These are all formulated in the language of Category Theory. The purpose it to
show what they correspond to in the in Cubical Type Theory. As I understand it
at least the last buzzword on this list corresponds to Type Families.

I'm not sure how I'll go about expressing this in Agda. I suspect it might
be a matter of demostrating that these two formulations are isomorphic.

So far I have some experience with at least expressing some categorical
concepts in Agda using this new notion of equality. That is, equaility is in
some sense a continuuous path from a point of some type to another. So at the
moment, my understanding of cubical type theory is just that it has another
notion of equality but is otherwise pretty much the same.

Timeplan
========

The first part of the project will focus on studying and understanding the
foundations for this project namely; familiarizing myself with basic concepts
from category theory, understanding how cubical type theory gives rise to
expressing functional extensionality and the univalence theorem.

After I have understood these fundamental concepts I will use them in the
formalization of functors, applicative functors, monads, etc.. in Agda. This
should be done before the end of the first semester of the school-year
2017/2018.

At this point I will also have settled on a direction for the rest of the
project and developed a time-plan for the second phase of the project. But
cerainly it will involve applying the result of phase 1 in some context as
mentioned in [the project aim][aim].

Resources
=========

* Cubical demo by Andrea Vezossi: [@cubical-demo]
* Paper on cubical type theory [@cohen-2016]
* Book on homotopy type theory: [@hott-2013]
* Book on category theory: [@awodey-2006]
* Modal logic - Modal type theory,
  see [ncatlab](https://ncatlab.org/nlab/show/modal+type+theory).

References
==========
