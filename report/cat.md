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
type-theory is outlined in [@cohen-2016] that recovers the computational interprtation of the univalence theorem.

Keywords: The category of sets, limits, colimits, functors, natural
transformations, kleisly category, yoneda lemma, closed cartesian categories,
propositional logic.

Aim
===

The aim of the project is two-fold. The first part of the project will be
concerned with formalizing some concepts from category theory in Agda's
type-system: functors, applicative functors, monads, etc.. The second part of
the project could take different directions:

* It might involve using this formalization to prove properties of functional
  programs.
* It may be used to prove the Modal used in Cubical Type Theory using Preshiefs.

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
* Modal logic - Modal type theory, see
  [ncatlab](https://ncatlab.org/nlab/show/modal+type+theory).

References
==========
