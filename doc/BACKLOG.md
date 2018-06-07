Presentation
====
Find one clear goal.

Remember crowd-control.

Leave out:
  lemPropF

Outline
-------

Introduction

A formalization of Category Theory in cubical Agda.

Cubical Agda: A constructive interpretation of functional
extensionality and univalence

Talk about structure of library:
===

What can I say about reusability?

Meeting with Andrea May 18th
============================

App. 2 in HoTT gives typing rule for pathJ including a computational
rule for it.

If you have this computational rule definitionally, then you wouldn't
need to use `pathJprop`.

In discussion-section I mention HITs. I should remove this or come up
with a more elaborate example of something you could do, e.g.
something with pushouts in the category of sets.

The type Prop is a type where terms are *judgmentally* equal not just
propositionally so.

Maybe mention that Andreas Källberg is working on proving the
initiality conjecture.

Intensional Type Theory (ITT): Judgmental equality is decidable

Extensional Type Theory (ETT): Reflection is enough to make judgmental
equality undecidable.

  Reflection : a ≡ b → a = b

ITT does not have reflections.

HTT ~ ITT + axiomatized univalence
Agda ~ ITT + K-rule
Coq  ~ ITT (no K-rule)
Cubical Agda ~ ITT + Path + Glue

Prop is impredicative in Coq (whatever that means)

Prop ≠ hProp

Comments about abstract
-----

Pattern matching for paths (?)

Intro
-----
Main feature of judgmental equality is the conversion rule.

Conor explained: K + eliminators ≡ pat. matching

Explain jugmental equality independently of type-checking

Soundness for equality means that if `x = y` then `x` and `y` must be
equal according to the theory/model.

Decidability of `=` is a necessary condition for typechecking to be
decidable.

Canonicity is a nice-to-have though without canonicity terms can get
stuck. If we postulate results about judgmental equality. E.g. funext,
then we can construct a term of type natural number that is not a
numeral. Therefore stating canonicity with natural numbers:

    ∀ t . ⊢ t : N , ∃ n : N . ⊢ t = sⁿ 0 : N

is a sufficient condition to get a well-behaved equality.

Eta-equality for RawFunctor means that the associative law for
functors hold definitionally.

Computational property for funExt is only relevant in two places in my
whole formulation. Univalence and gradLemma does not influence any
proofs.
