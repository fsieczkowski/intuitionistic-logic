# Intuitionistic propositional logic: Soundness and Completeness

This project contains a simple formalisation of soundness and
completeness of intuitionistic propositional logic (in the
natural-deduction presentation) with respect to its algebraic
semantics (i.e., Heyting algebras). The contents of the modules are as
follows:

* [`Syntax`](./Syntax.v) contains the syntax of IPL propositions and
  some notations;
* [`Deduction`](./Deduction.v) contains the definition of natural
  deduction for IPL, and the proof of a weakening lemma;
* [`Heyting`](./Heyting.v) contains an axiomatisation of Heyting
  algebras, as well as some derived facts; note that the algebra is
  defined as a pre-order, with elements ordered in both directions
  taken as equivalent;
* [`Interp`](./Interp.v) defines an interpretation of IPL propositions
  in a Heyting algebra;
* [`Soundness`](./Soundness.v) proves the interpretation sound with
  respect to natural deduction;
* [`Completeness`](./Completeness.v) contains the construction of the
  Lindenbaum algebra and the proof of completeness.

To compile the project, run `make -f CoqMakefile`. Tested with Coq v8.19.1.
