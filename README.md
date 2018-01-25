# Mechanized Metatheory 2

Every now and then, I get nerd sniped by mechanized metatheory. This
repository contains some Coq developments formalizing some results
based on logical relations.

This development uses raw de Bruijn indices to formalize variable
binding. To avoid repeatedly proving boring facts about substitution
on de Bruijn representations for each language separately, there is a
single, centralized ABT library that is parametrized by the operators
in the language and their arity. This is described in slightly more
detail below.

## Build instructions

    make

## Guide to files

- `abt.v`: The abstract binding tree framework. Defines capture
  avoiding substitution once and for all.
- `abtutil.v`: Makes it convenient to leverage the ABT framework on a
  client-specific abstract *syntax* tree by proving an isomorphism to
  an equivalent ABT representation. The library also provides tactics
  for proving this isomorphism. Once proved, many theorems about
  capture avoiding substitution come for free.
- `util.v`: Various lemmas that should probably be in the stdlib.
- `stlc.v`: Syntax, operational semantics, and type system for the
  simply typed lambda calculus over booleans. Uses the ABT framework
  to get facts about substitution essentially for free.
- `stlc_unary.v`: A unary logical relation for proving termination of STLC.
- `stlc_binary.v`: A binary logical relation for establishing
  contextual equivalence in STLC.
- `f.v`: Syntax, operational semantics, and type system for System F
  with booleans, universal and existential types, and
  functions. Again, uses the ABT framework for substitution theorems.
- `f_unary.v`: A unary logical relation for proving termination of
  System F. Also contains some applications to proving "free theorems"
  for universal types.

## References

I found the following references especially helpful:

- [Semantics of Type Systems](https://plv.mpi-sws.org/semantics/2017/lecturenotes.pdf)
  by Derek Dreyer et al. The termination proofs for STLC and System F
  are formalized based on these notes.
- [Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types](http://www.ccs.neu.edu/home/amal/papers/lr-recquant-techrpt.pdf)
  by Amal Ahmed. The binary logical relations (even those for vanilla
  STLC and System F) are based on a combination of the unary notes
  above and this very detailed appendix about contextual equivalence.

## Coming Soon

I have put some ideas for extensions in [`TODO.md`](TODO.md).
