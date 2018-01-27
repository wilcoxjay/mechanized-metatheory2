- prove some consequnces of f_unary for existential types
- prove f_binary sound for contextual equivalence
- prove some consequnces of f_binary for existential types
- do step-indexed versions of all these models (won't prove termination, but semantic safety)
- do a language first-order state
- in a binary model of a language with state, prove some nontrivial equivalences
- do a language with recursive types
- do a language with concurrency

- consider purely functional arrays, implemented in two ways:
      1. arrays are values
      2. arrays are allocated on a heap
  for programs that are well typed in a linear lambda calcus,
  formalize and prove the claim that these two semantics are equivalent.
  One way to do this would be to prove some sort of simulation result
  between the two semantics, assuming well typed linear programs.
  Another way would be to prove that "all the usual reasoning
  principles from purel functional land" are sound in the heap
  semantics.

- formalize various meta theorems from Frank's substructural logic
  course notes.
