# Formalization status

The retained library builds with pinned Lean/Mathlib 4.35.0. It contains no
`sorry`, `admit`, custom axioms, or `native_decide`. Audited declarations use
only `propext`, `Classical.choice`, and `Quot.sound`.

The main accepted additions are the unconditional operational register lower
bound, the exact cut/increment rank identity,
the zero-increment locus equivalence, and the extended-risk threshold and
strict-memory-gain theorems. See `DECLARATION_MAP.md` for exact scope.

The complete register-realization theorem and the optimization benchmark
theorems remain unfinished in Lean. Work-in-progress files with proof holes
are excluded from this repository. A separate Open Math project retains the
research history. A successful library build does not make the entire paper
formally verified.
