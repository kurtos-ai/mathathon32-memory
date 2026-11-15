# Formalization status

The retained library builds with pinned Lean/Mathlib 4.35.0. It contains no
`sorry`, `admit`, custom axioms, or `native_decide`. Audited declarations use
only `propext`, `Classical.choice`, and `Quot.sound`.

The library proves the operational register-realization theorem in both
directions, including one coefficient machine valid in every finite dimension.
The upper bound constructs actual states and updates; the lower bound derives
the cut factorization from formal-input correctness. It also proves the exact
cut/increment rank identity, the operational rank-form memory locus and its finite rational determinant equations,
the one-register/zero-increment equivalence, and the extended-risk threshold and
strict-memory-gain theorems. The coefficient-coordinate bijection, its operational
memory fibers, projection/Gram support, quadratic polynomial recurrence and
Chebyshev algebra and the scaled candidate's exact weighted maximum, the matrix residual identity and spectral risk maximum tied to the history-map trajectory, the actual OGM realization and exact one/two-register count, and algebraicity of
rational quantifier-free endpoints are also proved. See `DECLARATION_MAP.md` for exact scope.

Normalized-register equivalence in every finite dimension, finite convex subgradient interpolation, and the actual Chebyshev root schedule are now proved. The quadratic matrix-model minimax value, exact threshold ray, and absence of gains are proved at every operational register budget, using the independent EReal risk/value definitions.

General projected rank and loss-set equivalences, smooth-convex interpolation, effective
quantifier elimination and the smooth-convex optimization benchmark proofs remain unfinished
in Lean. Work-in-progress files with proof holes
are excluded from this repository. A separate Open Math project retains the
research history. A successful library build does not make the entire paper
formally verified.
