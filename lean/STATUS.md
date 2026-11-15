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

Necessary and sufficient finite smooth-convex interpolation is proved from actual gradient, convexity and Lipschitz definitions. The finite dual construction has a proved everywhere-defined conjugate gradient, with existence, uniqueness and the exact Lipschitz bound. Fixed-instance one-register trajectories and losses are continuous in the schedule. The actual all-dimensional EReal risk is lower semicontinuous, with proved scalar-quadratic lower bounds and explicit coefficient and squared-step bounds.

The projected rank upper bound, effective quantifier
elimination and complete root isolation, and smooth-convex benchmark optimality,
and uniqueness remain unfinished
in Lean. Work-in-progress files with proof holes
are excluded from this repository. A separate Open Math project retains the
research history. A successful library build does not make the entire paper
formally verified.

The causal exact-oracle trajectory, its uniqueness and register-execution bridge,
and the generic zero-chain induction are proved. The finite smooth Gram formula
is explicitly defined and proved equal to the actual all-dimensional loss set.
Every feasible datum is realized in dimension N+2, with all causal queries and
the terminal loss preserved. This includes zero-query horizons.

Current verification: 9,119 successful build jobs and 675 audited declarations.
The written report remains only partially formalized.

Zero-increment history methods and step schedules now have proved identical
actual trajectories and EReal risks, including the operational minimax infimum.

Actual risk sublevels are compact for L,R>0, and an optimal one-register
coefficient map is proved to exist with its operational realization. The
finite/nonnegative value bounds are also proved.

Projected finite loss-set exactness is now proved for unbounded and norm-bounded
subgradient oracles, including repeated queries with distinct returns and the
complete projection recurrence. The bounded zero-increment loss is at most MR.

For every nontrivial closed convex domain, projected formal-input correctness
implies an ordinary scalar realization with the same registers. Thus the
projected cut-rank and maximum-rank lower bounds are now proved, including
domains with empty ambient interior. The matching construction remains open.

Simple roots are proved to enter the actual rational sign-filtered grid output
for every sufficiently small positive mesh. This is a refinement theorem with
an existential mesh threshold, not complete effective root isolation.

The fixed-horizon algebraic energy identity and its general-L objective bound
are proved. Applying this certificate to the actual OGM coefficients and
oracle trajectory remains separate from the generic certificate.
