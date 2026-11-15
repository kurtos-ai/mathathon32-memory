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

Effective quantifier
elimination, executable root isolation, and smooth-convex benchmark optimality,
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

Current verification: 9,137 successful build jobs and 956 audited declarations.
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
domains with empty ambient interior. The matching construction and the singleton minimum are now proved.

Simple roots are proved to enter the actual rational sign-filtered grid output
for every sufficiently small positive mesh. This is a refinement theorem with
an existential mesh threshold, not complete effective root isolation.

The fixed-horizon algebraic energy identity and its general-L objective bound
are proved. The actual OGM vector recurrences and oracle trajectory now instantiate this
certificate, proving the terminal bound L R²/(2 theta_N²) for every horizon
and actual finite-dimensional smooth-convex instance.

The projected realization theorem is now complete in every finite-dimensional
real inner-product space: the least register count is the ordinary maximum
cut rank on a nontrivial closed convex domain, and one on a nonempty singleton.
The construction proves the entire actual projected trajectory and uses one
predetermined scalar coefficient machine across all dimensions.

Squarefree preprocessing preserves every real root and gives nonzero derivative at each root. Given certified rational root and separation bounds, every simple root lies in the actual filtered grid output with mesh equal to half the separation. The later certificate construction supplies these bounds; executable isolation and QE remain separate obligations.

An explicit rational Cauchy bound is computed from the coefficients and proved to bound all real roots. The GJP simplex minimization lemma is proved, including attainment and unique equality coordinates for every horizon. Connecting this lemma through the matrix elimination to actual OGM coefficient uniqueness remains open.

The conditional isolator now uses the explicit half-separation mesh and proves coverage of every original root and exactly one original root per returned cell. Its squarefree preprocessing depends on Mathlib noncomputable polynomial division/gcd; an executable refinement remains open.

The rational univariate isolation specification now constructs its own Bezout, root, coefficient, curvature and separation certificates from every nonzero input polynomial. It proves root coverage, unique cells and disjointness; executable polynomial arithmetic and multivariate QE remain open.

Drori finite hard-data formulas, positivity and strict decrease and the exact terminal datum are verified (not the hard interpolant/lower bound). The separate normalized OGM weighted-coefficient recurrence includes the predecessor-diagonal correction and final theta step.

The actual OGM upper bound is connected to the independently defined operational risk and minimax value, at every auxiliary memory budget m≥1. For one query, it holds already at m=0 with bound LR²/8.

The actual orthant-constrained Drori hard function now exists as a smooth-convex radius-R instance, with every prescribed value/gradient, the minimizer, and lower bounds on prefix subspaces. The zero-chain and all-method minimax lower bound remain unfinished. GJP Lemma3.3 is proved from the actual bordered PSD matrix, including singular triangular completion and tight nonsingular uniqueness; full coefficient uniqueness remains unfinished.
