# Formalization status

The retained library builds with pinned Lean/Mathlib 4.35.0. Current verification:
9,168 successful build jobs and 1,300 audited declarations. Audited declarations
use only `propext`, `Classical.choice`, and `Quot.sound`; retained sources contain
no proof holes, custom axioms, or `native_decide`.

The operational register-realization theorem is proved in both directions,
including one predetermined coefficient machine valid in every finite dimension.
The coefficient-coordinate bijection, cut/increment rank identity, finite rational
determinant equations for memory, normalized realization theorem, and exact
one-register characterization are proved from the actual recursion.

The independent extended-real risk/value definitions satisfy the strict-threshold
and memory-gain criteria, including infinite values without attainment assumptions.
Rational quantifier-free threshold endpoints are proved algebraic. General
quantifier elimination, which must produce those formulas, remains unfinished.

The quadratic benchmark is complete: actual matrix oracle trajectories, residual
polynomials, spectral risk, Chebyshev alternation, explicit root schedules, and
the exact minimax value at every operational memory budget. Additional memory
never improves that value.

The projected setting is verified: closed-convex projection and every query,
finite convex subgradient interpolation and exact finite loss models, including
repeated queries and bounded/unbounded subgradient returns. The minimum register
count is the ordinary maximum cut rank on every nontrivial closed convex set,
including empty-interior sets, and one on a nonempty singleton.

For smooth convex functions, necessary and sufficient interpolation, exact finite
Gram loss models, and all-dimensional oracle realization are proved. The actual
one-register risk is lower semicontinuous, has compact sublevels, and attains its
infimum. OGM has its proved implementation and exact one/two-register count.

The sharp smooth-convex minimax value is proved for every positive query horizon
and every auxiliary memory budget m≥1. The upper bound uses the actual OGM oracle
trajectory. The lower bound uses an actual orthant-conjugate Drori function with
proved gradient, minimizer radius, zero-chain property, and loss lower bound for
every history matrix. Exact threshold rays and no gain beyond m=1 follow from
the independent operational risk/value definitions. For one query the exact
value LR²/8 is proved already at m=0 and hence at every memory budget.
At zero queries the exact value LR²/2 and threshold ray hold for every budget;
the sharp formula at m≥1 therefore covers every nonnegative horizon.

The GJP simplex problem is proved, including its unique equality case. Matrix
elimination starts from the actual bordered PSD condition, treats singular
triangular completion, and proves tight nonsingular uniqueness. Projection of
admissible factors onto the simplex and its lower-rate implication are proved.
The full admissible TC factorization is proved, including singular pivots.
Optimal factors and the method certified by them are unique. Approaching optimal
certificates converge to those factors, and closed feasibility supplies the
limiting certificate. The coefficient normalization and actual smooth-instance
scaling are also proved. Full coefficient uniqueness for actual oracle risk still
requires the risk-to-certificate duality bridge. Consequently the strict gap from
m=0 to m=1 at horizons N≥2 remains outside the accepted Lean result.

Rational root isolation is now executable and certified. Coefficient-list
arithmetic, division, gcd, Bezout coefficients, derivative and evaluation refine
Mathlib polynomial operations. The computed squarefree polynomial, rational
bounds and separation grid produce a finite list covering every real root,
exactly one original-polynomial root per cell, and disjoint distinct cells.
The zero polynomial is detected separately. Fourteen guarded execution checks
exercise arithmetic and isolation. Exact zero and sign tests at represented
algebraic roots are proved and execute in six further guarded checks.

Executable symbolic elimination is proved for arbitrary Boolean combinations
affine in the eliminated variable, with rational polynomial parameter
coefficients. It handles strict and weak inequalities, equality, negation and
coefficient sign changes. Four guarded execution checks pass. This restricted
result is not general multivariate nonlinear QE, which remains unfinished.

The report is still partially formalized. Only checked modules enter the tracked
library. External Open Math work is preserved; local Codex agents continue after
the external provider quota was exhausted. `DECLARATION_MAP.md` records exact
scope and `FORMALIZATION_PROGRAM.md` retains the development history.
