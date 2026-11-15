# Formalization status

The retained library builds with pinned Lean/Mathlib 4.35.0. Current verification:
9,248 successful build jobs and 2,013 audited declarations
(1,675 project declarations and 338 public declarations from the attributed
TauCeti dependency). Audited declarations
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

The quadratic benchmark is complete: exact equality with the scalar two-variable
loss model, actual matrix oracle trajectories, residual
polynomials, spectral risk, Chebyshev alternation, explicit root schedules, and
the exact minimax value at every operational memory budget. Additional memory
never improves that value.

The projected setting is verified: closed-convex projection and every query,
finite convex subgradient interpolation and exact finite loss models, including
repeated queries and bounded/unbounded subgradient returns. The minimum register
count is the ordinary maximum cut rank on every nontrivial closed convex set,
including empty-interior sets, and one on a nonempty singleton. Operational
projected minimax values equal the register-constrained infima, with exact
threshold rays, saturated budgets and rational gain witnesses. For bounded
subgradients the values lie in [0,MR] at every budget.

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
scaling are also proved. The actual-risk duality bridge is now proved from finite-dimensional convex
separation and positive-functional Gram realization. It supplies arbitrarily
close compact certificates from actual oracle bounds, with no Slater,
interpolation, or duality assumption. Actual optimal coefficient maps are exactly
OGM. For every horizon and budget, increasing auxiliary memory m to m+1 strictly
improves minimax performance exactly when m=0 and N≥2. The equivalent threshold
set criterion is also proved. These are statements about independently defined
all-dimensional operational risk, not just certificate optimization. Zero-padding
and actual interpolation identify the same loss set in every fixed dimension
n≥N+2 and prove the fixed-dimension uniqueness theorem as stated in the paper.

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
result is not general multivariate nonlinear QE. A complete executable decision
procedure now handles arbitrary-degree Boolean formulas with one quantified real
variable and rational coefficients, for both existential and universal
quantifiers. Root-free regions have certified rational representatives; exact
algebraic signs handle roots. Five guarded runs check satisfiable, unsatisfiable,
universal and constant cases.

Algebraic input constants now have certified minimal-polynomial/root-cell codes.
Their exact rationalization preserves arbitrary first-order quantifier alternation.
Exact endpoint selection from rational threshold formulas is executable and proved,
including infinite endpoints. Composition through a supplied correct rational QE
step yields the independently defined minimax value. The general parameterized
nonlinear QE step remains unfinished; no assumed step is presented as complete.
Executable determinant/minor formulas now characterize actual register memory.
Finite sign branching, positive symbolic pseudo-division, signed remainder chains,
infinity signs, and symbolic Tarski queries are implemented and proved under every
real coefficient specialization, including zero and degree-drop cases.
The targeted Sturm–Tarski/sign-determination
foundation from TauCeti is retained unchanged under Apache-2.0 at revision
1c497c347f615b3087cb605f8cf743e591376105. All 39 vendored files build against the
project pin; source hashes, authors and license are under third_party/TauCeti.
These are pre-existing library results and do not by themselves provide the
remaining executable parameterized elimination.

The report is still partially formalized. Only checked modules enter the tracked
library. External Open Math work is preserved; local Codex agents continue after
the external provider quota was exhausted. `DECLARATION_MAP.md` records exact
scope and `FORMALIZATION_PROGRAM.md` retains the development history.
