# Full-paper Lean continuation

The authors requested continuing toward formalization of the whole paper on
November 14, 2026. The verified starting source is repository commit
`712749132ed8ba3e7177a9a6509e2f5a02ad66d4` (Lean source checkpoint
`47198777156ee68f1b1d16b1a443131ad8dbf9a2`).

## Execution record

Open Math OS project: `p-91419caf7bbd45d386338df47ac68c02`.
Coordinator chat: `chat-74fec83d9b`.
Initial Ultramath swarm: `smwhj2c0w`, workers `m1`–`m5`.
Replacement swarms are tracked in the coordinator's `status/full-paper-program.md`; workers that end without completing their targets are replaced.
Coordinator configuration: Kimi K3.1 Pro, maximum reasoning. Execution history
also records turns served by DeepSeek V4.1 Flash.
Worker model: Muse Spark Open, maximum reasoning (Kimi is not available in the
Ultramath worker allowlist).

The exact verified source snapshot was transferred and all 33 extracted files
were checked against the archive. Archive SHA256:
`ee121a2dcec7cff0548a6ad7135f19d5ea71595d76043c4ef8737da4596da1a4`.
The isolated continuation source is `continuation/lean-full-paper` in Open Math OS;
the source gate is open.
New work is isolated from the accepted library. An active worker or a successful
build of helper lemmas does not imply that a paper theorem has been formalized.

| Workstream | Remaining targets |
|---|---|
| Normalization and coefficients | Complete: Proposition 2.2 in all finite dimensions, rank/minor criterion and finite rational polynomial memory loci. |
| Semialgebraic decision procedure | Polynomial formula syntax/semantics, effective real quantifier elimination, termination, root isolation, root extraction and exact minimax decisions. |
| Projected methods | Section 4: projection graph, convex interpolation and exact loss model complete; projected-register rank equivalence and singleton minimum complete; effective decision theorem remains. |
| Convex quadratics | Complete in the quadratic matrix model: competing-polynomial lower bound, root schedule, every operational memory budget's EReal minimax value, threshold ray, and no memory gain. |
| Smooth convex methods | Section 6: interpolation and exact Gram reduction complete; optimum and uniqueness and strict gap remain; one-register attainment complete. |

## Acceptance requirements

- Match the report's actual hypotheses, oracle semantics, all-horizon statements,
  and query points as well as terminal output.
- No proof holes, custom axioms, native_decide, assumed copies of target theorems,
  or definitions equating minimax values to desired formulas.
- A theorem conditional on a supplied algorithm or literature result is recorded
  as conditional until those dependencies are themselves proved.
- Effective computation must not be replaced by noncomputable choice.
- Pin Lean 4.35.0 and Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Compile each completed dependency closure and inspect theorem types and
  `#print axioms`; only propext, Classical.choice, and Quot.sound are accepted.
- Codex independently checks exported milestones locally, updates the declaration
  map, and commits/pushes accepted changes to the private repository.

## Known foundation gap

The initial Mathlib audit found real-closed-field definitions and substantial
Chebyshev/Gram support, but no effective real quantifier-elimination and
algebraic-root-isolation implementation. That part requires further foundational
work; assuming an elimination oracle does not complete Theorem 3.1.

See `DECLARATION_MAP.md` for what is actually verified in the current commit.
This program file records work in progress, not additional theorem coverage.

## Checked continuation milestone

The coefficient-coordinate bijection and both inverse formulas were proved locally.
Projection graph/correction identities and Gram/PSD identities were exported by
the coordinator, inspected, built locally and included in the expanded axiom audit.
These support results do not close the projected or smooth benchmark sections.
The remaining workstreams continue with concrete targets in the coordinator chat.

The next checked batch proves quadratic residual-polynomial normalization, degree
bounds and the T=0 product identity, plus odd-Chebyshev algebra. It also proves
the actual OGM two-register machine for all formal inputs and all finite vector
dimensions. These results do not establish benchmark minimax optimality.
Stalled runs were replaced after inspecting source and transcript timestamps;
checking only a running flag was insufficient.

A further checked component gives concrete rational-polynomial QF syntax and
proves that its one-dimensional frontier consists of algebraic numbers. A local
bridge proves algebraicity of finite minimax values conditional on an exact QF
description of the strict threshold set. Effective QE and root isolation remain
unproved, so this is not a completed algorithmic decision theorem.

## Verified continuation through 30f50e4

The library additionally proves projected readout recursion and singleton
trajectories; the actual OGM realization and exact least register count; the
quadratic polynomial recurrence and matrix residual identity tied to W(d,T);
and rational quantifier-free endpoint algebraicity, with its conditional bridge
to finite minimax values. The accepted build has 9082 jobs and the audit names
135 declarations. These milestones do not establish interpolation exactness,
benchmark optimality, effective elimination, or the projected rank theorem.

## Verified continuation through f5aeb9c

The exact spectral risk formula is proved for the actual linear-oracle trajectory
over all positive finite dimensions, with dimension-one attainment. The scaled
Chebyshev candidate has proved normalization, degree bound and exact weighted
interval maximum. The coordinate-change core and time-dependent normalization
matrices preserve the all-ones state. Full build: 9085 jobs; expanded audit: 219
declarations. Missing quadratic lower-bound optimality and one-register schedule,
and missing normalized trajectory conjugacy, remain explicit.

## Verified rank/minor milestone

The rank/minor criterion is proved constructively by selecting independent actual
rows and columns. A finite family of rational multivariate determinant polynomials
is explicitly defined; its zero locus is proved equivalent to the independently
defined memory rank locus and to actual register realizability. This completes
the algebraic memory constraint, not effective quantifier elimination.

Quadratic lower-bound and real-root schedule work now runs in a separate
coordinator chat `chat-bc32b9d6c2`, actual Ultramath swarm `smwhnh69n`
(Muse Spark Open, maximum reasoning).

## Normalization, convex interpolation, and quadratic schedule

The corrected normalized conjugacy is proved in both directions, including one
coefficient machine for every finite dimension. The finite max-affine envelope
proves exact convex/subgradient interpolation with a subgradient at every point.
The explicit Chebyshev roots, factorization, schedule polynomial, and actual
achieved risk are independently compiled and included in the axiom audit.
The general projected rank theorem, smooth-convex interpolation, effective
elimination, and the quadratic competing-polynomial lower bound remain open
in this retained checkpoint.

## Quadratic minimax completed

The all-horizon alternation lower bound and root schedule compile locally.
`QuadraticOperational` defines risk from actual history losses, restricts to
strict increment coordinates, and connects the memory predicate to operational
register realizability. Its independent EReal minimax value and threshold sets
are computed for every budget; one register attains the value, so extra memory
never helps on this quadratic matrix model.

Remaining workers now cover projected rank and exact loss-set assembly, smooth
interpolation, effective root isolation/elimination, and the smooth benchmark.
The quadratic coordinator `chat-bc32b9d6c2` has moved to actual smooth instances
and one-register attainment. `chat-60ae65a17a` owns OGM performance, the all-method
lower bound, and uniqueness. `chat-74fec83d9b` retains projected/interpolation/
root-isolation coordination.

## Dual interpolation construction

The finite maximum of dual quadratics has proved strong convexity, attained maxima, and exact value and subgradient contacts at the supplied data. Conjugate existence, differentiability, Lipschitz gradient, and the resulting interpolation equivalence remain active targets. Reconstructed exploratory NumPy coordinate probes are retained under `computations/exploratory/`; they are not proof certificates.

The root-isolation support now includes a finite rational partition and a proved cover of every real root, conditional on a supplied positive root bound. This is a cover theorem, not a completed isolation algorithm; root separation and assembly remain active.

## Necessary smooth interpolation and attainment support

The actual gradient assumptions now imply the descent bound and tangent lower
bound, hence the exact necessary THG interpolation inequality. The shared
Euclidean instance type satisfies these inequalities, with zero gradient at its
minimizer. The actual one-register recurrence is continuous in its schedule on
every fixed instance. Product-polynomial coefficient identities are proved.
Coercivity, unconditional risk lower semicontinuity, attainment, interpolation
sufficiency, and the sharp smooth minimax bounds remain separate open targets.

## Oracle execution and forward smooth Gram model

The shared oracle trajectory uses actual recursively generated query points and
is proved unique. Every vector-register realization executes it. A generic
zero-chain induction is proved for arbitrary predetermined history matrices.
The finite N+2-coordinate Gram model now represents every actual smooth loss;
its PSD, radius, interpolation and terminal-loss constraints are all checked.
The converse remains open, pending sufficient interpolation and assembly.

Gram reconstruction in dimension N+2 is now proved. Given an actual smooth
interpolant for the reconstructed data, the converse execution, radius,
minimizer and terminal loss are proved. The remaining interpolation-sufficiency
dependency is explicit; no unconditional loss-set equality is claimed yet.

## Scalar risk, coefficient bounds, and conjugate values

The actual one-register EReal risk now ranges over genuine instances in all positive
finite dimensions. Its lower semicontinuity and scalar-quadratic lower bounds are
proved. A fixed Vandermonde system and Cramer's identity give explicit coefficient
and squared-step bounds from finitely many polynomial samples. Compact sublevels,
attainment, and the bridge to Q0 remain the next obligations.

The actual dual conjugate is finite and has the prescribed values and subgradients.
General differentiability and smooth interpolation sufficiency are separate work.
Rational Bezout data and coefficient bounds now certify root separation, but the
algorithm's full output coverage remains unproved; a previous claim covering only
the unfiltered partition was rejected. No complete root-isolation or QE algorithm
is claimed.

General strong-convex-conjugate regularity is now proved locally: explicit-ball
existence, uniqueness, inverse-strong monotonicity, Lipschitz maximizer map,
convex conjugate value and actual gradient. Applying it to the finite dual
construction and closing the exact Gram model are the next integration steps.

## Exact smooth interpolation and finite loss model

The finite THG inequalities are now proved necessary and sufficient for an actual
convex differentiable L-smooth interpolant, for every nonempty finite data set
and Euclidean dimension. The proof uses the actual finite dual maximum, proved
conjugate regularity and uniqueness at the prescribed gradient contacts.

Every feasible Gram data set is then realized by an actual instance in dimension
N+2, including all intermediate oracle queries and the terminal loss. The finite
model is proved equal to the actual loss set over all positive finite dimensions.
The OGM performance/optimality and uniqueness results and one-register attainment
are still open; exact interpolation is no longer an assumed dependency.

The Q0/step-schedule bridge is now proved for actual trajectories, losses and
all-dimensional EReal risks. The operational one-register minimax value is
exactly the infimum over step schedules, and the actual performance condition
is exactly the finite Gram test. This closes the semantic bridge needed by
the independent compactness/attainment proof.

## Actual one-register attainment

For every horizon and L,R>0, actual risk sublevels are proved compact, an
optimal schedule is attained, and the Q0 bridge gives a genuinely realizable
one-register coefficient map attaining the operational minimax value. The
value is finite and nonnegative. Smooth benchmark optimality and uniqueness
remain open, so the strict memory gap is not yet fully formalized.

## Exact projected loss models

Both the arbitrary-subgradient and norm-bounded oracle variants now have exact
finite loss models on every fixed nonempty closed convex K. The proof constructs
the actual finite envelope, its minimizer and permitted subgradients everywhere,
and proves all intermediate projected iterates agree with the feasible data.
Actual executions produce the same finite inequalities, including an auxiliary
terminal subgradient. The zero-increment loss bound MR is proved for the bounded
variant. Projected register rank and effective elimination remain separate.

## Projected lower bound and simple-root refinement

Root independently proved the general projected register lower bound by
segment perturbations and scalarization, including all causal query points.
The upper-bound worker retains ownership of the quotient-state construction.
Export14 supplied the simple-root sign and actual filtered-grid refinement
lemmas; fixed-grid examples were omitted and names now distinguish sign-changing
cells from intervals with certified unique roots. Effective separation-based
coverage remains the next isolation target.

## OGM energy certificate

Root proved the fixed-horizon prefix identity, its terminal specialization,
and the objective inequality with general-L scaling. The OGM worker owns the
remaining coefficient/vector recurrence, theta identities, and actual-instance
instantiation. The performance theorem remains open until these are connected.

## Complete projected realization theorem

Root completed the vector construction, full projected-state invariant,
nontrivial-domain rank equivalence and singleton minimum. The scalar-only
worker attempts are superseded and their duplicate lanes should be closed.
Effective projected quantifier elimination remains part of the general QE task.

## Squarefree preprocessing and certified coverage

Exports15–16 are locally compiled and fully audited. The quotient by gcd has exactly the original real roots, all simple. Given certified rational bounds and separation, the finite filtered grid with mesh half the separation covers every root. This does not yet compute the certificates or prove complete effective isolation/QE. The duplicate projected workers have been stopped because the full projected register theorem is now accepted.

## Rational root bound and simplex minimization

The rational coefficient bound is explicitly computed and verified locally. The exact exported GJP Lemma 3.1 source (SHA-256 0d8de45e724861b56ede320a7ae9c1d058e0edf26734f3b14a10ae3f189ec762) builds locally with all 37 declarations audited. This closes simplex minimization and equality uniqueness, not matrix elimination or actual OGM coefficient uniqueness.

## Conditional isolator

Coverage now states the concrete half-separation mesh. Soundness proves exactly one root in each filtered cell; squarefree equivalence transfers both properties to the original polynomial. The remaining executable work must replace/refine Mathlib noncomputable division/gcd; a syntactic ordinary `def` inside a noncomputable section is not evidence of code generation.

## Actual OGM bound and constructed univariate certificates

Root proved the actual OGM upper bound via vector Y/Eta/Z/V recurrences, actual oracle evaluation, smooth interpolation residuals, and the verified energy identity. It includes every horizon and finite dimension. The accepted Drori finite hard-data prefix and normalized coefficient recurrence are integrated. Export17 completes construction of the mathematical univariate isolation certificates and proves coverage, unique cells and disjointness. Executable division/gcd and QE, the Drori actual hard-function lower bound and full GJP coefficient uniqueness remain active obligations.

## Operational OGM bound

The actual trajectory upper bound is now connected to the independent EReal risk and minimax definitions via the coefficient-coordinate equivalence and proved operational memory characterization. This proves the upper bound at every m≥1 and, for N=1, already at m=0. Drori lower bounds, full GJP coefficient uniqueness, and executable elimination remain unfinished.

## Local continuation after external quota exhaustion

On Nov15 around12:45UTC, Open Math OS's provider key reached its weekly limit; Kimi and the Muse fallback both returned HTTP429, with reset Nov21 06:43:56UTC. Existing remote sources remain preserved. Three local Codex agents continue Drori's lower bound, GJP uniqueness, and executable arithmetic/elimination. Root reviews, builds, audits, and integrates their completed modules.

The constrained-conjugate helper and actual Drori instance are verified, including interpolation, exact radius and prefix-space lower bounds. The zero-chain is still under development. GJP Lemma3.3 now has the true bordered-matrix equivalence, singular completion, and tight nonsingular uniqueness; full actual-risk coefficient uniqueness remains open.

## Sharp smooth benchmark and executable isolation

The full actual Drori lower-bound chain now compiles and passes the global axiom audit, including a genuine zero-chain proved by dual tail-candidate comparison and constrained-maximizer uniqueness. Combined with OGM, the independent operational value, threshold ray and absence of gains beyond m=1 are proved. The N=1,m=0 endpoint is included. The GJP factor-to-simplex projection is also integrated.

The executable coefficient-list polynomial layer refines Mathlib operations for all inputs, including zero divisors, and the complete executable rational isolator refines the proved certificate. Coverage, uniqueness, disjointness and exact zero-polynomial detection are proved; fourteen guarded runtime checks pass. General nonlinear QE and full actual-risk coefficient uniqueness remain active obligations.

## Local continuation: factor stability and symbolic affine elimination

Accepted batch: 19 modules, 9,168 successful build jobs, 1,300 audited declarations.
The new proofs cover singular TC factorization, exact optimal factors, convergence
of approaching certificates and their limiting feasibility, compact-certificate
uniqueness, actual-instance scaling, and the zero-query smooth benchmark.
Executable affine elimination with polynomial parameters and exact algebraic
root zero/sign tests are also checked.

Remaining programme: connect actual smooth risk to approaching compact dual
certificates, conclude actual coefficient uniqueness and the strict N≥2 memory
gap, and finish general multivariate nonlinear quantifier elimination. Local
agents continue these tasks; the external Open Math provider remains quota-blocked.

## Actual smooth uniqueness and complete memory classification

Accepted batch: 15 modules, 9,183 successful build jobs, 1,431 audited declarations.
Actual-risk duality is proved by separation and Gram realization, and the
approaching-certificate theorem closes the actual coefficient-uniqueness proof.
The operational strict-gain and threshold-gain classifications now hold exactly
when m=0 and N≥2. No abstract duality or uniqueness assumption remains.
Arbitrary-degree univariate existential/universal Boolean decision is executable
and proved correct. The final coverage audit continues for general nonlinear QE,
algebraic coefficient rationalization, endpoint/minimax output composition,
fixed-dimension realization, and quadratic/projected operational wrappers.

## Fixed dimensions, finite models, and verified external foundations

Accepted batch: five project modules (40 declarations), 38 unchanged TauCeti
modules (337 audited public declarations), 9,227 build jobs and 1,808 audits.
Fixed-dimension smooth uniqueness, exact quadratic loss-set equality, and
projected operational minimax/ray composition now cover the identified
noncomputational benchmark gaps. TauCeti attribution, pin, license and hashes
are retained under third_party/TauCeti; this is pre-existing work.
General effective QE and exact minimax-output composition continue.

## Algebraic inputs, symbolic remainder chains, and exact endpoints

Accepted batch: 20 project modules, 204 project declarations and one additional
unchanged TauCeti instance file. Verification: 9,248 successful build jobs and
2,013 audited declarations, including 338 external declarations. Algebraic
constant rationalization and literal first-order reduction, exact executable
endpoint selection, determinant/minor syntax, and symbolic Tarski-query
foundations are verified. Full Boolean nonlinear elimination and the final
loss-model-to-minimax pipeline are still being assembled. Conditional composition
lemmas explicitly retain the central QE step premise until it is discharged.
