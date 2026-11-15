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
| Projected methods | Section 4: projected-register rank theorem, projection graph, convex interpolation, exact loss model and decision theorem. |
| Convex quadratics | Complete in the quadratic matrix model: competing-polynomial lower bound, root schedule, every operational memory budget's EReal minimax value, threshold ray, and no memory gain. |
| Smooth convex methods | Section 6: interpolation and exact Gram reduction complete; optimum and uniqueness, one-register attainment and strict gap remain. |

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
