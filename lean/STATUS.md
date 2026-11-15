# Formalization status

The checked library builds at pinned Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`: **9,271 successful build jobs** and
**2,328 audited declarations** (1,990 project and 338 attributed TauCeti declarations).
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the audit.
There are no proof holes, custom axioms, or `native_decide` in retained sources.

The actual register realization theorem, normalization, coordinate bijection,
cut/increment rank identity, executable minor equations, and one-register
characterization are proved. One predetermined machine reproduces all query
points and the terminal output in every finite dimension.

The exact three-step procedure is now executable and proved. It constructs
threshold formulas from a supplied finite loss formula, performs general nonlinear
real quantifier elimination with arbitrary quantifier alternation, isolates the
finite algebraic endpoint or returns an infinite endpoint, decides strict memory
gain, and selects the least sufficient budget. Finite algebraic input coefficients
are encoded and rationalized exactly. No QE, root, endpoint, or minimax oracle is
assumed. Exactness of the supplied loss model is the paper's explicit input
hypothesis, not an input containing an unknown optimum.

The quadratic benchmark is proved for all horizons and budgets, including actual
matrix-gradient trajectories, the exact scalar loss model, Chebyshev lower bound,
and one-register optimal schedule. Its concrete rational input compiler is checked,
and the complete program is proved to return the sharp value, no strict gain,
and least auxiliary memory zero.

The smooth benchmark is proved from actual convex differentiable functions:
necessary and sufficient interpolation, exact Gram loss sets, OGM upper bound,
constructed Drori lower bound for the paper's predetermined linear-history class,
one-register compactness and attainment, conic duality, and GJP uniqueness. Fixed
dimension n≥N+2 has the same loss set as all finite dimensions. Strict memory gain
occurs exactly at m=0,N≥2; there is no gain beyond m=1. Zero and one query are also
covered. The concrete rational smooth input compiler is checked.

Projected rank, singleton memory, convex subgradient interpolation, exact actual
loss sets, operational minimax composition and bounded-oracle finiteness are
proved. The projected symbolic compiler accepts supplied algebraic domain and
slope constraints, binds every trajectory and projection-test variable, and
computes the actual endpoint, strict gain and least sufficient memory. The
explicit norm-ball specialization proves bounded values finite and in [0,MR].
Its register interpretation uses nontrivial domains, exactly as in the report;
singleton loss semantics and the separate one-register theorem are also proved.

The formalization programme is complete for the report's stated results.
Both benchmark algorithms have concrete rational and algebraic inputs and
proved exact outputs. Smooth least memory is zero for N≤1 and one for N≥2.
The generic procedure retains only the report's explicit exact finite-loss-model
input hypothesis; all benchmark and projected compilers discharge it in their
stated settings. No unproved literature result or assumed computational oracle
is used by these final theorems.

The computation has no claimed practical complexity bound. Four closed nonlinear
runtime checks pass. A parameterized quadratic runtime probe was stopped after
more than one minute without a result; its source and status are preserved under
`computations/exploratory/`. Benchmark outputs are proved for every horizon rather
than inferred from large runs of elimination.

The 39 unchanged pre-existing TauCeti files are pinned at
`1c497c347f615b3087cb605f8cf743e591376105`, with original authors, Apache-2.0 license
and source hashes in `third_party/TauCeti`. They provide verified Sturm–Tarski and
sign-determination foundations; the project supplies the executable symbolic
elimination and memory procedure. The report identifies the accepted source checkpoint; its verification section
and the declaration map state the same mathematical scope.

`DECLARATION_MAP.md` records theorem coverage. `FORMALIZATION_PROGRAM.md` retains
the development history and external/local AI provenance.
