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
| Normalization and coefficients | Proposition 2.2; rank/minor criterion and algebraic memory loci. |
| Semialgebraic decision procedure | Polynomial formula syntax/semantics, effective real quantifier elimination, termination, root isolation, root extraction and exact minimax decisions. |
| Projected methods | Section 4: projected-register rank theorem, projection graph, convex interpolation, exact loss model and decision theorem. |
| Convex quadratics | Section 5: spectral risk formula, Chebyshev construction and lower bound, all-horizon minimax and one-register optimality. |
| Smooth convex methods | Section 6: interpolation and Gram reduction, optimum and uniqueness, one-register attainment and strict gap. |

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
