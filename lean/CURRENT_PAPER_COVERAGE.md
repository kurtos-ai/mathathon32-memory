# Current revised-paper coverage audit

Authoritative source: `outputs/memory-report-revised/report.tex`, SHA-256
`425060623672d39d1d6c7c1c5bcb7053109f11d489e124af582400de3cb1c525`. The table distinguishes complete claims from checked ingredients.

The formalization does **not** cover the whole revised paper. In particular,
objective-error optimality on smooth convex functions does not imply terminal-gradient
optimality under an initial function-gap bound, and the zero-versus-one auxiliary
register gap does not imply the new one-versus-two auxiliary register separation.

| Current claim | Checked coverage | Missing mathematical content |
|---|---|---|
| Sections 2–3: exact memory and decision procedure | Extensive checked support; see `DECLARATION_MAP.md`, `RegisterMachine.vectorRealization_iff_maxCutRank`, `RealizationCore.realization_iff_coordinates`, `EffectiveProcedure.methodEndpoint_correct` | A new application must supply and prove its exact finite loss-model premise; concrete benchmark compilers discharge it. |
| Section 3.3 parameterized-gap expansion | Uniform symbolic QE handles polynomial parameters, but there is no semialgebraic growth/Puiseux theorem. | A finite-valued parameterized value-function graph theorem and the rational-exponent asymptotic expansion; O(ε) alone does not supply them. |
| Section 4 quadratic and smooth-convex objective-error benchmarks | Actual trajectories, exact loss sets, sharp values, coefficient uniqueness and strict gain classification are checked. | These do not establish the Section 5 stationarity benchmark. |
| Appendix D ITEM-wf memory | `Submission2026.StrongConvexMemory.item_history_trajectory`, `item_vectorRealizes`, and `item_executes_oracle` identify the displayed schedule with an actual two-register recurrence, uniformly over finite dimensions. | The selected risk-root existence/uniqueness, parameter regularity and cited minimax optimality are not proved. |
| Appendix E Lemniscate memory | `LemniscateMemory.coefficients_entry`, `cut_rank_le_one`, `machine_vectorRealizes`, and `machine_executes_oracle` prove the displayed coefficient calculation and explicit two-register implementation. | Calibrated parameter existence/uniqueness and the cited minimax value/optimality are not proved. |
| Section 5, `w:thm:weak`: all-horizon terminal-gradient minimax for q∈[-1,0] | Existing actual interpolation/conic machinery is for the earlier convex objective-error model. No weak-curvature stationarity theorem is present. | Exact nonconvex gap-based PEP; triangular completion; terminal/simplex projections; scalar root existence/uniqueness; lower bound; actual attaining recurrence; strict horizon decrease and asymptotic limit. |
| Section 5 positive-curvature upper bound (`ext:prop:positive`) | No matching initial-gap stationarity result. | Root-domain analysis, certificate identity, two-register guarantee, exact one-query result and stated uniform lower bounds. |
| Section 6 total-step extremal theorem (`s:thm:extremal`) | `GJP.exists_TC_admissible`/factorization and actual conic duality are reusable only as ingredients. | Forward-multiplier projection; path optimization; weighted-Laplacian dual certificate; four-term residual identity; equality/limiting uniqueness for the total-step problem. |
| Section 6 second auxiliary vector (`s:thm:sep`) | `ExtremalMemory.vector_memory_exact` proves exactly three persistent registers for the explicit N=4 coefficient family under `PathConditions4` (positive normalized path data, diagonal slack and adjacent stationarity). The actual recurrence and determinant identity are proved. `GJP.operational_strict_gain_iff` concerns m=0 versus m=1 on the full convex smooth class. | Existence/calibration and optimality of the path satisfying those hypotheses; hinge actual instances; exact rational interval certificates; coefficient a priori bounds; compact one-auxiliary attainment; union minimax equality and uniqueness. The conditional memory theorem does not establish this separation. |
| Section 6 common finite smoothness (`s:cor:smooth-union`) | No theorem for hinge-union truncation. | Quantitative hinge truncation error and compactness gap argument with a common positive width. The paper itself asserts existence, not a numeric truncated gap or truncated uniqueness. |
| Section 7 pointwise rigidity (`ext:thm:rigidity`) | `ResidualRigidity.residual_eq_of_scalar_quadratic_domination` proves terminal-polynomial equality from distinct positive-root scalar loss tests; `terminal_eq_of_scalar_quadratic_domination` gives matching terminal points on all matrix quadratics. Smooth minimax uniqueness is a different assertion. | The localized smooth perturbation and recovery of every intermediate query row; near-OGM examples. Terminal-polynomial equality alone does not imply coefficient-map equality. |
| Section 7 quadratic replacement (`ext:prop:compile`) | `QuadraticReplacement.exists_one_register_pointwise_replacement` and `QuadraticReplacement.exists_two_register_exact_replacement` prove both assertions for every horizon and dimension: one persistent register pointwise dominates the terminal objective on every PSD quadratic, and two persistent registers reproduce the terminal error on every real matrix quadratic. | This proposition is fully covered in the coefficient/actual matrix-trajectory model. The domination proof uses real parts of complex normalized factors; exact reproduction uses real degree-one/two factors, zero padding, and strict-subdiagonal cut-rank bounds. |
| Section 7 near-quadratic gap (`ext:thm:near`) | No perturbation-transport theorem. | Explicit trajectory constants and dimension-independent O(ε) value comparison for the stated perturbed class. |
| Section 7 fixed-prefix comparison (`ext:rem:prefix`) | General memory-minor criteria are reusable. | Actual specified prefix, terminal-design lower witness, explicit upper method, and exact 1/50 < 51/2000 bound. |

## Verification policy

A new lemma counts only for its exact Lean type. Algebraic identities, numerical
certificates, or conditional assembly theorems will be recorded as ingredients and
will not be described as proofs of the full new minimax results. Source scans are
supplemented by the Lean build and axiom dependency audit.
