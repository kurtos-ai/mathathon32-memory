# Report-to-Lean declaration map

This is a partial formalization. A compiled theorem is claimed only at its actual type.
Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned.

| Report claim | Lean declaration | Coverage and hypotheses |
|---|---|---|
| Section 2, coefficient coordinates | `RealizationCore.coordinateEquiv`, `d_of_W_of`, `T_of_W_of`, `W_of_dT_of` | Actual bijection between strict history matrices and (first subdiagonal, strict increment matrix). Both inverse laws, all horizons, using the paper's finite sums and the accepted `T_of`. |
| Proposition 2.3, coordinate memory fibers | `RealizationCore.realization_iff_coordinates` | For every admissible T and every d, W(d,T) has an m+1-register realization iff T belongs to Q_m. |
| Proposition 2.3, rank identity | `RealizationCore.rank_H_eq_one_add_rank_S` | Exact identity for every finite N and cut k≤N, with the actual consecutive-row increment blocks. Includes empty endpoint cuts. |
| Proposition 2.3, Q₀={0} | `MemoryRank.Incremental.Q_zero_iff` | Exact equivalence on strictly lower triangular T. The triangular hypothesis is explicit. |
| Theorem 2.1, lower bound | `RegisterMachine.Hk_eq_phi_mul_psi`, `necessity_rank_le_unconditional`, `maxCutRank_le_registers` | Actual scalar register recursion initialized at e₁x₀; reproduces every query and terminal output for arbitrary formal inputs. The cut factorization is derived, not assumed. |
| Theorem 2.1, construction and equivalence | `RegisterMachine.realization_iff_rank_all`, `realization_iff_maxCutRank`, `isLeast_registerCount` | Constructs a machine from cut-rank bounds using the canonical cut ranges, finite-basis embeddings and proved left inverses. The top-level theorem assumes only the cut-rank bounds. The maximum cut rank is proved to be the least operational register count. Includes N=0 and s=0. |
| Theorem 2.1, all finite dimensions | `RegisterMachine.vectorRealizes_iff_scalar`, `vectorRealization_iff_maxCutRank`, `isLeast_vectorRegisterCount` | Direct vector-state recursion and a coordinatewise induction. One predetermined coefficient machine works for every dimension; all query points and the terminal output are reproduced for arbitrary formal vector inputs. |
| Theorem 2.1, dimension bound | `MemoryRank.CutRank.memRank_le` | Bounds the maximum cut rank by 1+floor(N/2), hence bounds the minimum register count by the equivalences above. |
| Proposition 2.3, operational memory locus | `RegisterMachine.realization_iff_incrementLocus`, `one_register_iff_zero_increment` | Actual m+1-register realizability iff all interior increment-block ranks are at most m. One register iff T(W)=0. Endpoint blocks are proved harmless. The rank/minor equivalence itself is not formalized. |
| Theorem 3.1, strict uniform bound | `MemoryDecision.risk_lt_iff_uniform_bound` | Exact equivalence for the EReal supremum of a supplied feasible real loss model, including unbounded loss. |
| Theorem 3.1, projected performance set | `MemoryDecision.mem_performance_iff` | Performance is defined from the loss constraints using ∃d ∃b<γ ∀z, not from unknown minimax values. |
| Theorem 3.1, threshold intersection | `MemoryDecision.threshold_iff_value_lt` | Exact equivalence to an independently defined infimum of risks. No attainment or finite-risk assumption. The memory set is an explicit input. |
| Theorem 3.1, ray and empty cases | `MemoryDecision.thresholds_eq_ray_of_value_eq`, `thresholds_empty_iff_value_top` | Finite value gives the open ray; empty threshold set iff value=+∞. |
| Corollary 3.2 | `MemoryDecision.gain_iff`, `gain_has_rational_witness` | Exact strict-gain criterion, including infinite values, and existence of a rational threshold witness. |
| Risk properties | `MemoryDecision.risk_nonneg`, `value_nonneg`, `value_antitone` | Nonnegativity uses nonempty feasible losses and nonnegative loss; monotonicity uses nested memory sets. |
| Theorem 6.6, final logical implication | `MemoryDecision.strict_separation_of_unique_attainment` | Generic implication from an actual lower bound, unique optimizer, attainment on a restricted set, and exclusion of that optimizer. These hypotheses are not proofs of the benchmark theorems. |
| Section 4, projection support | `Continuation.ProjectedSupport.proj_graph_correct`, `proj_unique`, `piK_of_mem`, `piK_singleton` | Euclidean projection on nonempty closed convex sets: variational graph, uniqueness, fixed points and singleton case. General projected rank theorem remains open. |
| Section 4, correction algebra | `Continuation.ProjectedSupport.weightedSum_initState`, `correction_algebra` | Initial and corrected readouts for the actual register-update expression. Does not yet identify a constructed trajectory with the paper's projected recurrence. |
| Section 4, projected readout recursion | `Continuation.Projected.projQuery_zero`, `projQuery_succ_eq_piK`, `projQuery_mem_K` | For the correction-register recursion, the initial query is x₀ and every subsequent query is the projection of the predicted readout. All queries lie in K when x₀∈K. |
| Section 4, singleton trajectories | `Continuation.Projected.direct_singleton_a`, `proj_singleton_a` | For K={a}, both the paper recurrence and every admissible correction-register machine return a at every query and terminal output. General non-singleton equivalence remains open. |
| Section 6, Gram support | `Continuation.SmoothSupport.gram_identity`, `gram_norm`, `psd_factorization`, `forward_psd` | Finite-dimensional Gram identities, positivity and square factorization. Does not prove smooth-convex interpolation or the minimax theorem. |
| Section 5, residual polynomial algebra | `QuadraticFoundations.pIter_eval_zero`, `pIter_natDegree_le`, `pIter_T_zero_eq_product`, `pN_T_zero_eq_productPoly` | Paper's increment-coordinate polynomial recurrence: normalization, degree ≤ query index, and exact specialization to the product polynomial when T=0. Identification with matrix-gradient trajectories and spectral risk remains open. |
| Section 5, Chebyshev support | `QuadraticFoundations.chebM_degree`, `chebM_eval_cos`, `chebM_eval_neg`, `chebM_eq_X_mul_s`, `comp_neg_X_coeff` | Degree, cosine identity, oddness and divisibility for the actual odd Chebyshev polynomial. The scaled optimal polynomial and alternation/minimax conclusions remain open. |
| Section 6, actual OGM memory upper bound | `SmoothOGM.stateNat_eq`, `ogmMachine_realizes`, `ogmHasRealization`, `ogmVectorRealizes` | Actual two-register update with the paper's horizon-dependent θ sequence. Proves all query and terminal readouts for every formal input, using one machine in every finite dimension. Does not prove the performance bound or exclude one-register realizations. |
| Quadratic helpers | `QuadraticBenchmark.productPoly_eval`, `productPoly_eval_zero` | Evaluation and normalization of ∏(1+dᵢX). No spectral risk identity or optimality claim. |
| Smooth helpers | `SmoothBenchmark.theta_pos`, `theta_ge_one`, `theta_recurrence_standard`, `theta_recurrence_final` | Scalar θ recurrence and bounds. |
| Generic rank-one cut construction | `SmoothBenchmark.factoredT_rank_le_one` | Rank bound for supplied outer-product coefficients; no identification with actual OGM coefficients. |

The report's normalized-register equivalence,
projected-method theorems, exact interpolation models, effective quantifier
elimination/root isolation, quadratic minimax theorem, OGM optimality and
uniqueness, and benchmark attainment arguments are not yet Lean formalized.
Their support is the written proofs and cited literature in the report.
No claim of complete Lean verification of the report is made.

`lean/CheckAxioms.lean` names the declarations included in the axiom audit.
