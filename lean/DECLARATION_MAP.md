# Principal checked declarations

The method class has predetermined real scalar coefficients. The entries below
state the proved scope; `CURRENT_PAPER_COVERAGE.md` lists remaining claims.

| Topic | Principal declarations | Scope |
|---|---|---|
| Exact register count | `RegisterMachine.vectorRealization_iff_maxCutRank`, `RegisterMachine.isLeast_vectorRegisterCount` | A single machine works in every finite dimension; upper construction and lower bound. |
| Coordinates and memory | `RealizationCore.coordinateEquiv`, `RealizationCore.rank_H_eq_one_add_rank_S`, `RealizationCore.realization_iff_coordinates` | Exact coefficient bijection and increment-cut characterization. |
| Executable memory formula | `MemorySemialgebraic.SymbolicQE.flatMemoryFormula_realization` | Finite rational determinant syntax exactly describes register eligibility. |
| Extended-real thresholds | `MemoryDecision.threshold_iff_value_lt`, `MemoryDecision.gain_iff` | Strict minimax comparisons, including infinite risk and without attainment. |
| Real quantifier elimination | `MemorySemialgebraic.SymbolicQE.FirstOrder.quantifierEliminate_correct` | Executable general nonlinear real QE with arbitrary quantifier alternation; no QE oracle. |
| Endpoint and memory algorithms | `MemorySemialgebraic.EffectiveProcedure.methodEndpoint_correct`, `MemorySemialgebraic.EffectiveProcedure.leastSufficientMemory_correct`, `MemorySemialgebraic.EffectiveProcedure.algebraicMethodEndpoint_correct` | Exact finite algebraic or infinite output; retains an explicit exact finite-loss-description input hypothesis. No practical complexity bound. |
| Projected register model | `Continuation.Projected.projected_realization_iff_rank`, `Continuation.Projected.subsingleton_least_registers` | Nontrivial closed convex domains, with singleton case separated. |
| Projected actual losses | `ProjectedLossModel.lossSet_eq`, `MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.lossFormula_correct`, `ProjectedOperational.bounded_value_finite` | Exact supplied domain/slope formulas; finite bound in the bounded-slope case. |
| Quadratic actual losses | `QuadraticSpectral.historyLossSet_eq_scalarLossSet` | Full scalar loss-set equality for actual matrix-gradient trajectories. |
| Quadratic minimax | `QuadraticOperational.value_eq`, `QuadraticOperational.no_memory_gain`, `MemorySemialgebraic.QuadraticProcedure.leastSufficientMemory_zero` | Sharp all-horizon value, equality at every memory budget, and computed least budget zero. |
| Smooth actual losses | `SmoothGramModel.actualLossSet_eq_modelLossSet`, `SmoothGramModel.actualLossSet_eq_fixed_dimension` | Actual smooth-convex interpolation and every fixed dimension n≥N+2. |
| Smooth sharp bounds | `OGMVerified.actual_upper_bound`, `SmoothDrori.hardInstance_all_linear_history_lower`, `SmoothDrori.operational_value_eq_all_queries` | Matching actual-function objective-error bounds for predetermined linear-history methods. |
| Smooth uniqueness and attainment | `GJP.actual_method_unique`, `SmoothOperational.exists_optimal_one_register` | Actual-risk coefficient uniqueness and one-register attainment. |
| Smooth strict gain | `GJP.operational_strict_gain_iff`, `MemorySemialgebraic.SmoothProcedure.leastSufficientMemory_correct` | Strict gain exactly at m=0,N≥2; computed least auxiliary memory zero for N≤1 and one otherwise. |
| Algebraic concrete inputs | `MemorySemialgebraic.SmoothAlgebraicInput.input_correct`, `MemorySemialgebraic.QuadraticAlgebraicProcedure.endpoint_correct` | Discharges the exact finite-input premise for the stated algebraic benchmark parameters. |
| ITEM-wf register implementation | `Submission2026.StrongConvexMemory.item_history_trajectory`, `Submission2026.StrongConvexMemory.item_vectorRealizes`, `Submission2026.StrongConvexMemory.item_executes_oracle` | Displayed backward schedule and actual two-register recurrence in every dimension. Does not prove risk-root calibration or cited minimax optimality. |
| Lemniscate register implementation | `LemniscateMemory.coefficients_entry`, `LemniscateMemory.cut_rank_le_one`, `LemniscateMemory.machine_vectorRealizes`, `LemniscateMemory.machine_executes_oracle` | Actual displayed coefficient formula, separable row differences and explicit two-register machine. Does not prove parameter calibration or cited optimum. |
| Quadratic replacements | `QuadraticReplacement.exists_one_register_pointwise_replacement`, `QuadraticReplacement.exists_two_register_exact_replacement` | Both quadratic-replacement assertions: one-register pointwise objective domination and two-register exact terminal reproduction, with exactly the given call budget. |
| Four-query extremal memory | `ExtremalMemory.omegaEntry_recurrence`, `ExtremalMemory.determinant4_neg`, `ExtremalMemory.vector_memory_exact` | Actual recurrence and exact three-register count under positive normalized path, slack and stationarity conditions. Does not prove existence/calibration or optimality of those parameters, or the union-class separation. |
| Residual rigidity | `ResidualRigidity.residual_eq_of_scalar_quadratic_domination`, `ResidualRigidity.terminal_eq_of_scalar_quadratic_domination` | Distinct positive-root scalar tests force terminal-polynomial equality, including fewer competing calls. Does not recover intermediate query rows or prove full smooth pointwise rigidity. |

The attributed TauCeti source provides verified Sturm–Tarski and sign-determination
foundations; its revision, authors, license and hashes are in `third_party/TauCeti`.
All listed declarations are checked by `CheckAxioms.lean` using only the standard
axioms documented in `AXIOM_AUDIT.md`.
