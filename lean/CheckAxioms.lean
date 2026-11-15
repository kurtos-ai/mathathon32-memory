module
public import Continuation
public import Decision
public import Benchmarks
public import MemoryRank
public import RealizationCore
public import Submission2026

public import TauCeti.Algebra.BigOperators.Finset.Filter
public import TauCeti.Algebra.Polynomial.Eval.Sign
public import TauCeti.Algebra.Polynomial.LinearFactor
public import TauCeti.Algebra.Polynomial.Rolle
public import TauCeti.Algebra.Polynomial.Thom
public import TauCeti.Algebra.Polynomial.Eval.OneSided
public import TauCeti.FieldTheory.RealClosure.FiniteExtension
public import TauCeti.FieldTheory.RealClosure.Galois
public import TauCeti.Algebra.Order.Ring.Ordering.Extension
public import TauCeti.Algebra.Order.Ring.Ordering.Semireal
public import TauCeti.FieldTheory.RealClosure.Complexification
public import TauCeti.FieldTheory.RealClosure.AlgebraicClosed
public import TauCeti.Algebra.QuadraticDiscriminant
public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
public import TauCeti.Algebra.Polynomial.RealClosed.Quadratic
public import TauCeti.FieldTheory.RealClosure.IVT
public import TauCeti.Data.Finset.Jumps
public import TauCeti.Algebra.Polynomial.RealClosed.Sign
public import TauCeti.Data.List.SignVariations
public import TauCeti.Algebra.Polynomial.Sturm.Signs
public import TauCeti.Algebra.Polynomial.Sturm.Local
public import TauCeti.Algebra.Polynomial.Sturm.Sequence
public import TauCeti.Algebra.Polynomial.Sturm.SignedRemainders
public import TauCeti.Algebra.Polynomial.Sturm.Sum
public import TauCeti.Algebra.Polynomial.Sturm.Tarski
public import TauCeti.Algebra.Polynomial.Sturm.OneSided
public import TauCeti.Algebra.Polynomial.Eval.Infinity
public import TauCeti.Algebra.Polynomial.Sturm.Infinity
public import TauCeti.FieldTheory.RealClosure.AbstractRolle
public import TauCeti.Algebra.Polynomial.RealClosed.Sampling
public import TauCeti.Data.Fintype.Fiber
public import TauCeti.Data.Matrix.OccCount
public import TauCeti.Data.SignType.Lagrange
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Moments
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Defs
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Polynomial
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.WholeLine
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Roots

public import TauCeti.FieldTheory.IsRealClosed.Real

#print axioms MemoryDecision.risk_lt_iff_uniform_bound
#print axioms MemoryDecision.mem_performance_iff
#print axioms MemoryDecision.threshold_iff_value_lt
#print axioms MemoryDecision.thresholds_eq_ray_of_value_eq
#print axioms MemoryDecision.thresholds_empty_iff_value_top
#print axioms MemoryDecision.gain_iff
#print axioms MemoryDecision.gain_has_rational_witness
#print axioms MemoryDecision.value_nonneg
#print axioms MemoryDecision.value_antitone
#print axioms MemoryDecision.strict_separation_of_unique_attainment
#print axioms MemoryBlock.blockOne_rank
#print axioms MemoryBlock.upperBlock_rank
#print axioms RealizationCore.rank_H_eq_one_add_rank_S
#print axioms MemoryRank.Incremental.Q_zero_iff
#print axioms MemoryRank.CutRank.memRank_le
#print axioms QuadraticBenchmark.productPoly_eval
#print axioms QuadraticBenchmark.productPoly_eval_zero
#print axioms QuadraticBenchmark.quadMinimaxValue_pos
#print axioms SmoothBenchmark.theta_pos
#print axioms SmoothBenchmark.theta_ge_one
#print axioms SmoothBenchmark.theta_recurrence_standard
#print axioms SmoothBenchmark.theta_recurrence_final
#print axioms SmoothBenchmark.factoredT_rank_le_one

#print axioms RegisterMachine.Hk_eq_phi_mul_psi
#print axioms RegisterMachine.necessity_rank_le_unconditional
#print axioms RegisterMachine.increment_rank_lower_bound
#print axioms RegisterMachine.maxCutRank_le_registers
#print axioms RegisterMachine.chain_realizes
#print axioms RegisterMachine.cv_succ
#print axioms RegisterMachine.cdrop_range
#print axioms RegisterMachine.ch_range
#print axioms RegisterMachine.coordL_coordJ
#print axioms RegisterMachine.canonical_correct
#print axioms RegisterMachine.cH_rank_eq_Hk_rank
#print axioms RegisterMachine.realization_iff_rank_all
#print axioms RegisterMachine.realization_iff_maxCutRank
#print axioms RegisterMachine.isLeast_registerCount
#print axioms RegisterMachine.realization_iff_incrementLocus
#print axioms RegisterMachine.one_register_iff_zero_increment
#print axioms RegisterMachine.vectorState_coordinate
#print axioms RegisterMachine.vectorRealizes_iff_scalar
#print axioms RegisterMachine.vectorRealization_iff_maxCutRank
#print axioms RegisterMachine.isLeast_vectorRegisterCount

#print axioms Continuation.ProjectedSupport.piK
#print axioms Continuation.ProjectedSupport.proj_iff_variational
#print axioms Continuation.ProjectedSupport.proj_unique
#print axioms Continuation.ProjectedSupport.proj_graph_correct
#print axioms Continuation.ProjectedSupport.piK_of_mem
#print axioms Continuation.ProjectedSupport.piK_singleton
#print axioms Continuation.ProjectedSupport.projStateAux
#print axioms Continuation.ProjectedSupport.projQuery
#print axioms Continuation.ProjectedSupport.directStateAux
#print axioms Continuation.ProjectedSupport.weightedSum_initState
#print axioms Continuation.ProjectedSupport.correction_algebra

#print axioms Continuation.SmoothSupport.gram_identity
#print axioms Continuation.SmoothSupport.gram_norm
#print axioms Continuation.SmoothSupport.psd_factorization
#print axioms Continuation.SmoothSupport.forward_psd

#print axioms RealizationCore.d_of_W_of
#print axioms RealizationCore.T_of_W_of
#print axioms RealizationCore.W_of_dT_of
#print axioms RealizationCore.coordinateEquiv
#print axioms RealizationCore.realization_iff_coordinates

#print axioms Continuation.Projected.projStateAux_succ
#print axioms Continuation.Projected.projQuery_zero
#print axioms Continuation.Projected.projQuery_succ_eq_piK
#print axioms Continuation.Projected.projQuery_mem_K
#print axioms Continuation.Projected.direct_singleton_a
#print axioms Continuation.Projected.proj_singleton_a

#print axioms SmoothOGM.ogmW_strict
#print axioms SmoothOGM.ogmW_last_is_d
#print axioms SmoothOGM.stateNat_eq
#print axioms SmoothOGM.ogmMachine_realizes
#print axioms SmoothOGM.ogmHasRealization
#print axioms SmoothOGM.ogmVectorRealizes

#print axioms QuadraticFoundations.pIter_eval_zero
#print axioms QuadraticFoundations.pIter_natDegree_le
#print axioms QuadraticFoundations.pIter_T_zero_eq_product
#print axioms QuadraticFoundations.pN_T_zero_eq_productPoly
#print axioms QuadraticFoundations.chebM_degree
#print axioms QuadraticFoundations.chebM_natDegree
#print axioms QuadraticFoundations.chebM_eval_cos
#print axioms QuadraticFoundations.chebM_eval_neg
#print axioms QuadraticFoundations.chebM_comp_neg
#print axioms QuadraticFoundations.chebM_eval_zero
#print axioms QuadraticFoundations.chebM_dvd_X
#print axioms QuadraticFoundations.chebM_s
#print axioms QuadraticFoundations.chebM_eq_X_mul_s
#print axioms QuadraticFoundations.neg_X_pow
#print axioms QuadraticFoundations.comp_neg_X_coeff

#print axioms MemorySemialgebraic.QFFormula.eval
#print axioms MemorySemialgebraic.zero_mem_algebraic
#print axioms MemorySemialgebraic.qf_formula_stable_nonZero
#print axioms MemorySemialgebraic.frontier_solutionSet_subset_zeroLocus_nonZero
#print axioms MemorySemialgebraic.qf_endpoint_algebraic
#print axioms MemorySemialgebraic.frontier_empty_of_all_zero
#print axioms MemorySemialgebraic.linear_root_algebraic

#print axioms MemorySemialgebraic.ray_endpoint_algebraic
#print axioms MemorySemialgebraic.finite_value_algebraic_of_qf_thresholds

#print axioms InstalledOGM.ogmT_inst
#print axioms InstalledOGM.ogmS_inst
#print axioms InstalledOGM.Hk_bridge
#print axioms InstalledOGM.theta_one_one
#print axioms InstalledOGM.theta_N_one
#print axioms InstalledOGM.theta_one_gt_one
#print axioms InstalledOGM.T10_numer_ne_zero
#print axioms InstalledOGM.increment_eq
#print axioms InstalledOGM.increment_eq_zero
#print axioms InstalledOGM.ogmACoeff_one_zero
#print axioms InstalledOGM.ogmACoeff_one_zero_simplified
#print axioms InstalledOGM.ogmECoeff_one_zero
#print axioms InstalledOGM.ogmECoeff_one_zero_simplified
#print axioms InstalledOGM.ogmACoeff_two_zero
#print axioms InstalledOGM.T10_eq
#print axioms InstalledOGM.T10_ne_zero
#print axioms InstalledOGM.T_zero_of_N1
#print axioms InstalledOGM.S1_entry_T10
#print axioms InstalledOGM.S1_rank_one
#print axioms InstalledOGM.T_in_Q1_of_realization
#print axioms InstalledOGM.T_in_Q1_unconditional
#print axioms InstalledOGM.s_WO_eq_one_of_N1
#print axioms InstalledOGM.s_WO_not_one_of_ge2
#print axioms InstalledOGM.memory_conclusion_N1
#print axioms InstalledOGM.memory_conclusion_ge2
#print axioms InstalledOGM.memory_conclusion_N1_unconditional
#print axioms InstalledOGM.memory_conclusion_ge2_unconditional
#print axioms InstalledOGM.theta_pos_ne_zero
#print axioms InstalledOGM.T10_ne_zero_of_pos
#print axioms InstalledOGM.memory_conclusion_ge2_pos
#print axioms InstalledOGM.T10_eq_pos

#print axioms QuadraticResidual.errorIter
#print axioms QuadraticResidual.errorIter_eq_polynomial
#print axioms QuadraticResidual.vectorTarget_step
#print axioms QuadraticResidual.errorIter_eq_history
#print axioms QuadraticResidual.history_eq_polynomial

#print axioms QuadraticSpectral.polynomial_energy_bound
#print axioms QuadraticSpectral.lossSet
#print axioms QuadraticSpectral.scalar_loss_mem
#print axioms QuadraticSpectral.isGreatest_lossSet
#print axioms QuadraticSpectral.spectral_risk_attained
#print axioms QuadraticSpectral.historyLossSet
#print axioms QuadraticSpectral.historyLossSet_eq
#print axioms QuadraticSpectral.history_risk_eq_scalar_max

#print axioms RegisterMachine.qFin
#print axioms RegisterMachine.target_zero_grad
#print axioms RegisterMachine.qFin_zero_eq_e1
#print axioms RegisterMachine.dot_c_qFin
#print axioms RegisterMachine.dot_o_qFin
#print axioms RegisterMachine.F_mul_qFin
#print axioms RegisterMachine.onesVec
#print axioms RegisterMachine.dotLinear
#print axioms RegisterMachine.dotLinear_apply_eq_dot
#print axioms RegisterMachine.e1Linear
#print axioms RegisterMachine.e1_dot_ones
#print axioms RegisterMachine.e1Linear_apply_onesVec
#print axioms RegisterMachine.dotLinear_ne_zero_of_dot_eq_one
#print axioms RegisterMachine.e1Linear_ne_zero
#print axioms RegisterMachine.finrank_fin_fun_real
#print axioms RegisterMachine.ker_finrank_of_dot_eq_one
#print axioms RegisterMachine.ker_finrank_e1Linear
#print axioms RegisterMachine.kerEquiv
#print axioms RegisterMachine.projCMap
#print axioms RegisterMachine.projEMap
#print axioms RegisterMachine.projCMap_apply'
#print axioms RegisterMachine.projEMap_apply'
#print axioms RegisterMachine.dotLinear_projCMap
#print axioms RegisterMachine.e1Linear_projEMap
#print axioms RegisterMachine.projToKerC
#print axioms RegisterMachine.projToKerE
#print axioms RegisterMachine.A_lin
#print axioms RegisterMachine.A_lin_apply
#print axioms RegisterMachine.B_lin
#print axioms RegisterMachine.B_lin_apply
#print axioms RegisterMachine.A_lin_q_eq_ones
#print axioms RegisterMachine.e1Linear_A_lin
#print axioms RegisterMachine.projToKerE_A_lin
#print axioms RegisterMachine.B_lin_A_lin
#print axioms RegisterMachine.A_lin_B_lin
#print axioms RegisterMachine.A_equiv
#print axioms RegisterMachine.A_mat
#print axioms RegisterMachine.A_mat_inv
#print axioms RegisterMachine.A_mat_mulVec
#print axioms RegisterMachine.A_mat_inv_mulVec
#print axioms RegisterMachine.A_mat_q_eq_ones
#print axioms RegisterMachine.e1_dot_A_mat
#print axioms RegisterMachine.B_lin_ones_eq_q
#print axioms RegisterMachine.A_mat_inv_ones_eq_q
#print axioms RegisterMachine.A_equiv_q_eq_ones
#print axioms RegisterMachine.A_equiv_symm_ones_eq_q
#print axioms RegisterMachine.e1_comp_A_equiv
#print axioms RegisterMachine.A_equiv_maps_ker

#print axioms RegisterMachine.A_of
#print axioms RegisterMachine.A_of_q_eq_ones
#print axioms RegisterMachine.e1_dot_A_of
#print axioms RegisterMachine.A_of_inv_mat
#print axioms RegisterMachine.A_of_inv_ones_eq_qFin
#print axioms RegisterMachine.normF
#print axioms RegisterMachine.normB
#print axioms RegisterMachine.normF_ones

#print axioms QuadraticFoundations.chebM_s_comp_neg
#print axioms QuadraticFoundations.chebM_s_odd_coeff_zero
#print axioms QuadraticFoundations.chebM_derivative_eval_zero
#print axioms QuadraticFoundations.evenHalve
#print axioms QuadraticFoundations.evenHalve_coeff
#print axioms QuadraticFoundations.monomial_comp_X_sq
#print axioms QuadraticFoundations.sum_comp_lemma
#print axioms QuadraticFoundations.evenHalve_comp_X_sq
#print axioms QuadraticFoundations.chebM_q
#print axioms QuadraticFoundations.chebM_q_comp_X_sq
#print axioms QuadraticFoundations.chebM_s_eq_q_mul
#print axioms QuadraticFoundations.p_star
#print axioms QuadraticFoundations.p_star_eval
#print axioms QuadraticFoundations.p_star_at_zero
#print axioms QuadraticFoundations.p_star_natDegree_le
#print axioms QuadraticFoundations.chebM_sq_le_one
#print axioms QuadraticFoundations.p_star_weight_identity
#print axioms QuadraticFoundations.p_star_weight_le
#print axioms QuadraticFoundations.p_star_weight_at_L
#print axioms QuadraticFoundations.p_star_isGreatest_weight

#print axioms MinorSelection.select_independent
#print axioms MinorSelection.exists_nonsingular_minor
#print axioms MinorSelection.rank_le_iff_minors_vanish

#print axioms MemorySemialgebraic.CoeffIndex
#print axioms MemorySemialgebraic.MinorIndex
#print axioms MemorySemialgebraic.polyBlock
#print axioms MemorySemialgebraic.phi
#print axioms MemorySemialgebraic.coeffEval
#print axioms MemorySemialgebraic.eval_polyBlock
#print axioms MemorySemialgebraic.eval_phi
#print axioms MemorySemialgebraic.Q_iff_phi_zero
#print axioms MemorySemialgebraic.realization_iff_phi_zero

#print axioms FiniteConvexInterpolation.RelativeSubgradient
#print axioms FiniteConvexInterpolation.plane
#print axioms FiniteConvexInterpolation.envelope
#print axioms FiniteConvexInterpolation.plane_le_envelope
#print axioms FiniteConvexInterpolation.envelope_at_site
#print axioms FiniteConvexInterpolation.plane_combination
#print axioms FiniteConvexInterpolation.envelope_convex
#print axioms FiniteConvexInterpolation.active_slope_subgradient
#print axioms FiniteConvexInterpolation.envelope_subgradient_everywhere
#print axioms FiniteConvexInterpolation.envelope_data_subgradient
#print axioms FiniteConvexInterpolation.interpolation_iff
#print axioms FiniteConvexInterpolation.bounded_subgradient_everywhere
#print axioms FiniteConvexInterpolation.zero_slope_minimizer

#print axioms QuadraticLower.card_finset_roots_le
#print axioms QuadraticLower.M_pos
#print axioms QuadraticLower.M_ne_zero
#print axioms QuadraticLower.angle_nonneg
#print axioms QuadraticLower.angle_lt_half_pi
#print axioms QuadraticLower.cos_altU_strictAntiOn
#print axioms QuadraticLower.cos_altU_mul_p_star

#print axioms QuadraticLower.root_j
#print axioms QuadraticLower.theta_j
#print axioms QuadraticLower.theta_j_eq
#print axioms QuadraticLower.theta_j_pos
#print axioms QuadraticLower.theta_j_lt_pi_div_two
#print axioms QuadraticLower.theta_j_mem_Ioo
#print axioms QuadraticLower.theta_j_mem_Icc_zero_pi
#print axioms QuadraticLower.cos_theta_j_pos
#print axioms QuadraticLower.cos_theta_j_lt_one
#print axioms QuadraticLower.root_j_pos
#print axioms QuadraticLower.root_j_lt_L
#print axioms QuadraticLower.root_j_mem_Ioo
#print axioms QuadraticLower.root_j_ne_zero
#print axioms QuadraticLower.theta_j_strictMono
#print axioms QuadraticLower.cos_theta_j_strictAnti
#print axioms QuadraticLower.root_j_injective
#print axioms QuadraticLower.root_j_pairwise_distinct
#print axioms QuadraticLower.cos_nat_pi_add_pi_div_two
#print axioms QuadraticLower.cos_two_mul_add_one_pi_div_two
#print axioms QuadraticLower.p_star_eval_root_j
#print axioms QuadraticLower.p_star_ne_zero
#print axioms QuadraticLower.p_star_natDegree_eq
#print axioms QuadraticLower.q_factor
#print axioms QuadraticLower.q_factor_eval_zero
#print axioms QuadraticLower.q_factor_natDegree_le
#print axioms QuadraticLower.q_factor_eval_root
#print axioms QuadraticLower.p_star_factorization
#print axioms QuadraticLower.schedD
#print axioms QuadraticLower.schedT
#print axioms QuadraticLower.productPoly_schedD_eq_q_factor
#print axioms QuadraticLower.schedD_pN_eq_p_star
#print axioms QuadraticLower.quadratic_risk_le
#print axioms QuadraticLower.p_star_lossSet_isGreatest
#print axioms QuadraticLower.historyLossSet_schedD_isGreatest
#print axioms QuadraticLower.history_risk_value

#print axioms RegisterMachine.A_mat_inv_mul_A_mat
#print axioms RegisterMachine.A_mat_mul_A_mat_inv
#print axioms RegisterMachine.A_of_inv_mul_A_of
#print axioms RegisterMachine.A_of_mul_A_of_inv
#print axioms RegisterMachine.dot_e1_self
#print axioms RegisterMachine.A_fixed
#print axioms RegisterMachine.A_fixed_inv
#print axioms RegisterMachine.A_fixed_ones_eq_e1
#print axioms RegisterMachine.A_fixed_inv_e1_eq_ones
#print axioms RegisterMachine.A_fixed_inv_mul_A_fixed
#print axioms RegisterMachine.A_fixed_mul_A_fixed_inv
#print axioms RegisterMachine.dot_e1_A_fixed
#print axioms RegisterMachine.dot_e1_A_fixed_inv
#print axioms RegisterMachine.NormalizedMachine
#print axioms RegisterMachine.normalizedMachineOf
#print axioms RegisterMachine.stateNormNat
#print axioms RegisterMachine.stateNormFin
#print axioms RegisterMachine.stateNormNat_zero
#print axioms RegisterMachine.stateNormNat_succ
#print axioms RegisterMachine.RealizesNorm
#print axioms RegisterMachine.normStateNat_eq_A_of_stateNat
#print axioms RegisterMachine.ordinary_to_normalized
#print axioms RegisterMachine.normalized_to_ordinary
#print axioms RegisterMachine.realization_iff_normalized
#print axioms RegisterMachine.vectorNormStateNat
#print axioms RegisterMachine.vectorNormState_coordinate
#print axioms RegisterMachine.vectorNormReadout_coordinate
#print axioms RegisterMachine.VectorRealizesNorm
#print axioms RegisterMachine.normalized_readout_all
#print axioms RegisterMachine.vectorRealizesNorm_iff_scalar
#print axioms RegisterMachine.vectorRealization_iff_normalized

#print axioms QuadraticLower.altU
#print axioms QuadraticLower.altX
#print axioms QuadraticLower.angle_lt_pi_div_two
#print axioms QuadraticLower.angle_mem_Icc_pi
#print axioms QuadraticLower.altU_pos
#print axioms QuadraticLower.altU_nonneg
#print axioms QuadraticLower.altU_le_one
#print axioms QuadraticLower.altX_nonneg
#print axioms QuadraticLower.altX_pos
#print axioms QuadraticLower.altX_le_L
#print axioms QuadraticLower.altX_mem_Icc
#print axioms QuadraticLower.altX_zero
#print axioms QuadraticLower.angle_strictMono_aux
#print axioms QuadraticLower.altU_strictAnti_on
#print axioms QuadraticLower.altX_strictAnti_on
#print axioms QuadraticLower.altX_injOn
#print axioms QuadraticLower.altU_mul_p_star
#print axioms QuadraticLower.violation_bound
#print axioms QuadraticLower.neg_one_pow_eq_or
#print axioms QuadraticLower.q_sign
#print axioms QuadraticLower.q_eval_sign_alternates
#print axioms QuadraticLower.q_consecutive_opposite_sign
#print axioms QuadraticLower.ivt_root_between
#print axioms QuadraticLower.q_natDegree_le
#print axioms QuadraticLower.q_eval_zero
#print axioms QuadraticLower.q_isRoot_zero
#print axioms QuadraticLower.altX_intervals_disjoint
#print axioms QuadraticLower.Ioo_not_contain_zero
#print axioms QuadraticLower.degree_contradiction
#print axioms QuadraticLower.strict_lower_bound
#print axioms QuadraticLower.lower_bound_N0
#print axioms QuadraticLower.quadratic_lower_bound
#print axioms QuadraticLower.bddAbove_eval_sq_image
#print axioms QuadraticLower.quadratic_lower_bound_of_degree

#print axioms QuadraticLower.historyLossSet_schedD_sSup
#print axioms QuadraticLower.historyLossSet_schedD_sSup_eq_quadMinimaxValue
#print axioms QuadraticLower.pIter_lower_bound
#print axioms QuadraticLower.quad_minimax_lower
#print axioms QuadraticLower.Coeff
#print axioms QuadraticLower.riskOf
#print axioms QuadraticLower.bddAbove_lossSet
#print axioms QuadraticLower.risk_ge_constant
#print axioms QuadraticLower.risk_schedD_le_constant
#print axioms QuadraticLower.risk_schedD_eq_constant
#print axioms QuadraticLower.sInf_risk_eq
#print axioms QuadraticLower.schedT_in_Q
#print axioms QuadraticLower.all_methods_lower_bound
#print axioms QuadraticLower.minimax_attained_in_Q
#print axioms QuadraticLower.threshold_set_eq_Ioi

#print axioms QuadraticOperational.feasible
#print axioms QuadraticOperational.loss
#print axioms QuadraticOperational.memory
#print axioms QuadraticOperational.zeroIncrement
#print axioms QuadraticOperational.mem_memory_iff_realization
#print axioms QuadraticOperational.zeroIncrement_mem
#print axioms QuadraticOperational.schedule_has_one_register
#print axioms QuadraticOperational.risk_lower_bound
#print axioms QuadraticOperational.schedule_risk
#print axioms QuadraticOperational.value_eq
#print axioms QuadraticOperational.thresholds_eq
#print axioms QuadraticOperational.no_memory_gain

-- Dual interpolation construction (not yet conjugate regularity).
#print axioms E
#print axioms SmoothDual.hComp
#print axioms SmoothDual.Hi
#print axioms SmoothDual.H
#print axioms SmoothDual.Hi_eq
#print axioms SmoothDual.Hi_at_g
#print axioms SmoothDual.Hi_at_g_eq_h
#print axioms SmoothDual.norm_sq_convex_combo
#print axioms SmoothDual.Hi_convex_combo
#print axioms SmoothDual.H_ge_Hi
#print axioms SmoothDual.H_exists_eq
#print axioms SmoothDual.H_attained
#print axioms SmoothDual.H_strongConvex
#print axioms SmoothDual.H_strongConvex_t
#print axioms SmoothDual.H_le_at_g
#print axioms SmoothDual.H_contact
#print axioms SmoothDual.H_contact'
#print axioms SmoothDual.H_subgradient
#print axioms SmoothDual.H_subgradient_weak

-- Finite rational partition and positive-radius root cover.
#print axioms RootIsolation.numSteps
#print axioms RootIsolation.partitionPoints
#print axioms RootIsolation.partitionPoints_length
#print axioms RootIsolation.consecutivePairs
#print axioms RootIsolation.partitionPoints_eq_range_map
#print axioms RootIsolation.partitionPoints_get
#print axioms RootIsolation.consecutivePairs_mem
#print axioms RootIsolation.original_statement_false
#print axioms RootIsolation.cover_from_cauchyBound

-- Actual smooth instances, coefficient and continuity support, necessary interpolation.
#print axioms SmoothAttain.Instance
#print axioms SmoothAttain.iter
#print axioms SmoothAttain.terminalLoss
#print axioms SmoothAttain.pReal
#print axioms SmoothAttain.pReal_eq_productPoly_eval
#print axioms SmoothAttain.productPoly_coeff_zero
#print axioms SmoothAttain.productPoly_succ
#print axioms SmoothAttain.coeff_mul_C_add_CdX_one
#print axioms SmoothAttain.coeff_mul_C_add_CdX_two
#print axioms SmoothAttain.productPoly_coeff_one
#print axioms SmoothAttain.pairSum
#print axioms SmoothAttain.pairSum_succ
#print axioms SmoothAttain.productPoly_coeff_two
#print axioms SmoothAttain.zeta1_eq
#print axioms SmoothAttain.zeta2_eq
#print axioms SmoothAttain.sum_sq_eq
#print axioms SmoothAttain.sumAlphaSq_eq_zeta
#print axioms SmoothAttain.toPi2
#print axioms SmoothAttain.ofPi2
#print axioms SmoothAttain.ofPi2_zero
#print axioms SmoothAttain.G_continuous
#print axioms SmoothAttain.f_continuous
#print axioms SmoothAttain.iter_continuous
#print axioms SmoothAttain.terminalLoss_continuous
#print axioms SmoothAttain.terminalLoss_lsc
#print axioms SmoothAttain.quadObjective
#print axioms SmoothAttain.quadGradient
#print axioms SmoothAttain.quadObjective_at_xStar
#print axioms SmoothAttain.quadGradient_at_xStar
#print axioms SmoothAttain.quadObjective_nonneg
#print axioms SmoothAttain.quadObjective_isMin
#print axioms SmoothAttain.errorPoly
#print axioms SmoothAttain.errorPoly_zero_eq_one
#print axioms SmoothNecessary.line_hasDerivAt
#print axioms SmoothNecessary.convex_line
#print axioms SmoothNecessary.tangent_lower
#print axioms SmoothNecessary.descent
#print axioms SmoothNecessary.interpolation_necessary
#print axioms SmoothAttain.Instance.interpolation_necessary
#print axioms SmoothAttain.Instance.gradient_at_minimizer

-- Actual causal oracle execution and zero-chain support.
#print axioms OracleTrajectory.run
#print axioms OracleTrajectory.run_eq
#print axioms OracleTrajectory.run_zero
#print axioms OracleTrajectory.unique
#print axioms OracleTrajectory.zero_chain
#print axioms OracleTrajectory.run_eq_vectorTarget
#print axioms OracleTrajectory.realization_executes_oracle

-- Forward exact-function to finite Gram-model reduction.
#print axioms SmoothGramModel.gram
#print axioms SmoothGramModel.combination_inner
#print axioms SmoothGramModel.combination_norm
#print axioms SmoothGramModel.gram_psd
#print axioms SmoothGramModel.Index
#print axioms SmoothGramModel.index_card
#print axioms SmoothGramModel.v
#print axioms SmoothGramModel.w
#print axioms SmoothGramModel.value
#print axioms SmoothGramModel.Feasible
#print axioms SmoothGramModel.site
#print axioms SmoothGramModel.physical
#print axioms SmoothGramModel.values
#print axioms SmoothGramModel.combine_v
#print axioms SmoothGramModel.combine_w
#print axioms SmoothGramModel.value_values
#print axioms SmoothGramModel.actual_feasible
#print axioms SmoothGramModel.terminalLoss
#print axioms SmoothGramModel.actualLossSet
#print axioms SmoothGramModel.modelLossSet
#print axioms SmoothGramModel.actualLossSet_subset_modelLossSet
#print axioms SmoothGramModel.actual_uniform_bound_of_model_bound

-- Gram reconstruction and execution given an actual interpolating function.
#print axioms SmoothGramModel.exists_euclidean_gram
#print axioms SmoothGramModel.exists_gram_in_dimension
#print axioms SmoothGramModel.model_data_inequalities
#print axioms SmoothGramModel.realize_of_interpolant

-- Continuation/Smooth/Attain/ScalarRisk.lean
#print axioms SmoothAttain.scalarObj
#print axioms SmoothAttain.scalarGrad
#print axioms SmoothAttain.scalar_hasGradientAt
#print axioms SmoothAttain.scalar_lipschitz
#print axioms SmoothAttain.scalar_convexOn
#print axioms SmoothAttain.scalarInstance
#print axioms SmoothAttain.prodRange'
#print axioms SmoothAttain.prodRange'_zero
#print axioms SmoothAttain.prodRange'_succ
#print axioms SmoothAttain.prodRange'_eq_pReal
#print axioms SmoothAttain.scalar_iter_sub_range
#print axioms SmoothAttain.scalar_terminalLoss_eq
#print axioms SmoothAttain.mkX
#print axioms SmoothAttain.norm_mkX
#print axioms SmoothAttain.norm_mkX_eq_abs
#print axioms SmoothAttain.norm_mkX_eq_R
#print axioms SmoothAttain.norm_sub_mkX_zero
#print axioms SmoothAttain.scalarInstanceExtremal
#print axioms SmoothAttain.scalar_extremal_loss
#print axioms SmoothAttain.continuous_real_toEReal
#print axioms SmoothAttain.terminalLoss_ereal_lsc
#print axioms SmoothAttain.AllInstances
#print axioms SmoothAttain.risk0
#print axioms SmoothAttain.risk0_lsc
#print axioms SmoothAttain.risk0_ge_scalar

-- Continuation/Smooth/Attain/Coercivity.lean
#print axioms SmoothAttain.lam
#print axioms SmoothAttain.lam_mem_Icc
#print axioms SmoothAttain.lam_pos
#print axioms SmoothAttain.lam_ne_zero
#print axioms SmoothAttain.lam_lt_L
#print axioms SmoothAttain.lam_injective
#print axioms SmoothAttain.lam_le_L1
#print axioms SmoothAttain.lam_nonneg
#print axioms SmoothAttain.productPoly_natDegree_le
#print axioms SmoothAttain.Mmat
#print axioms SmoothAttain.Mmat_eq_diag_mul_vandermonde
#print axioms SmoothAttain.det_Mmat_ne_zero
#print axioms SmoothAttain.eval_M_mul_zeta
#print axioms SmoothAttain.abs_det_le
#print axioms SmoothAttain.C_entry
#print axioms SmoothAttain.C_entry_nonneg
#print axioms SmoothAttain.C_entry_ge_S1
#print axioms SmoothAttain.C_entry_ge_pow
#print axioms SmoothAttain.lam_pow_le_C_entry
#print axioms SmoothAttain.M_entries_le_C
#print axioms SmoothAttain.b_bound
#print axioms SmoothAttain.cramer_eq_det_smul_zeta
#print axioms SmoothAttain.K_bound
#print axioms SmoothAttain.K_bound_nonneg
#print axioms SmoothAttain.coeff_bound
#print axioms SmoothAttain.coeff_bound_two_step
#print axioms SmoothAttain.B_bound
#print axioms SmoothAttain.B_bound_nonneg
#print axioms SmoothAttain.sumAlphaSq_le_B_bound

-- Continuation/Smooth/ConjBounds.lean
#print axioms SmoothDual.F_conj
#print axioms SmoothDual.F_conj_bddAbove
#print axioms SmoothDual.F_conj_at_xi
#print axioms SmoothDual.F_conj_subgradient

-- Continuation/RootIsolation/Separation.lean
#print axioms RootIsolation.coeffAbsSum
#print axioms RootIsolation.aeval_bound_of_coeffAbsSum
#print axioms RootIsolation.abs_le_C_of_mem_Icc
#print axioms RootIsolation.bezout_at_root
#print axioms RootIsolation.separationBound_of_bezout
#print axioms RootIsolation.separationEps
#print axioms RootIsolation.separationEps_pos
#print axioms RootIsolation.separationEps_le
#print axioms RootIsolation.separation_ge_eps
#print axioms RootIsolation.squarefreePart
#print axioms RootIsolation.squarefreePart_ne_zero
#print axioms RootIsolation.existsBezout_of_coprime
#print axioms RootIsolation.existsBezout_of_gcd_one
#print axioms RootIsolation.squarefreePart_dvd
#print axioms RootIsolation.root_of_squarefreePart_root

-- General strong-convex-conjugate regularity.
#print axioms ConjugateRegularity.strong_support
#print axioms ConjugateRegularity.maximizers_monotone
#print axioms ConjugateRegularity.maximizers_lipschitz
#print axioms ConjugateRegularity.value
#print axioms ConjugateRegularity.value_ge
#print axioms ConjugateRegularity.value_support
#print axioms ConjugateRegularity.value_remainder
#print axioms ConjugateRegularity.value_convex
#print axioms ConjugateRegularity.value_hasGradientAt
#print axioms ConjugateRegularity.maximizer_unique
#print axioms ConjugateRegularity.exists_maximizer
#print axioms ConjugateRegularity.exists_smooth_conjugate

-- Necessary and sufficient smooth-convex finite interpolation.
#print axioms SmoothDual.Hi_continuous
#print axioms SmoothDual.H_continuous
#print axioms SmoothDual.interpolation_sufficient
#print axioms SmoothInterpolation.sufficient
#print axioms SmoothInterpolation.iff_interpolable

-- Exact finite Gram loss model and dimension reduction.
#print axioms SmoothGramModel.realize_feasible
#print axioms SmoothGramModel.modelLossSet_subset_actualLossSet
#print axioms SmoothGramModel.actualLossSet_eq_modelLossSet
#print axioms SmoothGramModel.dimension_reduction
#print axioms SmoothGramModel.uniform_bound_iff

-- Smooth operational memory/schedule/performance bridge.
#print axioms SmoothOperational.iter_cumulative
#print axioms SmoothOperational.zero_increment_trajectory
#print axioms SmoothOperational.zero_increment_loss
#print axioms SmoothOperational.feasible
#print axioms SmoothOperational.loss
#print axioms SmoothOperational.memory
#print axioms SmoothOperational.zeroIncrement
#print axioms SmoothOperational.mem_memory_iff_realization
#print axioms SmoothOperational.zeroIncrement_mem
#print axioms SmoothOperational.mem_memory_zero_iff
#print axioms SmoothOperational.actualLossSet_iff
#print axioms SmoothOperational.zero_increment_risk
#print axioms SmoothOperational.value_zero_eq_inf_risk0
#print axioms SmoothOperational.performance_iff_gram

-- Actual compact risk sublevels and attaining one-register schedules.
#print axioms SmoothAttain.sublevel_pReal_sq_le
#print axioms SmoothAttain.risk0_nonneg
#print axioms SmoothAttain.sublevel_pReal_abs_le
#print axioms SmoothAttain.sublevel_sum_sq_le_B
#print axioms SmoothAttain.finiteSublevel
#print axioms SmoothAttain.finiteSublevel_closed
#print axioms SmoothAttain.norm_bound_of_sum_sq_le
#print axioms SmoothAttain.finiteSublevel_bounded
#print axioms SmoothAttain.finiteSublevel_isCompact
#print axioms SmoothAttain.iter_zero_aux
#print axioms SmoothAttain.iter_zero
#print axioms SmoothAttain.terminalLoss_zero
#print axioms SmoothAttain.terminalLoss_le_half
#print axioms SmoothAttain.risk0_at_zero_le
#print axioms SmoothAttain.finiteSublevel_nonempty
#print axioms SmoothAttain.exists_minimizer
#print axioms SmoothAttain.isMinOn_attains_iInf

-- Attainment in the actual operational one-register class.
#print axioms SmoothOperational.exists_optimal_one_register
#print axioms SmoothOperational.value_zero_bounds

-- Exact projected loss model and bounded-subgradient variant.
#print axioms ProjectedLossModel.Instance
#print axioms ProjectedLossModel.pre
#print axioms ProjectedLossModel.site
#print axioms ProjectedLossModel.slope
#print axioms ProjectedLossModel.val
#print axioms ProjectedLossModel.Feasible
#print axioms ProjectedLossModel.Admissible
#print axioms ProjectedLossModel.terminalLoss
#print axioms ProjectedLossModel.direct_mem
#print axioms ProjectedLossModel.trajectory_of_feasible
#print axioms ProjectedLossModel.realize_feasible
#print axioms ProjectedLossModel.actual_feasible
#print axioms ProjectedLossModel.actualLossSet
#print axioms ProjectedLossModel.modelLossSet
#print axioms ProjectedLossModel.lossSet_eq
#print axioms ProjectedLossModel.direct_zero
#print axioms ProjectedLossModel.bounded_zero_loss
#print axioms ProjectedLossModel.bounded_lossSet_eq
#print axioms ProjectedLossModel.unbounded_lossSet_eq

-- Continuation.Projected.LowerBound
#print axioms Continuation.Projected.projection_correction_orthogonal
#print axioms Continuation.Projected.segment_coordinate_mem
#print axioms Continuation.Projected.projection_correction_orthogonal_of_interior_segment
#print axioms Continuation.Projected.ordinary
#print axioms Continuation.Projected.target_succ_increment
#print axioms Continuation.Projected.direct_segment
#print axioms Continuation.Projected.rawState
#print axioms Continuation.Projected.correction
#print axioms Continuation.Projected.state_scalarization
#print axioms Continuation.Projected.query_scalarization
#print axioms Continuation.Projected.state_affine
#print axioms Continuation.Projected.dot_affine
#print axioms Continuation.Projected.exists_small_scale
#print axioms Continuation.Projected.correction_inner_zero_of_segment
#print axioms Continuation.Projected.ProjectedRealizes
#print axioms Continuation.Projected.readout_on_segment
#print axioms Continuation.Projected.ordinary_realizes_of_segment
#print axioms Continuation.Projected.ordinary_realizes_of_nontrivial
#print axioms Continuation.Projected.projected_cut_rank_lower_bound
#print axioms Continuation.Projected.projected_memory_lower_bound

-- Continuation.RootIsolation.SimpleRoots
#print axioms RootIsolation.SimpleRoots.polyMapToReal
#print axioms RootIsolation.SimpleRoots.eval_map_algebraMap_eq_aeval
#print axioms RootIsolation.SimpleRoots.aeval_coe_eq_coe_eval
#print axioms RootIsolation.SimpleRoots.poly_aeval_continuous
#print axioms RootIsolation.SimpleRoots.exists_deriv_sign_nhd
#print axioms RootIsolation.SimpleRoots.mvt_right_sign
#print axioms RootIsolation.SimpleRoots.mvt_left_sign
#print axioms RootIsolation.SimpleRoots.simple_root_sign_change
#print axioms RootIsolation.SimpleRoots.pointRoots
#print axioms RootIsolation.SimpleRoots.signChangingIntervals
#print axioms RootIsolation.SimpleRoots.IsoInterval
#print axioms RootIsolation.SimpleRoots.IsoInterval.toSet
#print axioms RootIsolation.SimpleRoots.filteredIntervals
#print axioms RootIsolation.SimpleRoots.pointRoots_mem_iff
#print axioms RootIsolation.SimpleRoots.signChangingIntervals_mem_iff
#print axioms RootIsolation.SimpleRoots.partitionPoints_consecutive_form'
#print axioms RootIsolation.SimpleRoots.partitionPoints_get_eq'
#print axioms RootIsolation.SimpleRoots.partition_interval_length'
#print axioms RootIsolation.SimpleRoots.simple_root_mem_filteredIntervals

-- Generic energy certificate for OGM.
#print axioms OGMEnergy.R
#print axioms OGMEnergy.S
#print axioms OGMEnergy.energy_step
#print axioms OGMEnergy.energy_base
#print axioms OGMEnergy.prefix_identity
#print axioms OGMEnergy.terminal_identity
#print axioms OGMEnergy.objective_bound
#print axioms OGMEnergy.R_scale
#print axioms OGMEnergy.S_scale
#print axioms OGMEnergy.objective_bound_scaled

-- Complete projected realization construction and minimum register count.
#print axioms Continuation.Projected.readCoeffs
#print axioms Continuation.Projected.read_scalar
#print axioms Continuation.Projected.read_q
#print axioms Continuation.Projected.vectorState
#print axioms Continuation.Projected.vectorHistory
#print axioms Continuation.Projected.vectorState_inner
#print axioms Continuation.Projected.read_vector
#print axioms Continuation.Projected.projectedLift
#print axioms Continuation.Projected.weightedSum_shift
#print axioms Continuation.Projected.vectorHistory_succ
#print axioms Continuation.Projected.projectedLift_invariant
#print axioms Continuation.Projected.projectedLift_realizes
#print axioms Continuation.Projected.HasProjectedRealization
#print axioms Continuation.Projected.projected_realization_of_rank
#print axioms Continuation.Projected.projected_realization_iff_rank
#print axioms Continuation.Projected.projected_least_registers
#print axioms Continuation.Projected.projected_realization_iff_ordinary
#print axioms Continuation.Projected.oneProjected
#print axioms Continuation.Projected.projectedMachine_positive
#print axioms Continuation.Projected.singleton_realization
#print axioms Continuation.Projected.subsingleton_least_registers

-- Continuation.RootIsolation.SquarefreePreprocessing
#print axioms SquarefreePreprocessing.rootMultiplicity_gcd_eq_min
#print axioms SquarefreePreprocessing.squarefreePart
#print axioms SquarefreePreprocessing.gcd_ne_zero_of_p_ne_zero
#print axioms SquarefreePreprocessing.squarefreePart_mul
#print axioms SquarefreePreprocessing.squarefreePart_ne_zero
#print axioms SquarefreePreprocessing.qToR
#print axioms SquarefreePreprocessing.map_qToR_ne_zero
#print axioms SquarefreePreprocessing.derivative_map_qToR
#print axioms SquarefreePreprocessing.gcd_map_qToR
#print axioms SquarefreePreprocessing.pR_eq_dR_mul_qR
#print axioms SquarefreePreprocessing.aeval_eq_map_eval
#print axioms SquarefreePreprocessing.isRoot_map_iff_aeval
#print axioms SquarefreePreprocessing.eq_C_of_deriv_eq_zero'
#print axioms SquarefreePreprocessing.nat_min_sub_one
#print axioms SquarefreePreprocessing.nat_sub_sub_one
#print axioms SquarefreePreprocessing.squarefree_aeval_root_iff
#print axioms SquarefreePreprocessing.squarefree_deriv_ne_zero

-- Continuation.RootIsolation.CertifiedSeparation
#print axioms RootIsolation.SimpleRoots.sign_between_endpoint_and_local_neighborhood
#print axioms RootIsolation.SimpleRoots.sign_between_local_and_endpoint_neighborhood
#print axioms RootIsolation.SimpleRoots.endpoint_sign_of_unique_simple_root
#print axioms RootIsolation.SimpleRoots.simple_root_mem_half_separation

-- Continuation.RootIsolation.RationalBound
#print axioms RootIsolation.rationalRootBound
#print axioms RootIsolation.rationalRootBound_one_le
#print axioms RootIsolation.cauchyBound_le_rationalRootBound
#print axioms RootIsolation.root_norm_lt_rationalRootBound

-- Continuation.GJP.Simplex
#print axioms GJP.rOGM
#print axioms GJP.S
#print axioms GJP.partialSum
#print axioms GJP.phiTerm
#print axioms GJP.Phi
#print axioms GJP.DeltaProp
#print axioms GJP.deltaStar
#print axioms GJP.rOGM_pos
#print axioms GJP.rOGM_nonneg
#print axioms GJP.theta_sq_standard
#print axioms GJP.theta_sq_final
#print axioms GJP.S_zero_eq
#print axioms GJP.S_succ_eq
#print axioms GJP.S_eq_total
#print axioms GJP.deltaStar_S_eq
#print axioms GJP.deltaStar_total
#print axioms GJP.quadratic_le
#print axioms GJP.sqrt_two_mul_eq
#print axioms GJP.deltaStar_mem_Delta
#print axioms GJP.phiTerm_tied
#print axioms GJP.deltaStar_Phi_eq
#print axioms GJP.S_nonneg
#print axioms GJP.S_mono
#print axioms GJP.S_le_S_succ
#print axioms GJP.delta_le_S
#print axioms GJP.delta_eq_zero_of_S_eq_zero
#print axioms GJP.delta_sq_le
#print axioms GJP.delta_le_sqrt
#print axioms GJP.S_le_bound
#print axioms GJP.rOGM_leq_Phi
#print axioms GJP.le_of_sq_le_sq'
#print axioms GJP.sqrt_rOGM
#print axioms GJP.terminal_rOGM_identity
#print axioms GJP.total_split
#print axioms GJP.delta_le_of_sum_eq
#print axioms GJP.uniqueness_of_partialSum_bound
#print axioms GJP.uniqueness

-- Continuation.RootIsolation.IsolationCertificate
#print axioms RootIsolation.SimpleRoots.sign_change_has_root
#print axioms RootIsolation.SimpleRoots.filteredIntervals_unique_root
#print axioms RootIsolation.SimpleRoots.isolateWithCertificate
#print axioms RootIsolation.SimpleRoots.isolateWithCertificate_correct

-- SmoothDrori
#print axioms SmoothDrori.theta_final_gt_one_local
#print axioms SmoothDrori.hardF_algebra
#print axioms SmoothDrori.zetaStar
#print axioms SmoothDrori.zetaStar_last
#print axioms SmoothDrori.hardG
#print axioms SmoothDrori.hardX
#print axioms SmoothDrori.hardF
#print axioms SmoothDrori.hardG_norm_sq
#print axioms SmoothDrori.zetaStar_pos_aux
#print axioms SmoothDrori.zetaStar_Nplus1_eq
#print axioms SmoothDrori.zetaStar_N_eq
#print axioms SmoothDrori.zetaStar_ltN_eq
#print axioms SmoothDrori.theta_gt_one_final
#print axioms SmoothDrori.theta_two_mul_sub_one_pos
#print axioms SmoothDrori.coeff_pos_N
#print axioms SmoothDrori.coeff_pos_ltN
#print axioms SmoothDrori.zetaStar_nonneg_aux
#print axioms SmoothDrori.zetaStar_nonneg
#print axioms SmoothDrori.zetaStar_pos_aux2
#print axioms SmoothDrori.zetaStar_pos
#print axioms SmoothDrori.coeff_gt_one_N
#print axioms SmoothDrori.coeff_gt_one_ltN
#print axioms SmoothDrori.zetaStar_strictAnti
#print axioms SmoothDrori.hardF_value

-- OGMWeighted
#print axioms OGMWeighted.A
#print axioms OGMWeighted.B
#print axioms OGMWeighted.theta_mul_sub_one_standard
#print axioms OGMWeighted.theta_mul_sub_one_final
#print axioms OGMWeighted.a_add_e
#print axioms OGMWeighted.a_add_e_one
#print axioms OGMWeighted.ogmACoeff_self_zero
#print axioms OGMWeighted.A_eq_B_mul_theta
#print axioms OGMWeighted.A_mul_one_sub_inv
#print axioms OGMWeighted.A_sub_B_eq_A_prev
#print axioms OGMWeighted.A_div_theta_eq_B
#print axioms OGMWeighted.B_pos
#print axioms OGMWeighted.weightedRecurrence

-- RootIsolation.Effective
#print axioms RootIsolation.Effective.squarefree_parts_eq
#print axioms RootIsolation.Effective.rootMultiplicity_div_gcd_eq_one
#print axioms RootIsolation.Effective.derivative_not_isRoot_div_gcd
#print axioms RootIsolation.Effective.squarefreePart_map
#print axioms RootIsolation.Effective.squarefreePart_isCoprime
#print axioms RootIsolation.Effective.bezoutNormalizer
#print axioms RootIsolation.Effective.bezoutA
#print axioms RootIsolation.Effective.bezoutB
#print axioms RootIsolation.Effective.bezoutNormalizer_mul_gcd
#print axioms RootIsolation.Effective.bezoutIdentity
#print axioms RootIsolation.Effective.A
#print axioms RootIsolation.Effective.B
#print axioms RootIsolation.Effective.A_mul_squarefreePart_add_B_mul_derivative
#print axioms RootIsolation.Effective.bezoutIdentity_map
#print axioms RootIsolation.Effective.rootBound
#print axioms RootIsolation.Effective.coefficientBound
#print axioms RootIsolation.Effective.curvatureBound
#print axioms RootIsolation.Effective.epsilon
#print axioms RootIsolation.Effective.gridStep
#print axioms RootIsolation.Effective.one_le_rootBound
#print axioms RootIsolation.Effective.one_le_coefficientBound
#print axioms RootIsolation.Effective.one_le_curvatureBound
#print axioms RootIsolation.Effective.rootBound_spec
#print axioms RootIsolation.Effective.rootBound_norm_spec
#print axioms RootIsolation.Effective.coefficientBound_spec
#print axioms RootIsolation.Effective.curvatureBound_spec
#print axioms RootIsolation.Effective.epsilon_pos
#print axioms RootIsolation.Effective.gridStep_pos
#print axioms RootIsolation.Effective.squarefreePart_derivative_ne_zero
#print axioms RootIsolation.Effective.roots_separated
#print axioms RootIsolation.Effective.eq_of_roots_mem_same_filteredInterval
#print axioms RootIsolation.Effective.existsUnique_root_of_mem_filteredInterval
#print axioms RootIsolation.Effective.intervals
#print axioms RootIsolation.Effective.every_simple_root_mem_filteredIntervals_eps_div_two
#print axioms RootIsolation.Effective.every_squarefreePart_root_mem_intervals
#print axioms RootIsolation.Effective.every_root_mem_intervals
#print axioms RootIsolation.Effective.no_partitionPoint_mem_consecutive_open
#print axioms RootIsolation.Effective.consecutivePairs_eq_of_open_overlap
#print axioms RootIsolation.Effective.eq_of_mem_intervals_of_common_point
#print axioms RootIsolation.Effective.disjoint_intervals_of_ne

-- OGMVerified
#print axioms OGMVerified.Y
#print axioms OGMVerified.Eta
#print axioms OGMVerified.Y_succ
#print axioms OGMVerified.Eta_succ
#print axioms OGMVerified.Z
#print axioms OGMVerified.A
#print axioms OGMVerified.B
#print axioms OGMVerified.A_succ
#print axioms OGMVerified.A_div_theta
#print axioms OGMVerified.Z_succ
#print axioms OGMVerified.V
#print axioms OGMVerified.V_succ
#print axioms OGMVerified.Y_weighted
#print axioms OGMVerified.query
#print axioms OGMVerified.grad
#print axioms OGMVerified.Y_query
#print axioms OGMVerified.Y_shift
#print axioms OGMVerified.actual_upper_bound

-- Operational OGM risk and minimax upper bounds.
#print axioms OGMVerified.coordinates
#print axioms OGMVerified.coordinates_recover
#print axioms OGMVerified.lossSet_upper
#print axioms OGMVerified.risk_upper
#print axioms OGMVerified.coordinates_mem_memory
#print axioms OGMVerified.value_upper
#print axioms OGMVerified.coordinates_mem_memory_one_query
#print axioms OGMVerified.value_upper_one_query

-- Smooth/ConstrainedConjugateRegularity
#print axioms ConstrainedConjugate.strong_support
#print axioms ConstrainedConjugate.maximizers_monotone
#print axioms ConstrainedConjugate.maximizers_lipschitz
#print axioms ConstrainedConjugate.value
#print axioms ConstrainedConjugate.value_ge
#print axioms ConstrainedConjugate.value_support
#print axioms ConstrainedConjugate.value_remainder
#print axioms ConstrainedConjugate.value_convex
#print axioms ConstrainedConjugate.value_hasGradientAt
#print axioms ConstrainedConjugate.maximizer_unique
#print axioms ConstrainedConjugate.exists_maximizer
#print axioms ConstrainedConjugate.exists_smooth_conjugate

-- GJP/Elimination
#print axioms GJP.matrixSymm
#print axioms GJP.borderedMatrix
#print axioms GJP.borderedMatrix_posSemidef_iff
#print axioms GJP.equation15Matrix
#print axioms GJP.equation15_schur
#print axioms GJP.posSemidef_eq_zero_of_diagonal
#print axioms GJP.matrixSymm_transpose
#print axioms GJP.matrixSymm_congruence
#print axioms GJP.outer_congruence
#print axioms GJP.colSum_eq
#print axioms GJP.reducedSlack
#print axioms GJP.equation15_congruence
#print axioms GJP.equation15_reduced_iff
#print axioms GJP.UnitLower
#print axioms GJP.UnitLower.det_eq_one
#print axioms GJP.UnitLower.isUnit
#print axioms GJP.lower_mul_diag
#print axioms GJP.UnitLower.inv
#print axioms GJP.UnitLower.mul
#print axioms GJP.matrixSymm_injective_lower
#print axioms GJP.transformed_lower
#print axioms GJP.transformed_diag
#print axioms GJP.reducedSlack_diag
#print axioms GJP.equation15_diagonal_necessary
#print axioms GJP.equation15_tight_slack_zero
#print axioms GJP.equation15_tight_unique

-- GJP/Completion
#print axioms GJP.triangularCompletion
#print axioms GJP.triangularCompletion_lower
#print axioms GJP.triangularCompletion_diag
#print axioms GJP.triangularCompletion_zero_row
#print axioms GJP.triangularCompletion_slack
#print axioms GJP.exists_unitLower_solution
#print axioms GJP.diagonal_inequality_zero
#print axioms GJP.upper_zero_column
#print axioms GJP.equation15_exists_of_diagonal
#print axioms GJP.equation15_exists_iff_diagonal

-- GJP/TriangularOrder
#print axioms GJP.lower_comparison
#print axioms GJP.upper_comparison
#print axioms GJP.upper_zero_column_of_colsum
#print axioms GJP.upper_exists_solution_bounded

-- Smooth/DroriCoordinates
#print axioms SmoothDrori.hardX_apply
#print axioms SmoothDrori.hardG_apply
#print axioms SmoothDrori.hardG_inner
#print axioms SmoothDrori.hardG_inner_hardX
#print axioms SmoothDrori.hardG_inner_hardG_ne
#print axioms SmoothDrori.hardF_sub_norm
#print axioms SmoothDrori.zetaStar_antitone_bounded
#print axioms SmoothDrori.hardG_norm_sub_sq
#print axioms SmoothDrori.hardData_interpolation
#print axioms SmoothDrori.exists_hardData_interpolant

-- Smooth/DroriRadius
#print axioms SmoothDrori.zetaStar_step_mul
#print axioms SmoothDrori.zetaStar_last_mul
#print axioms SmoothDrori.zetaStar_square_div_step
#print axioms SmoothDrori.zetaStar_square_div_last
#print axioms SmoothDrori.zetaStar_weighted_sum
#print axioms SmoothDrori.hardX_minimizer_norm_sq_sum
#print axioms SmoothDrori.hardX_minimizer_norm

-- Smooth/DroriOracle
#print axioms SmoothDrori.hardX_zero
#print axioms SmoothDrori.Space
#print axioms SmoothDrori.orthant
#print axioms SmoothDrori.hardDual
#print axioms SmoothDrori.orthant_closed
#print axioms SmoothDrori.orthant_convex
#print axioms SmoothDrori.hardG_mem_orthant
#print axioms SmoothDrori.hardDual_strongConvex
#print axioms SmoothDrori.hardDual_continuous
#print axioms SmoothDrori.hardDual_support
#print axioms SmoothDrori.hardDual_contact
#print axioms SmoothDrori.exists_orthant_hardGradient
#print axioms SmoothDrori.hardGradient
#print axioms SmoothDrori.hardFunction
#print axioms SmoothDrori.hardGradient_spec
#print axioms SmoothDrori.hardGradient_at_data
#print axioms SmoothDrori.hardFunction_at_data
#print axioms SmoothDrori.hardFunction_minimizer
#print axioms SmoothDrori.hardInstance
#print axioms SmoothDrori.prefixSpace
#print axioms SmoothDrori.prefixSpace_mono
#print axioms SmoothDrori.hardFunction_lower_on_prefix

-- Smooth/DroriTail
#print axioms DroriTail.prefixSum
#print axioms DroriTail.base
#print axioms DroriTail.B
#print axioms DroriTail.B_eq_base
#print axioms DroriTail.prefixSum_nonneg
#print axioms DroriTail.prefixSum_mono
#print axioms DroriTail.base_step
#print axioms DroriTail.scalar_tail_bound
#print axioms DroriTail.candidate
#print axioms DroriTail.candidate_nonneg
#print axioms DroriTail.base_le_of_prefixSum_le_one
#print axioms DroriTail.base_candidate_small
#print axioms DroriTail.base_candidate_large
#print axioms DroriTail.candidate_base_bound_small_sum
#print axioms DroriTail.candidate_base_bound_large_sum

-- Smooth/DroriDualFormula
#print axioms SmoothDrori.hardShift
#print axioms SmoothDrori.hardShift_apply
#print axioms SmoothDrori.hardHi_eq_shift
#print axioms SmoothDrori.hardScale
#print axioms SmoothDrori.hardUnscale
#print axioms SmoothDrori.hardUnscale_apply
#print axioms SmoothDrori.hardUnscale_hardScale
#print axioms SmoothDrori.hardScale_hardUnscale
#print axioms SmoothDrori.hardScale_nonneg
#print axioms SmoothDrori.hardUnscale_mem_orthant
#print axioms SmoothDrori.hardUnscale_norm_sq
#print axioms SmoothDrori.hardShift_inner_unscale
#print axioms SmoothDrori.hardHi_unscale

-- Smooth/DroriGeometry
#print axioms SmoothDrori.hardX_mem_prefix
#print axioms SmoothDrori.hardG_mem_prefix
#print axioms SmoothDrori.eq_zero_of_mem_prefix_zero
#print axioms SmoothDrori.hardGradient_prefix_zero
#print axioms SmoothDrori.hardFunction_minimum_zero
#print axioms SmoothDrori.hardFunction_terminal_lower

-- Smooth/DroriTailGeometry
#print axioms DroriTail.quad
#print axioms DroriTail.prefixQuad
#print axioms DroriTail.tailQuad
#print axioms DroriTail.quad_split
#print axioms DroriTail.quad_candidate
#print axioms DroriTail.tailQuad_nonneg
#print axioms DroriTail.quad_candidate_zero_le
#print axioms SmoothDrori.inner_unscale_candidate
#print axioms SmoothDrori.hardDual_unscale_ge
#print axioms SmoothDrori.hardDual_unscale_eq_piece
#print axioms SmoothDrori.hardUnscale_candidate_mem_prefix
#print axioms SmoothDrori.hardGradient_eq_tail_candidate

-- Smooth/DroriTailCost
#print axioms DroriTail.prefixSum_succ
#print axioms DroriTail.B_at_next
#print axioms DroriTail.candidate_cost_large_coordinate
#print axioms DroriTail.candidate_cost_small_coordinate

-- Smooth/DroriLowerBound
#print axioms SmoothDrori.zetaStar_antitone_through_zero
#print axioms SmoothDrori.hardDual_candidate_small_sum
#print axioms SmoothDrori.hardDual_candidate_large_sum
#print axioms SmoothDrori.hardGradient_zero_chain
#print axioms SmoothDrori.hardInstance_all_linear_history_lower
#print axioms SmoothDrori.actualLossSet_has_sharp_lower_witness

-- Smooth/DroriOperational
#print axioms SmoothDrori.operational_risk_lower
#print axioms SmoothDrori.operational_value_lower
#print axioms SmoothDrori.operational_value_eq
#print axioms SmoothDrori.operational_ogm_risk_eq
#print axioms SmoothDrori.operational_thresholds_eq_ray
#print axioms SmoothDrori.operational_no_gain_beyond_one
#print axioms SmoothDrori.operational_no_strict_gain_beyond_one
#print axioms SmoothDrori.operational_value_one_query_zero_memory
#print axioms SmoothDrori.operational_value_one_query
#print axioms SmoothDrori.operational_thresholds_one_query

-- RootIsolation/ExecutablePolynomial
#print axioms RootIsolation.Executable.Poly
#print axioms RootIsolation.Executable.denote
#print axioms RootIsolation.Executable.denote_nil
#print axioms RootIsolation.Executable.ofCoeffList_append
#print axioms RootIsolation.Executable.denote_cons
#print axioms RootIsolation.Executable.degree_denote_lt_length
#print axioms RootIsolation.Executable.degree_denote_cons
#print axioms RootIsolation.Executable.leadingCoeff_denote_cons
#print axioms RootIsolation.Executable.trim
#print axioms RootIsolation.Executable.denote_trim
#print axioms RootIsolation.Executable.trim_head_ne_zero
#print axioms RootIsolation.Executable.trim_eq_nil_iff
#print axioms RootIsolation.Executable.natDegree
#print axioms RootIsolation.Executable.leadingCoeff
#print axioms RootIsolation.Executable.natDegree_refines
#print axioms RootIsolation.Executable.leadingCoeff_refines
#print axioms RootIsolation.Executable.add
#print axioms RootIsolation.Executable.sub
#print axioms RootIsolation.Executable.scale
#print axioms RootIsolation.Executable.monomial
#print axioms RootIsolation.Executable.denote_add
#print axioms RootIsolation.Executable.denote_sub
#print axioms RootIsolation.Executable.denote_scale
#print axioms RootIsolation.Executable.denote_replicate_zero
#print axioms RootIsolation.Executable.denote_monomial
#print axioms RootIsolation.Executable.shift
#print axioms RootIsolation.Executable.denote_shift
#print axioms RootIsolation.Executable.mul
#print axioms RootIsolation.Executable.denote_mul
#print axioms RootIsolation.Executable.degree
#print axioms RootIsolation.Executable.degree_refines
#print axioms RootIsolation.Executable.monicDivMod
#print axioms RootIsolation.Executable.monicDivMod_refines
#print axioms RootIsolation.Executable.monicDivMod_quotient
#print axioms RootIsolation.Executable.monicDivMod_remainder
#print axioms RootIsolation.Executable.normalized_monic
#print axioms RootIsolation.Executable.divMod
#print axioms RootIsolation.Executable.divMod_quotient
#print axioms RootIsolation.Executable.divMod_remainder
#print axioms RootIsolation.Executable.divMod_refines
#print axioms RootIsolation.Executable.denote_surjective
#print axioms RootIsolation.Executable.divMod_reconstructs
#print axioms RootIsolation.Executable.divMod_remainder_lt
#print axioms RootIsolation.Executable.gcd
#print axioms RootIsolation.Executable.gcd_refines
#print axioms RootIsolation.Executable.xgcdAux
#print axioms RootIsolation.Executable.xgcdAux_refines
#print axioms RootIsolation.Executable.xgcd
#print axioms RootIsolation.Executable.gcdA
#print axioms RootIsolation.Executable.gcdB
#print axioms RootIsolation.Executable.denote_one
#print axioms RootIsolation.Executable.xgcd_refines
#print axioms RootIsolation.Executable.gcdA_refines
#print axioms RootIsolation.Executable.gcdB_refines
#print axioms RootIsolation.Executable.gcd_bezout
#print axioms RootIsolation.Executable.coeff
#print axioms RootIsolation.Executable.coeff_refines
#print axioms RootIsolation.Executable.derivative
#print axioms RootIsolation.Executable.derivative_refines
#print axioms RootIsolation.Executable.eval
#print axioms RootIsolation.Executable.eval_foldl
#print axioms RootIsolation.Executable.eval_refines

-- RootIsolation/ExecutableIsolation
#print axioms RootIsolation.Executable.squarefreePart
#print axioms RootIsolation.Executable.squarefreePart_refines
#print axioms RootIsolation.Executable.bezoutA
#print axioms RootIsolation.Executable.bezoutB
#print axioms RootIsolation.Executable.A
#print axioms RootIsolation.Executable.B
#print axioms RootIsolation.Executable.A_refines
#print axioms RootIsolation.Executable.B_refines
#print axioms RootIsolation.Executable.rootBound
#print axioms RootIsolation.Executable.rootBound_refines
#print axioms RootIsolation.Executable.coeffAbsSum
#print axioms RootIsolation.Executable.coeffAbsSum_refines
#print axioms RootIsolation.Executable.coefficientBound
#print axioms RootIsolation.Executable.curvatureBound
#print axioms RootIsolation.Executable.epsilon
#print axioms RootIsolation.Executable.gridStep
#print axioms RootIsolation.Executable.coefficientBound_refines
#print axioms RootIsolation.Executable.curvatureBound_refines
#print axioms RootIsolation.Executable.epsilon_refines
#print axioms RootIsolation.Executable.gridStep_refines
#print axioms RootIsolation.Executable.filteredIntervals
#print axioms RootIsolation.Executable.filteredIntervals_refines
#print axioms RootIsolation.Executable.intervals
#print axioms RootIsolation.Executable.intervals_refines
#print axioms RootIsolation.Executable.every_root_mem_intervals
#print axioms RootIsolation.Executable.existsUnique_root_of_mem_intervals
#print axioms RootIsolation.Executable.disjoint_intervals_of_ne
#print axioms RootIsolation.Executable.isolate
#print axioms RootIsolation.Executable.isolate_none_iff
#print axioms RootIsolation.Executable.isolate_some_iff
#print axioms RootIsolation.Executable.isolate_spec

-- GJP/FactorProjection
#print axioms GJP.TCAdmissible
#print axioms GJP.UnitLower.row_sum_le_one
#print axioms GJP.TCAdmissible.colsum_nonneg
#print axioms GJP.TCAdmissible.exists_b
#print axioms GJP.upper_prefix_bound
#print axioms GJP.upper_terminal_row

-- GJP/ScalarProjection
#print axioms GJP.projected_square_bound
#print axioms GJP.projected_fraction_bound
#print axioms GJP.projected_terminal_bound
#print axioms GJP.projected_fraction_equality
#print axioms GJP.projected_terminal_equality

-- GJP/Projection
#print axioms GJP.flowDelta
#print axioms GJP.flowDelta_simplex
#print axioms GJP.flowDelta_prefix_bound
#print axioms GJP.equation15_flow_bound
#print axioms GJP.equation15_projects_simplex
#print axioms GJP.equation15_rate_lower

#print axioms GJP.UnitLower.eq_one_of_row_sum

#print axioms GJP.upper_prefix_tight_zero

#print axioms GJP.deltaStar_pos

#print axioms GJP.equation15_optimal_equalities

#print axioms GJP.optimalFactorDiag

#print axioms GJP.optimalFactorT

#print axioms GJP.upper_successor_entry

#print axioms GJP.equation15_optimal_factors

#print axioms GJP.optimalFactorDiag_pos

#print axioms GJP.optimalFactorT_upper

#print axioms GJP.optimalFactorT_diag

#print axioms GJP.optimalFactorT_isUnit

#print axioms GJP.equation15_optimal_method_unique

#print axioms GJP.continuous_partial_sum

#print axioms GJP.simplex_coordinate_le_one

#print axioms GJP.simplex_polynomial_bound

#print axioms GJP.simplex_terminal_bound

#print axioms GJP.simplex_Phi_le_of_polynomial

#print axioms GJP.simplex_limit_eq_deltaStar

#print axioms GJP.simplex_stability

#print axioms GJP.projected_square_bound_with_mass

#print axioms GJP.projected_terminal_bound_with_mass

#print axioms GJP.mass_stability

#print axioms GJP.equation15_mass_stability

#print axioms GJP.offdiag_entry_lower

#print axioms GJP.TCAdmissible.upper_entry_bounds

#print axioms GJP.UnitLower.entry_bounds

#print axioms GJP.factors_bounded_of_mass

#print axioms GJP.isClosed_posSemidef

#print axioms GJP.matrix_entry_tendsto

#print axioms GJP.limit_eq_of_forall

#print axioms GJP.UnitLower.of_tendsto

#print axioms GJP.TCAdmissible.of_tendsto

#print axioms GJP.continuous_equation15Matrix

#print axioms GJP.equation15_psd_of_tendsto

#print axioms GJP.equation15_factor_stability

#print axioms GJP.equation15_limit_certificate

#print axioms GJP.equation15_approaching_method_unique

#print axioms GJP.sourceMatrix

#print axioms GJP.sourceMatrix_entry_lt

#print axioms GJP.sourceMatrix_injective

#print axioms GJP.sourceMatrix_unitLower

#print axioms GJP.run_sourceMatrix

#print axioms GJP.sourceMatrix_coordinates_injective

#print axioms GJP.scaled_hasGradient

#print axioms GJP.rescaleInstance

#print axioms GJP.rescale_trajectory

#print axioms GJP.rescale_terminalLoss

#print axioms GJP.uniform_bound_rescale

#print axioms GJP.normalized_radius

#print axioms GJP.normalized_benchmark

#print axioms GJP.uniform_bound_normalized

#print axioms GJP.sourceMatrix_normalized

#print axioms GJP.compactDualMatrix

#print axioms GJP.CompactDualFeasible

#print axioms GJP.compactDualMatrix_factor

#print axioms GJP.CompactDualFeasible.factor

#print axioms GJP.compactDual_rate_lower

#print axioms GJP.compactDual_limit_certificate

#print axioms GJP.compactDual_approaching_method_unique

#print axioms GJP.DDMZ

#print axioms GJP.DDMZ.diag_nonneg

#print axioms GJP.DDMZ.zero_pivot

#print axioms GJP.border

#print axioms GJP.border_cast_cast

#print axioms GJP.border_cast_last

#print axioms GJP.border_last_cast

#print axioms GJP.border_last_last

#print axioms GJP.border_mul

#print axioms GJP.matrix_eq_border

#print axioms GJP.border_upper

#print axioms GJP.border_unitLower

#print axioms GJP.lastSchur

#print axioms GJP.lastSchur_rows

#print axioms GJP.lastSchur_cols

#print axioms GJP.DDMZ.schur

#print axioms GJP.TCFactor

#print axioms GJP.TCFactor.border

#print axioms GJP.exists_TC_factor

#print axioms GJP.UnitLower.inverse_nonneg

#print axioms GJP.TCFactor.colsum_nonneg

#print axioms GJP.exists_TC_factor_nonnegative

#print axioms GJP.exists_TC_admissible

#print axioms GJP.TCFactor.isUnit_upper

#print axioms GJP.TCFactor.diag_pos

#print axioms GJP.TCFactor.upper_inverse_nonneg

#print axioms GJP.TCFactor.unique

#print axioms SmoothDrori.scalar_zero_query_witness

#print axioms SmoothDrori.operational_risk_zero_query

#print axioms SmoothDrori.operational_value_zero_query

#print axioms SmoothDrori.operational_thresholds_zero_query

#print axioms SmoothDrori.operational_value_eq_all_queries

#print axioms MemorySemialgebraic.AffineElimination.Rel

#print axioms MemorySemialgebraic.AffineElimination.rel_le

#print axioms MemorySemialgebraic.AffineElimination.rel_of_lt

#print axioms MemorySemialgebraic.AffineElimination.rel_trans

#print axioms MemorySemialgebraic.AffineElimination.rel_sub

#print axioms MemorySemialgebraic.AffineElimination.rel_mul_pos

#print axioms MemorySemialgebraic.AffineElimination.finite_bounds_iff

#print axioms MemorySemialgebraic.AffineElimination.positive_affine_iff

#print axioms MemorySemialgebraic.AffineElimination.negative_affine_iff

#print axioms MemorySemialgebraic.AffineElimination.opposing_bounds_iff

#print axioms MemorySemialgebraic.AffineElimination.feasible_iff

#print axioms MemorySemialgebraic.SymbolicQE.Expr

#print axioms MemorySemialgebraic.SymbolicQE.Expr.sub

#print axioms MemorySemialgebraic.SymbolicQE.Expr.denote

#print axioms MemorySemialgebraic.SymbolicQE.Expr.evalReal

#print axioms MemorySemialgebraic.SymbolicQE.Expr.evalRat

#print axioms MemorySemialgebraic.SymbolicQE.Expr.evalReal_refines

#print axioms MemorySemialgebraic.SymbolicQE.Expr.evalReal_cast

#print axioms MemorySemialgebraic.SymbolicQE.Expr.denote_surjective

#print axioms MemorySemialgebraic.SymbolicQE.Formula

#print axioms MemorySemialgebraic.SymbolicQE.Formula.evalReal

#print axioms MemorySemialgebraic.SymbolicQE.Formula.evalRat

#print axioms MemorySemialgebraic.SymbolicQE.Formula.toQF

#print axioms MemorySemialgebraic.SymbolicQE.Formula.toQF_refines

#print axioms MemorySemialgebraic.SymbolicQE.Formula.evalRat_refines

#print axioms MemorySemialgebraic.SymbolicQE.Formula.relation

#print axioms MemorySemialgebraic.SymbolicQE.Formula.relation_eval

#print axioms MemorySemialgebraic.SymbolicQE.Formula.all

#print axioms MemorySemialgebraic.SymbolicQE.Formula.all_eval

#print axioms MemorySemialgebraic.SymbolicQE.Formula.any

#print axioms MemorySemialgebraic.SymbolicQE.Formula.any_eval

#print axioms MemorySemialgebraic.SymbolicQE.Constraint

#print axioms MemorySemialgebraic.SymbolicQE.Constraint.holds

#print axioms MemorySemialgebraic.SymbolicQE.Constraint.constantCondition

#print axioms MemorySemialgebraic.SymbolicQE.Constraint.pairCondition

#print axioms MemorySemialgebraic.SymbolicQE.Constraint.constantCondition_eval

#print axioms MemorySemialgebraic.SymbolicQE.Constraint.pairCondition_eval

#print axioms MemorySemialgebraic.SymbolicQE.eliminateConjunction

#print axioms MemorySemialgebraic.SymbolicQE.eliminateConjunction_correct

#print axioms MemorySemialgebraic.SymbolicQE.eliminateConjunction_toQF

#print axioms MemorySemialgebraic.SymbolicQE.eliminateDNF

#print axioms MemorySemialgebraic.SymbolicQE.eliminateDNF_correct

#print axioms MemorySemialgebraic.SymbolicQE.negateConstraint

#print axioms MemorySemialgebraic.SymbolicQE.negateConstraint_holds

#print axioms MemorySemialgebraic.SymbolicQE.AffineFormula

#print axioms MemorySemialgebraic.SymbolicQE.AffineFormula.evalReal

#print axioms MemorySemialgebraic.SymbolicQE.AffineFormula.equalZero

#print axioms MemorySemialgebraic.SymbolicQE.AffineFormula.equalZero_eval

#print axioms MemorySemialgebraic.SymbolicQE.clausesHold

#print axioms MemorySemialgebraic.SymbolicQE.clausesHold_nil

#print axioms MemorySemialgebraic.SymbolicQE.clausesHold_singleton

#print axioms MemorySemialgebraic.SymbolicQE.clausesHold_append

#print axioms MemorySemialgebraic.SymbolicQE.meetClauses

#print axioms MemorySemialgebraic.SymbolicQE.meetClauses_correct

#print axioms MemorySemialgebraic.SymbolicQE.toDNF

#print axioms MemorySemialgebraic.SymbolicQE.toDNF_correct

#print axioms MemorySemialgebraic.SymbolicQE.eliminate

#print axioms MemorySemialgebraic.SymbolicQE.eliminate_correct

#print axioms MemorySemialgebraic.SymbolicQE.eliminate_toQF

#print axioms RootIsolation.Executable.squarefreePart_aeval_iff

#print axioms RootIsolation.Executable.squarefreePart_derivative_ne_zero

#print axioms RootIsolation.Executable.gcd_denote_ne_zero

#print axioms RootIsolation.Executable.squarefree_gcd_aeval_iff

#print axioms RootIsolation.Executable.roots_eq_of_mem_interval

#print axioms RootIsolation.Executable.open_mem_intervals_sign

#print axioms RootIsolation.Executable.open_mem_intervals_endpoints_nonzero

#print axioms RootIsolation.Executable.exists_root_of_eval_product_neg

#print axioms RootIsolation.Executable.rootZero

#print axioms RootIsolation.Executable.rootZero_correct

#print axioms RootIsolation.Executable.rationalSign

#print axioms RootIsolation.Executable.realSign

#print axioms RootIsolation.Executable.realSign_cast

#print axioms RootIsolation.Executable.realSign_zero

#print axioms RootIsolation.Executable.realSign_eq_of_no_root

#print axioms RootIsolation.Executable.rootSign

#print axioms RootIsolation.Executable.rootSign_correct

#print axioms GJPDual.actual_bound_approximate_certificate

#print axioms GJPDual.normalized_approaching_certificates

#print axioms GJP.sharp_methods_equal

#print axioms GJP.actual_method_unique

#print axioms GJP.operational_method_unique

#print axioms GJP.operational_coordinates_unique

#print axioms GJP.operational_optimal_iff

#print axioms ConicDuality.imageCone

#print axioms ConicDuality.imageCone_zero

#print axioms ConicDuality.imageCone_smul

#print axioms ConicDuality.imageCone_convex

#print axioms ConicDuality.imageCone_interior_of_positive_annihilator

#print axioms ConicDuality.approximate_dual

#print axioms GJPDual.positive_annihilator_zero

#print axioms GJPDual.Q

#print axioms GJPDual.Index

#print axioms GJPDual.symmetricSpace

#print axioms GJPDual.SymBlock

#print axioms GJPDual.Off

#print axioms GJPDual.E

#print axioms GJPDual.Y

#print axioms GJPDual.linearMatrix

#print axioms GJPDual.linearMatrix_symm

#print axioms GJPDual.linearMatrix_add

#print axioms GJPDual.linearMatrix_smul

#print axioms GJPDual.mapLinear

#print axioms GJPDual.conicMap

#print axioms GJPDual.cost

#print axioms GJPDual.constantMatrix

#print axioms GJPDual.constantMatrix_symm

#print axioms GJPDual.constant

#print axioms GJPDual.ConePred

#print axioms GJPDual.conePred_closed

#print axioms GJPDual.cone

#print axioms GJPDual.mem_cone

#print axioms GJPDual.matrixSymm_symm

#print axioms GJPDual.matrixSymm_of_symm

#print axioms GJPDual.symmetrize

#print axioms GJPDual.matrixInjection

#print axioms GJPDual.offInjection

#print axioms GJPDual.rowInjection

#print axioms GJPDual.colInjection

#print axioms GJPDual.matrixFunctional

#print axioms GJPDual.gram

#print axioms GJPDual.offWeight

#print axioms GJPDual.rowWeight

#print axioms GJPDual.colWeight

#print axioms GJPDual.matrixFunctional_eq

#print axioms GJPDual.linear_pi_eq_sum

#print axioms GJPDual.functional_eq

#print axioms GJPDual.gram_symm

#print axioms GJPDual.gram_psd

#print axioms GJPDual.rowWeight_nonneg

#print axioms GJPDual.colWeight_nonneg

#print axioms GJPDual.offWeight_nonneg

#print axioms GJPDual.slack_matrix

#print axioms GJPDual.bordered_rate_pos

#print axioms GJPDual.compact_of_cone

#print axioms GJP.additiveHistory

#print axioms GJP.additiveHistory_strict

#print axioms GJP.sourceMatrix_additiveHistory

#print axioms GJP.additiveHistory_sourceMatrix

#print axioms GJP.gram_v_none

#print axioms GJP.gram_v_some

#print axioms GJP.shiftedSite

#print axioms GJP.shiftedSite_none

#print axioms GJP.shiftedSite_some

#print axioms GJP.gram_shiftedSite

#print axioms GJP.gramIndex

#print axioms GJP.gramOfBlock

#print axioms GJP.gramOfBlock_psd

#print axioms GJP.shiftedPairing

#print axioms GJP.shiftedSite_pairing

#print axioms GJP.shifted_interpolation_identity

#print axioms GJP.feasible_of_shifted_coordinates

#print axioms GJP.shifted_coordinates_actual_loss

#print axioms GJPDual.matrix_pair_symm

#print axioms GJPDual.matrixFunctional_bordered

#print axioms GJPDual.matrixFunctional_linearMatrix_single

#print axioms GJPDual.matrixFunctional_radius

#print axioms GJPDual.matrixFunctional_constant

#print axioms GJPDual.functional_parts

#print axioms GJPDual.functional_radius

#print axioms GJPDual.functional_constant

#print axioms GJPDual.offVector_single

#print axioms GJPDual.offVector_diagonal

#print axioms GJPDual.functional_single_offdiag

#print axioms GJPDual.functional_single_diag

#print axioms GJPDual.compatible_apply

#print axioms GJPDual.compatible_radius

#print axioms GJPDual.compatible_diagonal

#print axioms GJPDual.compatible_pair

#print axioms GJPDual.positive_functional_actual_loss

#print axioms GJPDual.positive_functional_bound

#print axioms GJP.UnitLower.first_row

#print axioms GJP.UnitLower.first_row_sum

#print axioms GJP.upper_mulVec_first_support

#print axioms GJP.TCFactor.row_normalized_pivots

#print axioms GJP.normalizeZeroRows

#print axioms GJP.TCFactor.normalize_zero_rows

#print axioms GJP.exists_TC_row_normalized

#print axioms GJP.TCFactor.column_normalized

#print axioms GJP.operational_zero_memory_gap

#print axioms GJP.operational_strict_gain

#print axioms GJP.operational_strict_gain_iff

#print axioms GJP.operational_threshold_gain_iff

#print axioms GJPDual.psd_column_zero

#print axioms GJPDual.triangular_positive_kernel

#print axioms RootIsolation.Executable.partition_cover_of_abs_le

#print axioms RootIsolation.Executable.grid_cell_roots_unique

#print axioms RootIsolation.Executable.rootfree_endpoint_of_unique

#print axioms RootIsolation.Executable.signSamples

#print axioms RootIsolation.Executable.exists_rootfree_sample

#print axioms RootIsolation.Executable.realSign_eq_of_no_root_uIcc

#print axioms RootIsolation.Executable.exists_sample_same_signs

#print axioms RootIsolation.Executable.familyProduct

#print axioms RootIsolation.Executable.familyProduct_ne_zero

#print axioms RootIsolation.Executable.familyProduct_covers

#print axioms MemorySemialgebraic.SymbolicQE.Expr.compileUnivariate

#print axioms MemorySemialgebraic.SymbolicQE.Expr.compileUnivariate_correct

#print axioms MemorySemialgebraic.SymbolicQE.realSign_eq_neg_one_iff

#print axioms MemorySemialgebraic.SymbolicQE.realSign_eq_zero_iff

#print axioms MemorySemialgebraic.SymbolicQE.realSign_eq_one_iff

#print axioms MemorySemialgebraic.SymbolicQE.Formula.atomPolys

#print axioms MemorySemialgebraic.SymbolicQE.Formula.evalSigns

#print axioms MemorySemialgebraic.SymbolicQE.Formula.evalSigns_correct

#print axioms MemorySemialgebraic.SymbolicQE.Formula.decideExists

#print axioms MemorySemialgebraic.SymbolicQE.Formula.decideExists_correct

#print axioms MemorySemialgebraic.SymbolicQE.Formula.decideExists_toQF

#print axioms MemorySemialgebraic.SymbolicQE.Formula.decideForall

#print axioms MemorySemialgebraic.SymbolicQE.Formula.decideForall_correct

#print axioms SmoothGramModel.padVector

#print axioms SmoothGramModel.sum_padded

#print axioms SmoothGramModel.padVector_inner

#print axioms SmoothGramModel.exists_gram_in_larger_dimension

#print axioms SmoothGramModel.realize_feasible_in_dimension

#print axioms SmoothGramModel.actualLossSet_eq_fixed_dimension

#print axioms SmoothGramModel.uniform_bound_iff_fixed_dimension

#print axioms GJP.actual_method_unique_fixed_dimension

#print axioms GJP.sharp_methods_equal_fixed_dimension

#print axioms QuadraticSpectral.scalarLossSet

#print axioms QuadraticSpectral.lossSet_nonneg

#print axioms QuadraticSpectral.lossSet_radius_mono

#print axioms QuadraticSpectral.scalar_loss_of_squared_radius

#print axioms QuadraticSpectral.scalarLossSet_subset

#print axioms QuadraticSpectral.lossSet_eq_scalarLossSet

#print axioms QuadraticSpectral.historyLossSet_eq_scalarLossSet

#print axioms QuadraticSpectral.scalarLossSet_uniform_bound

#print axioms ProjectedOperational.feasible

#print axioms ProjectedOperational.loss

#print axioms ProjectedOperational.memory

#print axioms ProjectedOperational.zeroIncrement

#print axioms ProjectedOperational.zeroIncrement_mem

#print axioms ProjectedOperational.mem_memory_iff_projected

#print axioms ProjectedOperational.value_eq_inf_projected

#print axioms ProjectedOperational.mem_performance_iff_model

#print axioms ProjectedOperational.threshold_iff_value_lt

#print axioms ProjectedOperational.thresholds_eq_ray

#print axioms ProjectedOperational.thresholds_empty_iff

#print axioms ProjectedOperational.zero_loss_mem

#print axioms ProjectedOperational.feasible_nonneg

#print axioms ProjectedOperational.value_nonneg

#print axioms ProjectedOperational.bounded_value_bounds

#print axioms ProjectedOperational.bounded_value_finite

#print axioms ProjectedOperational.memory_saturated

#print axioms ProjectedOperational.unrestrictedValue

#print axioms ProjectedOperational.value_eq_unrestricted

#print axioms ProjectedOperational.least_sufficient_budget

#print axioms ProjectedOperational.strict_gain_iff

#print axioms ProjectedOperational.strict_gain_rational_threshold

#print axioms ProjectedOperational.bounded_thresholds_eq_ray

#print axioms Finset.prod_filter_or_eq_of_not

#print axioms Polynomial.sign_eval_map

#print axioms Polynomial.natDegree_C_sub_X

#print axioms Polynomial.exists_eq_C_mul_X_sub_C_of_natDegree_le_one

#print axioms Polynomial.IsRoot.exists_eq_pow_succ_mul

#print axioms Polynomial.rootMultiplicity_add_eq_left_of_dvd

#print axioms Polynomial.eval_mul_pos_of_natDegree_le_one_of_no_roots

#print axioms Polynomial.derivative_root_factors

#print axioms TauCeti.PolynomialRolle

#print axioms TauCeti.PolynomialRolle.of_forall

#print axioms TauCeti.PolynomialRolle.exists_derivative_root

#print axioms TauCeti.PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul

#print axioms TauCeti.PolynomialRolle.monotoneOn

#print axioms TauCeti.PolynomialRolle.antitoneOn

#print axioms TauCeti.PolynomialRolle.strictMonoOn

#print axioms TauCeti.PolynomialRolle.strictAntiOn

#print axioms Polynomial.derivativeSign

#print axioms Polynomial.derivativeSign_def

#print axioms Polynomial.derivativeSign_eq_one_iff

#print axioms Polynomial.derivativeSign_eq_neg_one_iff

#print axioms Polynomial.derivativeSign_eq_zero_iff

#print axioms Polynomial.derivativeSign_ne_zero

#print axioms Polynomial.derivativeSign_zero

#print axioms Polynomial.derivativeSign_index_zero

#print axioms Polynomial.derivativeSign_eq_zero

#print axioms Polynomial.derivativeSign_C

#print axioms Polynomial.derivativeSign_derivative

#print axioms Polynomial.derivativeSign_iterate_derivative

#print axioms Polynomial.thomEncoding

#print axioms Polynomial.thomEncoding_apply

#print axioms Polynomial.thomEncoding_def

#print axioms Polynomial.thomEncoding_eq_iff

#print axioms Polynomial.derivativeSign_const

#print axioms Polynomial.thomEncoding_succ_lt_natDegree

#print axioms Polynomial.exists_derivativeSign_ne

#print axioms Polynomial.exists_thomEncoding_ne

#print axioms Polynomial.derivativeSign_eq_on_Icc

#print axioms Polynomial.ordConnected_preimage_derivativeSign

#print axioms Polynomial.ordConnected_preimage_thomEncoding

#print axioms Polynomial.eq_of_derivativeSign_eq

#print axioms Polynomial.thomEncoding_injOn

#print axioms Polynomial.lt_iff_derivativeSign

#print axioms Polynomial.lt_iff_thomEncoding

#print axioms Polynomial.derivativeSign_succ_ne_zero

#print axioms Polynomial.thomEncoding_succ_ne_zero

#print axioms Polynomial.signRight

#print axioms Polynomial.signLeft

#print axioms Polynomial.signRight_def

#print axioms Polynomial.signLeft_def

#print axioms Polynomial.signRight_zero

#print axioms Polynomial.signLeft_zero

#print axioms Polynomial.signRight_C

#print axioms Polynomial.signLeft_C

#print axioms Polynomial.signRight_eq_sign_eval

#print axioms Polynomial.signLeft_eq_sign_eval

#print axioms Polynomial.signRight_add_eq_left_of_dvd

#print axioms Polynomial.signLeft_add_eq_left_of_dvd

#print axioms Polynomial.signRight_map

#print axioms Polynomial.signLeft_map

#print axioms Polynomial.signRight_eq_sign_eval_divByMonic

#print axioms Polynomial.signRight_eq_zero_iff

#print axioms Polynomial.signLeft_eq_zero_iff

#print axioms Polynomial.eval_ne_zero_of_sign_eq_signRight

#print axioms Polynomial.eval_ne_zero_of_sign_eq_signLeft

#print axioms Polynomial.signLeft_eq_signRight_of_even

#print axioms Polynomial.signLeft_eq_neg_signRight_of_odd

#print axioms Polynomial.signRight_mul

#print axioms Polynomial.signLeft_mul

#print axioms Polynomial.signRight_one

#print axioms Polynomial.signLeft_one

#print axioms Polynomial.signRight_neg

#print axioms Polynomial.signLeft_neg

#print axioms Polynomial.signRight_pow

#print axioms Polynomial.signLeft_pow

#print axioms Polynomial.exists_signLeft_signRight

#print axioms List.exists_signs_right

#print axioms List.exists_signs_left

#print axioms TauCeti.RealClosure.finrank_eq_one_of_odd

#print axioms TauCeti.RealClosure.finrank_ne_two_of_forall_isSquare

#print axioms TauCeti.RealClosure.isPGroup_two_algEquiv

#print axioms TauCeti.RealClosure.finrank_eq_one_of_isPGroup

#print axioms TauCeti.RealClosure.finrank_eq_one_of_isGalois_of_forall_isSquare

#print axioms RingPreordering.adjoin

#print axioms RingPreordering.mem_adjoin

#print axioms RingPreordering.le_adjoin

#print axioms RingPreordering.self_mem_adjoin

#print axioms RingPreordering.adjoin_le

#print axioms RingPreordering.adjoin_le_iff

#print axioms RingPreordering.exists_le_isOrdering

#print axioms RingPreordering.exists_le_isOrdering_mem

#print axioms RingPreordering.toRingCone

#print axioms RingPreordering.mem_toRingCone

#print axioms RingPreordering.linearOrder

#print axioms RingPreordering.isStrictOrderedRing

#print axioms RingPreordering.nonneg_iff

#print axioms RingPreordering.exists_linearOrder

#print axioms RingPreordering.sumSq

#print axioms RingPreordering.mem_sumSq

#print axioms IsSemireal.exists_linearOrder

#print axioms TauCeti.RealClosure.exists_nonneg_sq

#print axioms QuadraticAlgebra.isSquare

#print axioms TauCeti.RealClosure.finrank_eq_one_of_forall_isSquare

#print axioms TauCeti.RealClosure.isAlgClosed_of_forall_isSquare

#print axioms Polynomial.natDegree_le_two_of_irreducible

#print axioms nonneg_of_discrim_le_zero

#print axioms pos_of_nonneg_of_discrim_lt_zero

#print axioms Int.discrim_le_zero_of_nonneg_of_lt_abs

#print axioms Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd

#print axioms Int.discrim_emod_four

#print axioms discrim_eq_sq_of_two_eq_zero

#print axioms Polynomial.derivative_quadratic

#print axioms Polynomial.sq_derivative_quadratic_sub_mul_eq_C_discrim

#print axioms Polynomial.separable_quadratic_of_isUnit_discrim

#print axioms Polynomial.separable_quadratic_iff_discrim_ne_zero

#print axioms Polynomial.splits_quadratic_iff_exists_root

#print axioms Polynomial.splits_quadratic_iff_isSquare

#print axioms Polynomial.splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero

#print axioms Polynomial.splits_quadratic_of_discrim_eq_zero

#print axioms Polynomial.card_rootSet_quadratic_of_discrim_eq_zero

#print axioms TauCeti.quadratic_pos_iff_of_discrim_neg

#print axioms TauCeti.quadratic_neg_iff_of_discrim_neg

#print axioms TauCeti.irreducible_quadratic_iff_discrim_neg

#print axioms TauCeti.irreducible_quadratic_eval_pos_iff

#print axioms TauCeti.irreducible_quadratic_eval_neg_iff

#print axioms TauCeti.irreducible_quadratic_eval_pos_iff_leadingCoeff_pos

#print axioms TauCeti.irreducible_quadratic_eval_neg_iff_leadingCoeff_neg

#print axioms TauCeti.irreducible_quadratic_eval_mul_pos

#print axioms Polynomial.eval_mul_pos_of_no_roots

#print axioms Polynomial.exists_root_Icc_of_mul_nonpos

#print axioms Polynomial.exists_root_Icc

#print axioms Polynomial.exists_root_Ioo

#print axioms Polynomial.exists_root_Ioo_of_mul_neg

#print axioms Polynomial.intermediate_value_Icc

#print axioms Polynomial.intermediate_value_Icc'

#print axioms Finset.exists_right_gap

#print axioms Finset.exists_left_gap

#print axioms Finset.sum_jumps

#print axioms Polynomial.sign_eval_const

#print axioms Polynomial.signs_at_nonroot

#print axioms Polynomial.signs_at_root

#print axioms Polynomial.sign_eval_sub_sign_eval_eq_sum

#print axioms List.firstSign

#print axioms List.firstSign_nil

#print axioms List.firstSign_zero_cons

#print axioms List.firstSign_cons_of_ne_zero

#print axioms List.signVariations_cons

#print axioms TauCeti.Sturm.signVariationsAt

#print axioms TauCeti.Sturm.signVariationsAt_def

#print axioms TauCeti.Sturm.signVariationsAt_nil

#print axioms TauCeti.Sturm.signVariationsAt_singleton

#print axioms TauCeti.Sturm.signVariationsAt_cons

#print axioms TauCeti.Sturm.signVariationsAt_map_mul

#print axioms TauCeti.Sturm.signVariationsAt_eq_of_alternate

#print axioms TauCeti.Sturm.signVariationsAt_const

#print axioms TauCeti.Sturm.IsAlternating

#print axioms TauCeti.Sturm.IsAlternating.tail

#print axioms TauCeti.Sturm.IsAlternating.signVariationsAt_eq

#print axioms TauCeti.Sturm.IsAlternating.second_eval_ne_zero

#print axioms TauCeti.Sturm.IsAlternating.signVariationsAt_nonroot

#print axioms TauCeti.Sturm.IsAlternating.root_jump

#print axioms Polynomial.getD_getElem?_sturmSeq

#print axioms Polynomial.eq_neg_mod_of_getElem?_sturmSeq

#print axioms Polynomial.natDegree_lt_of_getElem?_sturmSeq

#print axioms Polynomial.natDegree_le_of_mem_sturmSeq

#print axioms TauCeti.Sturm.IsRemainder

#print axioms TauCeti.Sturm.IsSignedRemainderSeq

#print axioms TauCeti.Sturm.IsRemainder.of_identity

#print axioms TauCeti.Sturm.IsRemainder.exists_identity

#print axioms TauCeti.Sturm.IsRemainder.dvd

#print axioms TauCeti.Sturm.IsRemainder.alternate

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.singleton

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.pair

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.cons

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.tail

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.last_dvd

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.isAlternating

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.sturmSeq

#print axioms TauCeti.Sturm.IsRemainder.cancel

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.cancel

#print axioms TauCeti.Sturm.IsSignedRemainderSeq.exists_isAlternating

#print axioms TauCeti.Sturm.IsAlternating.sum_sign

#print axioms TauCeti.Sturm.IsTarskiSeed

#print axioms TauCeti.Sturm.IsTarskiSeed.of_identity

#print axioms TauCeti.Sturm.IsTarskiSeed.exists_identity

#print axioms TauCeti.Sturm.IsTarskiSeed.mul_derivative

#print axioms TauCeti.Sturm.IsTarskiSeed.mod

#print axioms TauCeti.Sturm.IsTarskiSeed.sign_eq_of_mul

#print axioms TauCeti.Sturm.IsTarskiSeed.eval_eq_zero_of_mul

#print axioms TauCeti.Sturm.IsTarskiSeed.derivative_eval_ne_zero_of_mul

#print axioms TauCeti.Sturm.IsTarskiSeed.sign_mul_eq_of_mul

#print axioms TauCeti.Sturm.IsTarskiSeed.sign_eq

#print axioms TauCeti.Sturm.IsTarskiSeed.eval_eq_zero

#print axioms TauCeti.Sturm.IsTarskiSeed.sturmSeq

#print axioms TauCeti.Sturm.IsTarskiSeed.sum_sign_eq_zero

#print axioms TauCeti.Sturm.sum_sign

#print axioms TauCeti.Sturm.sum_sign_sturmSeq

#print axioms TauCeti.Sturm.card_roots_toFinset

#print axioms TauCeti.Sturm.signVariationsRight

#print axioms TauCeti.Sturm.signVariationsLeft

#print axioms TauCeti.Sturm.signVariationsRight_def

#print axioms TauCeti.Sturm.signVariationsLeft_def

#print axioms TauCeti.Sturm.signVariationsRight_nil

#print axioms TauCeti.Sturm.signVariationsLeft_nil

#print axioms TauCeti.Sturm.signVariationsRight_singleton

#print axioms TauCeti.Sturm.signVariationsLeft_singleton

#print axioms TauCeti.Sturm.signVariationsAt_eq_right

#print axioms TauCeti.Sturm.signVariationsAt_eq_left

#print axioms TauCeti.Sturm.signVariationsRight_eq_signVariationsAt

#print axioms TauCeti.Sturm.signVariationsLeft_eq_signVariationsAt

#print axioms TauCeti.Sturm.exists_signVariationsRight

#print axioms TauCeti.Sturm.exists_signVariationsLeft

#print axioms TauCeti.Sturm.sum_sign_Ioo

#print axioms TauCeti.Sturm.signVariationsLeft_sub_signVariationsRight

#print axioms TauCeti.Sturm.sum_sign_Ioc

#print axioms TauCeti.Sturm.sum_sign_Ico

#print axioms TauCeti.Sturm.sum_sign_Icc

#print axioms TauCeti.Sturm.sum_sign_sturmSeq_Ioo

#print axioms TauCeti.Sturm.sum_sign_sturmSeq_Ioc

#print axioms TauCeti.Sturm.sum_sign_sturmSeq_Ico

#print axioms TauCeti.Sturm.sum_sign_sturmSeq_Icc

#print axioms TauCeti.Sturm.card_roots_toFinset_Ioo

#print axioms TauCeti.Sturm.card_roots_toFinset_Ioc

#print axioms TauCeti.Sturm.card_roots_toFinset_Ico

#print axioms TauCeti.Sturm.card_roots_toFinset_Icc

#print axioms Polynomial.exists_sign_atTop

#print axioms Polynomial.exists_sign_atBot

#print axioms List.exists_signs_atTop

#print axioms List.exists_signs_atBot

#print axioms TauCeti.Sturm.signVariationsAtTop

#print axioms TauCeti.Sturm.signVariationsAtTop_def

#print axioms TauCeti.Sturm.signVariationsAtTop_nil

#print axioms TauCeti.Sturm.signVariationsAtTop_singleton

#print axioms TauCeti.Sturm.signVariationsAt_eq_atTop

#print axioms TauCeti.Sturm.signVariationsAtBot

#print axioms TauCeti.Sturm.signVariationsAtBot_def

#print axioms TauCeti.Sturm.signVariationsAtBot_nil

#print axioms TauCeti.Sturm.signVariationsAtBot_singleton

#print axioms TauCeti.Sturm.signVariationsAt_eq_atBot

#print axioms TauCeti.Sturm.exists_signVariationsAtTop

#print axioms TauCeti.Sturm.exists_signVariationsAtBot

#print axioms TauCeti.Sturm.exists_atTop

#print axioms TauCeti.Sturm.exists_atBot

#print axioms TauCeti.Sturm.sum_sign_Ioi

#print axioms TauCeti.Sturm.sum_sign_Iio

#print axioms TauCeti.Sturm.sum_sign_univ

#print axioms TauCeti.Sturm.sum_sign_sturmSeq_Ioi

#print axioms TauCeti.Sturm.sum_sign_sturmSeq_Iio

#print axioms TauCeti.Sturm.sum_sign_sturmSeq_univ

#print axioms TauCeti.Sturm.card_roots_toFinset_Ioi

#print axioms TauCeti.Sturm.card_roots_toFinset_Iio

#print axioms TauCeti.Sturm.card_roots_toFinset_univ

#print axioms Polynomial.exists_derivative_root_of_isRoot

#print axioms TauCeti.RealClosure.polynomialRolle_of_isRealClosed

#print axioms Polynomial.exists_derivative_root

#print axioms Polynomial.exists_eval_sub_eq_derivative_eval_mul

#print axioms Polynomial.monotoneOn_of_derivative_nonneg

#print axioms Polynomial.antitoneOn_of_derivative_nonpos

#print axioms Polynomial.strictMonoOn_of_derivative_pos

#print axioms Polynomial.strictAntiOn_of_derivative_neg

#print axioms Polynomial.signSamples

#print axioms Polynomial.mem_signSamples

#print axioms Polynomial.signSamples_of_natDegree_eq_zero

#print axioms Polynomial.signSamples_zero

#print axioms Polynomial.signSamples_nonempty

#print axioms Polynomial.exists_mem_signSamples

#print axioms Function.occCount

#print axioms Function.occCount_def

#print axioms Function.occCount_eq_card_filter

#print axioms Function.occCount_eq_sum

#print axioms Function.occCount_le_of_comp

#print axioms Function.occCount_lt_of_comp

#print axioms Function.occCount_pos

#print axioms Function.occCount_eq_card_preimage

#print axioms Function.occCount_of_notMem_range

#print axioms Function.occCount_of_injective

#print axioms Function.occCount_apply_of_injective

#print axioms Function.prod_occCount_pow

#print axioms Function.sum_occCount_eq_card

#print axioms Function.occCount_castSucc

#print axioms Function.occCount_succ

#print axioms Function.exists_perm_of_occCount_eq

#print axioms Function.mulVec_occCount

#print axioms Function.eq_occCount

#print axioms SignType.lagrangeCoeff

#print axioms SignType.lagrangeCoeff_zero

#print axioms SignType.lagrangeCoeff_neg_one

#print axioms SignType.lagrangeCoeff_one

#print axioms SignType.sum_lagrangeCoeff_mul_pow

#print axioms TauCeti.SignDetermination.fullMatrix

#print axioms TauCeti.SignDetermination.fullMatrix_def

#print axioms TauCeti.SignDetermination.fullInverse

#print axioms TauCeti.SignDetermination.fullMatrix_apply

#print axioms TauCeti.SignDetermination.fullInverse_apply

#print axioms TauCeti.SignDetermination.fullInverse_mul_fullMatrix

#print axioms TauCeti.SignDetermination.fullMatrix_mul_fullInverse

#print axioms TauCeti.SignDetermination.fullMatrix_mulVec_occCount

#print axioms TauCeti.SignDetermination.fullInverse_mulVec

#print axioms Finset.signCount

#print axioms Finset.signCount_eq_occCount

#print axioms Finset.signCount_eq_card_filter

#print axioms Finset.signCount_empty

#print axioms Finset.sum_signCount

#print axioms Finset.signCount_pos

#print axioms Finset.signSum

#print axioms Finset.signSum_eq_sum_subtype

#print axioms Finset.signSum_eq_sum

#print axioms Finset.signSum_empty

#print axioms Finset.signSum_zero

#print axioms Finset.signSum_one

#print axioms Finset.signSum_eq_card_sub_card

#print axioms Polynomial.tarskiQuery

#print axioms Polynomial.tarskiQuery_eq_signSum

#print axioms Polynomial.tarskiQuery_eq_sum

#print axioms Polynomial.tarskiQuery_eq_card_sub_card

#print axioms Polynomial.tarskiQuery_zero_left

#print axioms Polynomial.tarskiQuery_zero_right

#print axioms Polynomial.tarskiQuery_one_right

#print axioms Polynomial.signCount_roots_eq_natCard

#print axioms Polynomial.tarskiQuery_eq_sub

#print axioms Polynomial.signCount_roots_pos

#print axioms Finset.signSum_prod_pow

#print axioms Finset.mulVec_signCount

#print axioms Finset.eq_signCount

#print axioms Finset.signCount_solution_pos_iff

#print axioms Finset.fullInverse_mulVec_signSum

#print axioms Finset.signSum_eq_sum_signCount

#print axioms TauCeti.SignDetermination.sampleProduct

#print axioms TauCeti.SignDetermination.sampleProduct_def

#print axioms TauCeti.SignDetermination.dvd_sampleProduct

#print axioms TauCeti.SignDetermination.sampleProduct_ne_zero

#print axioms TauCeti.SignDetermination.sampleProduct_zero

#print axioms TauCeti.SignDetermination.sampleProduct_of_isEmpty

#print axioms TauCeti.SignDetermination.exists_mem_signSamples_sign_eq

#print axioms TauCeti.SignDetermination.signCount_signSamples_pos_iff

#print axioms TauCeti.SignDetermination.fullInverse_mulVec_signSum_pos_iff

#print axioms Polynomial.tarskiQuery_eq_sum_signCount

#print axioms Polynomial.fullInverse_mulVec_tarskiQuery

#print axioms Real.instIsRealClosed

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicExpr.compileWith

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicExpr.compileWith_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.compileWith

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.compileWith_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.evalReal

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.headMap

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.headMap_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.coefficientMap_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.compileWith

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.compileWith_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.compile

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.compile_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.rationalBody

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFirstOrder.rationalBody_exact

#print axioms MemorySemialgebraic.AlgebraicParameters.Code

#print axioms MemorySemialgebraic.AlgebraicParameters.Code.value

#print axioms MemorySemialgebraic.AlgebraicParameters.Code.value_spec

#print axioms MemorySemialgebraic.AlgebraicParameters.Code.value_unique

#print axioms MemorySemialgebraic.AlgebraicParameters.Code.value_algebraic

#print axioms MemorySemialgebraic.AlgebraicParameters.exists_minpoly_code

#print axioms MemorySemialgebraic.AlgebraicParameters.exists_minpoly_codes

#print axioms MemorySemialgebraic.AlgebraicParameters.power

#print axioms MemorySemialgebraic.AlgebraicParameters.power_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.polynomialAt

#print axioms MemorySemialgebraic.AlgebraicParameters.polynomialAt_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.cellConstraint

#print axioms MemorySemialgebraic.AlgebraicParameters.cellConstraint_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.Code.constraint

#print axioms MemorySemialgebraic.AlgebraicParameters.Code.constraint_exact

#print axioms MemorySemialgebraic.AlgebraicParameters.constraints

#print axioms MemorySemialgebraic.AlgebraicParameters.constraints_exact

#print axioms MemorySemialgebraic.AlgebraicParameters.assignment

#print axioms MemorySemialgebraic.AlgebraicParameters.assignment_left

#print axioms MemorySemialgebraic.AlgebraicParameters.assignment_right

#print axioms MemorySemialgebraic.AlgebraicParameters.coefficient_realization_unique

#print axioms MemorySemialgebraic.AlgebraicParameters.rationalizeFirstOrder

#print axioms MemorySemialgebraic.AlgebraicParameters.rationalizeFirstOrder_exact

#print axioms MemorySemialgebraic.AlgebraicParameters.algebraic_firstOrder_rational_reduction

#print axioms MemorySemialgebraic.AlgebraicParameters.eliminateFirstOrder

#print axioms MemorySemialgebraic.AlgebraicParameters.eliminateFirstOrder_correct

#print axioms MemorySemialgebraic.AlgebraicParameters.minimaxOutput

#print axioms MemorySemialgebraic.AlgebraicParameters.minimaxOutput_correct

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicExpr

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicExpr.evalReal

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicExpr.compile

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicExpr.compile_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.evalReal

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.compile

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.compile_eval

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.rationalBody

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.rationalBody_exact

#print axioms MemorySemialgebraic.AlgebraicParameters.AlgebraicFormula.rationalBody_toQF_exact

#print axioms MemorySemialgebraic.AlgebraicParameters.RationalExistential

#print axioms MemorySemialgebraic.AlgebraicParameters.RationalExistential.eval

#print axioms MemorySemialgebraic.AlgebraicParameters.rationalize

#print axioms MemorySemialgebraic.AlgebraicParameters.rationalize_exact

#print axioms MemorySemialgebraic.AlgebraicParameters.algebraic_coefficients_rational_reduction

#print axioms MemorySemialgebraic.EndpointSelection.center

#print axioms MemorySemialgebraic.EndpointSelection.center_lt_of_disjoint

#print axioms MemorySemialgebraic.EndpointSelection.compileUnivariate_toPoly

#print axioms MemorySemialgebraic.EndpointSelection.qf_root_covered

#print axioms MemorySemialgebraic.EndpointSelection.ray_endpoint_is_root

#print axioms MemorySemialgebraic.EndpointSelection.falseRootCells

#print axioms MemorySemialgebraic.EndpointSelection.mem_falseRootCells

#print axioms MemorySemialgebraic.EndpointSelection.eval_at_isolated_root

#print axioms MemorySemialgebraic.EndpointSelection.Output

#print axioms MemorySemialgebraic.EndpointSelection.select

#print axioms MemorySemialgebraic.EndpointSelection.select_empty

#print axioms MemorySemialgebraic.EndpointSelection.select_full

#print axioms MemorySemialgebraic.EndpointSelection.select_ray

#print axioms MemorySemialgebraic.EndpointSelection.Output.Denotes

#print axioms MemorySemialgebraic.EndpointSelection.select_minimax

#print axioms MemorySemialgebraic.SymbolicQE.cutEntries

#print axioms MemorySemialgebraic.SymbolicQE.cutEntries_eval

#print axioms MemorySemialgebraic.SymbolicQE.memoryFormula

#print axioms MemorySemialgebraic.SymbolicQE.memoryFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.entryVariables

#print axioms MemorySemialgebraic.SymbolicQE.matrixAssignment

#print axioms MemorySemialgebraic.SymbolicQE.entryVariables_eval

#print axioms MemorySemialgebraic.SymbolicQE.flatMemoryFormula

#print axioms MemorySemialgebraic.SymbolicQE.flatMemoryFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.flatMemoryFormula_realization

#print axioms MemorySemialgebraic.SymbolicQE.Expr.sumList

#print axioms MemorySemialgebraic.SymbolicQE.Expr.eval_sumList

#print axioms MemorySemialgebraic.SymbolicQE.Expr.eval_sumList_ofFn

#print axioms MemorySemialgebraic.SymbolicQE.Expr.determinant

#print axioms MemorySemialgebraic.SymbolicQE.Expr.determinant_eval

#print axioms MemorySemialgebraic.SymbolicQE.allTuples

#print axioms MemorySemialgebraic.SymbolicQE.mem_allTuples

#print axioms MemorySemialgebraic.SymbolicQE.Formula.all_ofFn_eval

#print axioms MemorySemialgebraic.SymbolicQE.Formula.rankBound

#print axioms MemorySemialgebraic.SymbolicQE.Formula.rankBound_eval

#print axioms MemorySemialgebraic.SymbolicQE.Formula.strictLower

#print axioms MemorySemialgebraic.SymbolicQE.Formula.strictLower_eval

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.evalReal

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.eliminate

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.eliminate_correct

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.cast

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.evalReal_cast

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.cons_addCases_cast

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.existsBlock

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.existsBlock_correct

#print axioms MemorySemialgebraic.SymbolicQE.Expr.renameVariables

#print axioms MemorySemialgebraic.SymbolicQE.Expr.renameVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.Formula.renameVariables

#print axioms MemorySemialgebraic.SymbolicQE.Formula.renameVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.liftRenaming

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.cons_comp_liftRenaming

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.renameVariables

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.renameVariables_correct

#print axioms MemorySemialgebraic.InfinitySamples.outerBound

#print axioms MemorySemialgebraic.InfinitySamples.root_abs_lt_outerBound

#print axioms MemorySemialgebraic.InfinitySamples.divisor_no_root_right

#print axioms MemorySemialgebraic.InfinitySamples.divisor_no_root_left

#print axioms MemorySemialgebraic.InfinitySamples.sign_outer_right

#print axioms MemorySemialgebraic.InfinitySamples.sign_outer_left

#print axioms MemorySemialgebraic.InfinitySamples.family_signs_atTop

#print axioms MemorySemialgebraic.InfinitySamples.family_signs_atBot

#print axioms MemorySemialgebraic.InfinitySamples.realized_iff_infinity_or_roots

#print axioms MemorySemialgebraic.InfinitySamples.realized_iff_infinity_or_tarski

#print axioms MemorySemialgebraic.SymbolicQE.SignTree

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.evalRat

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.evalReal

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.evalReal_cast

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.bind

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.map

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.evalReal_bind

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.evalReal_map

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.toFormula

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.toFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.normalizeCoeffs

#print axioms MemorySemialgebraic.SymbolicQE.normalizeCoeffs_length

#print axioms MemorySemialgebraic.SymbolicQE.normalizeCoeffs_head_ne_zero

#print axioms MemorySemialgebraic.SymbolicQE.Expr.compileHead

#print axioms MemorySemialgebraic.SymbolicQE.Expr.compileHead_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.derivative

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_derivative

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_derivative

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.compileHead_derivative_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_nil

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_cons

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.degree_lt_length

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.degree_cons

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.leadingCoeff_cons

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_normalize

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.addLow

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.add

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.neg

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.sub

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.scale

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.shift

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_add

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_neg

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_sub

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_scale

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_replicate_zero

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_shift

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.mul

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_mul

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_addLow

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_add

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_neg

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_sub

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_scale

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_shift

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.cancel

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.length_cancel

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.cancel_identity

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.pseudoRemainder

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.pseudoRemainder_length

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.pseudoRemainder_identity

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.pseudoRemainder_signed

#print axioms MemorySemialgebraic.SymbolicQE.Formula.SignClause

#print axioms MemorySemialgebraic.SymbolicQE.Formula.SignDNF

#print axioms MemorySemialgebraic.SymbolicQE.Formula.clauseHolds

#print axioms MemorySemialgebraic.SymbolicQE.Formula.dnfHolds

#print axioms MemorySemialgebraic.SymbolicQE.Formula.andDNF

#print axioms MemorySemialgebraic.SymbolicQE.Formula.andDNF_holds

#print axioms MemorySemialgebraic.SymbolicQE.Formula.appendDNF_holds

#print axioms MemorySemialgebraic.SymbolicQE.Formula.signCases

#print axioms MemorySemialgebraic.SymbolicQE.Formula.signCases_holds

#print axioms MemorySemialgebraic.SymbolicQE.Formula.toSignDNFWith

#print axioms MemorySemialgebraic.SymbolicQE.Formula.toSignDNFWith_correct

#print axioms MemorySemialgebraic.SymbolicQE.Formula.toSignDNF

#print axioms MemorySemialgebraic.SymbolicQE.Formula.toSignDNF_correct

#print axioms MemorySemialgebraic.SymbolicQE.expressionSign

#print axioms MemorySemialgebraic.SymbolicQE.expressionSign_correct

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.sequence

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.sequence_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.infinitySigns

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.infinitySigns_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.infinityVariations

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.infinityVariations_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.chainAux

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.chainAux_head

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.chainAux_second

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.chainAux_signed

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.query

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.query_correct

#print axioms MemorySemialgebraic.SymbolicQE.Expr.constantValue

#print axioms MemorySemialgebraic.SymbolicQE.Expr.constantValue_correct

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.pruneConstants

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.pruneConstants_correct

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.sumRational

#print axioms MemorySemialgebraic.SymbolicQE.SignTree.sumRational_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.power

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_power

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.product

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_product

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.powerProduct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.denote_powerProduct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.ternaryWords

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.sum_ternaryWords

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.count

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.count_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.normalize_eq_nil_iff

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.nonzeroFactor

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.nonzeroFactor_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.familyProduct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.familyProduct_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.infinityCondition

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.infinityCondition_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.rootCondition

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.rootCondition_correct

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.eliminateSignCondition

#print axioms MemorySemialgebraic.SymbolicQE.SymbolicPoly.eliminateSignCondition_correct

#print axioms MemorySemialgebraic.SymbolicQE.Formula.eliminateClause

#print axioms MemorySemialgebraic.SymbolicQE.Formula.eliminateClause_correct

#print axioms MemorySemialgebraic.SymbolicQE.Formula.eliminateExists

#print axioms MemorySemialgebraic.SymbolicQE.Formula.eliminateExists_correct

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.quantifierEliminate

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.quantifierEliminate_correct

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.quantifierEliminate_toQF

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.decideSentence

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.decideSentence_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.coefficientIndex

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.thresholdIndex

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.lossRenaming

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.memory_assignment

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.loss_assignment

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.boundFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.boundFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.thresholdFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.thresholdFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.feasible

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.loss

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.memory

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.thresholdFormula_mem

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.thresholdFormula_value

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.packCoefficients

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.unpackStep

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.unpackIncrement

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.unpackStep_pack

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.unpackIncrement_pack

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.packCoefficients_unpack

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.coefficientEquiv

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.incrementEntries

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.incrementEntries_eval

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.methodMemoryFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.methodMemoryFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.methodThresholdFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.methodThresholdFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProcedureSyntax.methodThresholdFormula_value

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.allBlock

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.allBlock_correct

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.pair

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.pair_correct

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.symmetricFormula

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.symmetricFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.quadraticBody

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.quadraticBody_correct

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.psdFormula

#print axioms MemorySemialgebraic.SymbolicQE.GramSyntax.psdFormula_correct

#print axioms MemorySemialgebraic.EndpointSelection.QEStep

#print axioms MemorySemialgebraic.EndpointSelection.StepCorrect

#print axioms MemorySemialgebraic.EndpointSelection.decideClosed

#print axioms MemorySemialgebraic.EndpointSelection.decideClosed_correct

#print axioms MemorySemialgebraic.EndpointSelection.rootConstraint

#print axioms MemorySemialgebraic.EndpointSelection.rootConstraint_eval

#print axioms MemorySemialgebraic.EndpointSelection.rootLessFormula

#print axioms MemorySemialgebraic.EndpointSelection.rootLessFormula_eval

#print axioms MemorySemialgebraic.EndpointSelection.compare_roots_correct

#print axioms MemorySemialgebraic.EndpointSelection.compareOutputs

#print axioms MemorySemialgebraic.EndpointSelection.valueOrdering

#print axioms MemorySemialgebraic.EndpointSelection.valueOrdering_lt

#print axioms MemorySemialgebraic.EndpointSelection.valueOrdering_eq

#print axioms MemorySemialgebraic.EndpointSelection.compareOutputs_correct

#print axioms MemorySemialgebraic.EndpointSelection.compareOutputs_none_iff

#print axioms MemorySemialgebraic.EndpointSelection.equalOutputs

#print axioms MemorySemialgebraic.EndpointSelection.equalOutputs_correct

#print axioms MemorySemialgebraic.EndpointSelection.strictGain

#print axioms MemorySemialgebraic.EndpointSelection.strictGain_correct

#print axioms MemorySemialgebraic.EndpointSelection.strictGain_thresholds

#print axioms MemorySemialgebraic.MemorySelection.memory

#print axioms MemorySemialgebraic.MemorySelection.memory_saturated

#print axioms MemorySemialgebraic.MemorySelection.unrestrictedValue

#print axioms MemorySemialgebraic.MemorySelection.value_eq_unrestricted

#print axioms MemorySemialgebraic.MemorySelection.budgetMatches

#print axioms MemorySemialgebraic.MemorySelection.leastBudget

#print axioms MemorySemialgebraic.MemorySelection.budgetMatches_correct

#print axioms MemorySemialgebraic.MemorySelection.leastBudget_correct

#print axioms MemorySemialgebraic.MemorySelection.leastSufficientBudget

#print axioms MemorySemialgebraic.MemorySelection.leastSufficientBudget_correct

#print axioms MemorySemialgebraic.MemorySelection.methodThresholds

#print axioms MemorySemialgebraic.MemorySelection.methodThresholds_correct

#print axioms MemorySemialgebraic.MemorySelection.methodLeastBudget

#print axioms MemorySemialgebraic.MemorySelection.methodLeastBudget_correct

#print axioms MemorySemialgebraic.MemorySelection.methodStrictGain

#print axioms MemorySemialgebraic.MemorySelection.methodStrictGain_correct

#print axioms MemorySemialgebraic.MemorySelection.thresholdOutput_ne_invalid

#print axioms MemorySemialgebraic.MemorySelection.methodThresholdOutput_ne_invalid

#print axioms MemorySemialgebraic.MemorySelection.algebraicMethodLeastBudget

#print axioms MemorySemialgebraic.MemorySelection.algebraicMethodLeastBudget_correct

#print axioms MemorySemialgebraic.MemorySelection.algebraicMethodStrictGain

#print axioms MemorySemialgebraic.MemorySelection.algebraicMethodStrictGain_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.eliminateAlgebraic

#print axioms MemorySemialgebraic.EffectiveProcedure.eliminateAlgebraic_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.endpoint

#print axioms MemorySemialgebraic.EffectiveProcedure.endpoint_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicEndpoint

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicEndpoint_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.compareEndpoints

#print axioms MemorySemialgebraic.EffectiveProcedure.compareEndpoints_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.compareEndpoints_none_iff

#print axioms MemorySemialgebraic.EffectiveProcedure.methodEndpoint

#print axioms MemorySemialgebraic.EffectiveProcedure.methodEndpoint_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.methodEndpoint_ne_invalid

#print axioms MemorySemialgebraic.EffectiveProcedure.strictGain

#print axioms MemorySemialgebraic.EffectiveProcedure.strictGain_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.leastSufficientMemory

#print axioms MemorySemialgebraic.EffectiveProcedure.leastSufficientMemory_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicMethodEndpoint

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicMethodEndpoint_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicStrictGain

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicStrictGain_correct

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicLeastSufficientMemory

#print axioms MemorySemialgebraic.EffectiveProcedure.algebraicLeastSufficientMemory_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.allIndex

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.allIndex_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.sumIndex

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.sumIndex_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.pair

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.pair_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.valueExpr

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.valueExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.gradientExpr

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.gradientExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.queryExpr

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.queryExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.difference

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.difference_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.psdFormula

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.psdFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.scaled_nonneg_iff

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.interpolationFormula

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.feasibleFormula

#print axioms MemorySemialgebraic.SymbolicQE.SmoothGramSyntax.feasibleFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.residual

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.residual_correct

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.lossFormula

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.lossFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.input

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.input_correct

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.parametricInput

#print axioms MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax.parametricInput_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.witnessSize

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.gramSlot

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.valueSlot

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.unpackGram

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.unpackValues

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.packWitness

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.unpackGram_pack

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.unpackValues_pack

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.liftExpr

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.liftExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.gramVariables

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.valueVariables

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.gramVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.valueVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.bodyFormula

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.bodyFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.lossFormula

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.lossFormula_model

#print axioms MemorySemialgebraic.SymbolicQE.SmoothLossSyntax.lossFormula_correct

#print axioms MemorySemialgebraic.AlgebraicParameters.specializePrefix

#print axioms MemorySemialgebraic.AlgebraicParameters.specializePrefix_correct

#print axioms MemorySemialgebraic.AlgebraicParameters.twoParameterOrder

#print axioms MemorySemialgebraic.AlgebraicParameters.twoParameterOrder_assignment

#print axioms MemorySemialgebraic.AlgebraicParameters.twoCodes

#print axioms MemorySemialgebraic.AlgebraicParameters.specializeTwoParameters

#print axioms MemorySemialgebraic.AlgebraicParameters.specializeTwoParameters_correct

#print axioms MemorySemialgebraic.QuadraticProcedure.endpoint_correct

#print axioms MemorySemialgebraic.QuadraticProcedure.strictGain_false

#print axioms MemorySemialgebraic.QuadraticProcedure.leastSufficientMemory_zero

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.extendedIncrement

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.extendedIncrement_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.history

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.history_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.coefficientHistory

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.coefficientHistory_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.input

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.input_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.parametricInput

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.parametricInput_correct

#print axioms MemorySemialgebraic.SymbolicQE.SmoothProcedureInput.threshold_correct

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.algebraicInput

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.algebraicInput_correct

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.endpoint

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.strictGain

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.leastSufficientMemory

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.endpoint_correct

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.strictGain_false

#print axioms MemorySemialgebraic.QuadraticAlgebraicProcedure.leastSufficientMemory_zero

#print axioms MemorySemialgebraic.SmoothProcedure.endpoint

#print axioms MemorySemialgebraic.SmoothProcedure.strictGain

#print axioms MemorySemialgebraic.SmoothProcedure.leastSufficientMemory

#print axioms MemorySemialgebraic.SmoothProcedure.endpoint_correct

#print axioms MemorySemialgebraic.SmoothProcedure.endpoint_sharp

#print axioms MemorySemialgebraic.SmoothProcedure.endpoint_zero_query

#print axioms MemorySemialgebraic.SmoothProcedure.endpoint_one_query

#print axioms MemorySemialgebraic.SmoothProcedure.strictGain_correct

#print axioms MemorySemialgebraic.SmoothProcedure.least_budget

#print axioms MemorySemialgebraic.SmoothProcedure.leastSufficientMemory_correct

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.input

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.input_correct

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.endpoint

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.strictGain

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.leastSufficientMemory

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.endpoint_correct

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.endpoint_sharp

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.strictGain_correct

#print axioms MemorySemialgebraic.SmoothAlgebraicInput.leastSufficientMemory_correct

#print axioms MemorySemialgebraic.SymbolicQE.Expr.substitute

#print axioms MemorySemialgebraic.SymbolicQE.Expr.substitute_correct

#print axioms MemorySemialgebraic.SymbolicQE.Formula.substitute

#print axioms MemorySemialgebraic.SymbolicQE.Formula.substitute_correct

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.allList

#print axioms MemorySemialgebraic.SymbolicQE.FirstOrder.allList_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.Space

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.evalVector

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.evalVector_apply

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.lift

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.lift_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.vectorSub

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.evalVector_sub

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.innerExpr

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.innerExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.domain

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.domainAt

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.domainAt_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.projectionFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.projectionFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.indices

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.mem_indices

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.siteExpr

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.slopeExpr

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.valueExpr

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.siteExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.slopeExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.valueExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.interpolationFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.interpolationFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.preExpr

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.preExpr_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.feasibleFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.feasibleFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.witnessSize

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.starSlot

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.pointSlot

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.slopeSlot

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.valueSlot

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackStar

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackPoints

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackSlopes

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackValues

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.packWitness

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackStar_pack

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackPoints_pack

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackSlopes_pack

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.unpackValues_pack

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.starVariables

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.pointVariables

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.slopeVariables

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.valueVariables

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.starVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.pointVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.slopeVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.valueVariables_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.bodyFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.bodyFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.lossFormula

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.lossFormula_model

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedLossSyntax.lossFormula_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.extendDomain

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.domain_extendDomain

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.parameterInput

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.parameterInput_model

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.input

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.input_model

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.input_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.endpoint

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.strictGain

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.leastSufficientMemory

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.endpoint_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.strictGain_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.leastSufficientMemory_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.algebraicDomain

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.domain_algebraicDomain

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.slopeBall

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.domain_slopeBall

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.domain_unrestricted

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.boundedEndpoint

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.boundedEndpoint_correct

#print axioms MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput.boundedEndpoint_finite

-- Revised-manuscript extensions.
#print axioms LemniscateMemory.phiCoefficients
#print axioms LemniscateMemory.phiCoefficients_strict
#print axioms LemniscateMemory.phi_increment_entry
#print axioms LemniscateMemory.phi_cut_eq_outer
#print axioms LemniscateMemory.phi_cut_rank_le_one
#print axioms LemniscateMemory.phi_increment_mem_one
#print axioms LemniscateMemory.phi_has_two_register_realization
#print axioms LemniscateMemory.phiMachine
#print axioms LemniscateMemory.phiMachine_state
#print axioms LemniscateMemory.phiMachine_readout
#print axioms LemniscateMemory.phiMachine_realizes
#print axioms LemniscateMemory.phi
#print axioms LemniscateMemory.coefficients
#print axioms LemniscateMemory.coefficients_entry
#print axioms LemniscateMemory.coefficients_strict
#print axioms LemniscateMemory.history
#print axioms LemniscateMemory.increment_entry
#print axioms LemniscateMemory.cut_rank_le_one
#print axioms LemniscateMemory.has_two_register_realization
#print axioms LemniscateMemory.memory_rank_le_two
#print axioms LemniscateMemory.machine
#print axioms LemniscateMemory.machine_realizes
#print axioms LemniscateMemory.machine_vectorRealizes
#print axioms LemniscateMemory.machine_executes_oracle
#print axioms QuadraticReplacement.Step
#print axioms QuadraticReplacement.stepPolynomial
#print axioms QuadraticReplacement.runPolynomial
#print axioms QuadraticReplacement.runPolynomial_append
#print axioms QuadraticReplacement.factorSteps
#print axioms QuadraticReplacement.factorSteps_length
#print axioms QuadraticReplacement.run_factorSteps
#print axioms QuadraticReplacement.allFactorSteps
#print axioms QuadraticReplacement.allFactorSteps_length
#print axioms QuadraticReplacement.run_allFactorSteps
#print axioms QuadraticReplacement.run_zero_steps
#print axioms QuadraticReplacement.exists_factor_steps
#print axioms QuadraticReplacement.polynomial_energy_identity
#print axioms QuadraticReplacement.polynomial_energy_mono
#print axioms QuadraticReplacement.exists_one_register_pointwise_replacement
#print axioms QuadraticReplacement.quadratic_two_call_identity
#print axioms QuadraticReplacement.complex_normalized_roots
#print axioms QuadraticReplacement.real_factor_le_complex
#print axioms QuadraticReplacement.list_real_factors_le
#print axioms QuadraticReplacement.exists_list_product_dominated
#print axioms QuadraticReplacement.ofFn_of_length
#print axioms QuadraticReplacement.exists_productPoly_dominated
#print axioms QuadraticReplacement.normalizeConstant
#print axioms QuadraticReplacement.normalizeConstant_eval_zero
#print axioms QuadraticReplacement.normalizeConstant_natDegree
#print axioms QuadraticReplacement.normalizeConstant_mul
#print axioms QuadraticReplacement.exists_normalized_low_degree_factors
#print axioms QuadraticReplacement.exists_normalized_factors
#print axioms QuadraticReplacement.low_degree_form
#print axioms QuadraticReplacement.linear_form
#print axioms QuadraticReplacement.subdiagonal
#print axioms QuadraticReplacement.subdiagonal_strict
#print axioms QuadraticReplacement.subdiagonal_memory
#print axioms QuadraticReplacement.subdiagonal_sum
#print axioms QuadraticReplacement.polynomialState
#print axioms QuadraticReplacement.polynomialState_eq
#print axioms QuadraticReplacement.polynomialState_eq_run
#print axioms QuadraticReplacement.exists_two_register_polynomial
#print axioms QuadraticReplacement.exists_two_register_exact_replacement
#print axioms ResidualRigidity.eq_of_normalized_root_values
#print axioms ResidualRigidity.eq_of_positive_roots_of_energy_domination
#print axioms ResidualRigidity.residual_eq_of_scalar_quadratic_domination
#print axioms ResidualRigidity.terminal_eq_of_scalar_quadratic_domination
#print axioms Submission2026.StrongConvexMemory.backwardPair
#print axioms Submission2026.StrongConvexMemory.a
#print axioms Submission2026.StrongConvexMemory.b
#print axioms Submission2026.StrongConvexMemory.c
#print axioms Submission2026.StrongConvexMemory.p
#print axioms Submission2026.StrongConvexMemory.alpha
#print axioms Submission2026.StrongConvexMemory.t
#print axioms Submission2026.StrongConvexMemory.u
#print axioms Submission2026.StrongConvexMemory.a_terminal
#print axioms Submission2026.StrongConvexMemory.b_terminal
#print axioms Submission2026.StrongConvexMemory.p_terminal
#print axioms Submission2026.StrongConvexMemory.backward_pair_step
#print axioms Submission2026.StrongConvexMemory.c_one
#print axioms Submission2026.StrongConvexMemory.p_before_terminal
#print axioms Submission2026.StrongConvexMemory.query_shift_identity
#print axioms Submission2026.StrongConvexMemory.original_v_update
#print axioms Submission2026.StrongConvexMemory.original_next_query
#print axioms Submission2026.StrongConvexMemory.RiskEquation
#print axioms Submission2026.StrongConvexMemory.machine
#print axioms Submission2026.StrongConvexMemory.step
#print axioms Submission2026.StrongConvexMemory.machine_step
#print axioms Submission2026.StrongConvexMemory.trajectory
#print axioms Submission2026.StrongConvexMemory.stateNat_trajectory
#print axioms Submission2026.StrongConvexMemory.psi_initial
#print axioms Submission2026.StrongConvexMemory.history
#print axioms Submission2026.StrongConvexMemory.history_causal
#print axioms Submission2026.StrongConvexMemory.target_state
#print axioms Submission2026.StrongConvexMemory.target_trajectory
#print axioms Submission2026.StrongConvexMemory.realizes
#print axioms Submission2026.StrongConvexMemory.vectorRealizes
#print axioms Submission2026.StrongConvexMemory.cut_rank_le_two
#print axioms Submission2026.StrongConvexMemory.memory_le_two
#print axioms Submission2026.StrongConvexMemory.itemMachine
#print axioms Submission2026.StrongConvexMemory.itemHistory
#print axioms Submission2026.StrongConvexMemory.item_realizes
#print axioms Submission2026.StrongConvexMemory.item_vectorRealizes
#print axioms Submission2026.StrongConvexMemory.item_cut_rank_le_two
#print axioms Submission2026.StrongConvexMemory.item_memory_le_two
#print axioms Submission2026.StrongConvexMemory.item_history_trajectory
#print axioms Submission2026.StrongConvexMemory.item_one_query_memory
#print axioms Submission2026.StrongConvexMemory.item_one_query_realizable
#print axioms Submission2026.StrongConvexMemory.item_executes_oracle

#print axioms ExtremalMemory.D
#print axioms ExtremalMemory.omegaEntry
#print axioms ExtremalMemory.omegaEntry_diagonal
#print axioms ExtremalMemory.omegaEntry_recurrence
#print axioms ExtremalMemory.D_pos
#print axioms ExtremalMemory.PathConditions4
#print axioms ExtremalMemory.coefficients
#print axioms ExtremalMemory.coefficients_strict
#print axioms ExtremalMemory.history
#print axioms ExtremalMemory.determinant4
#print axioms ExtremalMemory.wedge2
#print axioms ExtremalMemory.wedge2_cancellation
#print axioms ExtremalMemory.determinant4_factorization
#print axioms ExtremalMemory.determinant4_eq
#print axioms ExtremalMemory.determinant4_neg
#print axioms ExtremalMemory.cut2_det
#print axioms ExtremalMemory.cut2_rank
#print axioms ExtremalMemory.memory_rank_eq_three
#print axioms ExtremalMemory.has_three_register_realization
#print axioms ExtremalMemory.no_two_register_realization
#print axioms ExtremalMemory.vector_memory_exact
