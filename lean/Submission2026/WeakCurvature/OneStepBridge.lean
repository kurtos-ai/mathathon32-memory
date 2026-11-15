module
public import Submission2026.WeakCurvature.OneStep
public import Submission2026.WeakCurvature.ScalarParams
public import Submission2026.WeakCurvature.OneStepCertificate

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

lemma sVal_curvatureC {q : ℝ} (hq : q < 1) :
    WeakCurvature.sVal (curvatureC q) = Real.sqrt (oneStepD q) / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  have hrad : 4 * curvatureC q ^ 2 - 2 * curvatureC q + 1 =
      oneStepD q / (1 - q) ^ 2 := by
    unfold curvatureC oneStepD
    field_simp [ne_of_gt h1q]
    ring
  unfold WeakCurvature.sVal
  rw [hrad]
  have hsq : oneStepD q / (1 - q) ^ 2 =
      (Real.sqrt (oneStepD q) / (1 - q)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (oneStepD_nonneg q)]
  rw [hsq, Real.sqrt_sq (by positivity)]

lemma t1Val_curvatureC {q : ℝ} (hq : q < 1) :
    WeakCurvature.t1Val (curvatureC q) = (1 + Real.sqrt (oneStepD q)) / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  unfold WeakCurvature.t1Val
  rw [sVal_curvatureC hq]
  unfold curvatureC
  field_simp [ne_of_gt h1q]
  ring

lemma t1Val_mul_oneStepT {q : ℝ} (hq : q < 1) :
    WeakCurvature.t1Val (curvatureC q) * oneStepT q = 1 := by
  rw [t1Val_curvatureC hq, oneStepT]
  field_simp [oneStepDenominator_ne q, show 1 - q ≠ 0 by linarith]

lemma hVal_curvatureC_of_ne_zero {q : ℝ} (hq : q < 1) (hq0 : q ≠ 0) :
    WeakCurvature.hVal (curvatureC q) = (1 + q - Real.sqrt (oneStepD q)) / q := by
  have h1q : 0 < 1 - q := by linarith
  have hc0 : curvatureC q ≠ 0 := by
    unfold curvatureC
    exact div_ne_zero (neg_ne_zero.mpr hq0)
      (mul_ne_zero (by norm_num) (ne_of_gt h1q))
  unfold WeakCurvature.hVal
  simp only [if_neg hc0]
  rw [sVal_curvatureC hq]
  unfold curvatureC
  field_simp [ne_of_gt h1q, hq0]
  ring

lemma hVal_curvatureC_eq_one_add_t {q : ℝ} (hq : q < 1) (hq0 : q ≠ 0) :
    WeakCurvature.hVal (curvatureC q) = 1 + oneStepT q := by
  rw [hVal_curvatureC_of_ne_zero hq hq0, oneStepT]
  have hs := Real.sq_sqrt (oneStepD_nonneg q)
  change Real.sqrt (oneStepD q) ^ 2 = 1 - q + q ^ 2 at hs
  field_simp [oneStepDenominator_ne q, hq0]
  nlinarith

lemma hVal_curvatureC_zero : WeakCurvature.hVal (curvatureC 0) = 1 + oneStepT 0 := by
  norm_num [WeakCurvature.hVal, curvatureC, oneStepT, oneStepD]

lemma hVal_curvatureC {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) :
    WeakCurvature.hVal (curvatureC q) = 1 + oneStepT q := by
  by_cases hq0 : q = 0
  · subst q
    exact hVal_curvatureC_zero
  · exact hVal_curvatureC_eq_one_add_t (by linarith [hq.2]) hq0

lemma nuVal_curvatureC {q : ℝ} (hq : q < 1) :
    WeakCurvature.nuVal (curvatureC q) = oneStepNu q := by
  have ht := oneStepT_pos hq
  have ht1 := t1Val_mul_oneStepT hq
  have haeq := curvatureA_eq_one_sub_two_mul_c (ne_of_lt hq)
  have hrel := oneStep_tail_relation hq
  rw [haeq] at hrel
  have ht1eq : WeakCurvature.t1Val (curvatureC q) = 1 / oneStepT q := by
    apply (eq_div_iff (ne_of_gt ht)).2
    exact ht1
  have hdeneq : WeakCurvature.t1Val (curvatureC q) * (1 - 2 * curvatureC q) +
      curvatureC q = 1 / (2 * oneStepT q ^ 2) := by
    rw [ht1eq]
    field_simp [ne_of_gt ht]
    nlinarith
  unfold WeakCurvature.nuVal
  rw [hdeneq]
  unfold oneStepNu
  field_simp [ne_of_gt ht]

lemma oneStepCoeffEq_curvatureC {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) :
    WeakCurvature.OneStepCoeffEq (curvatureC q) (WeakCurvature.nuVal (curvatureC q))
      (WeakCurvature.t1Val (curvatureC q)) (WeakCurvature.hVal (curvatureC q)) := by
  by_cases hc : curvatureC q = 0
  · rw [hc]
    convert WeakCurvature.explicit_N1_c0 using 1 <;>
      norm_num [WeakCurvature.nuVal, WeakCurvature.t1Val, WeakCurvature.hVal,
        WeakCurvature.sVal]
  · exact WeakCurvature.explicit_N1_satisfies_coeffEq (curvatureC q) hc
      (c_le_quarter_of_mem_Icc hq) (c_nonneg_of_mem_Icc hq)

lemma oneStepCoeffEq_oneStepNu {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) :
    WeakCurvature.OneStepCoeffEq (curvatureC q) (oneStepNu q)
      (WeakCurvature.t1Val (curvatureC q)) (WeakCurvature.hVal (curvatureC q)) := by
  rw [← nuVal_curvatureC (show q < 1 by linarith [hq.2])]
  exact oneStepCoeffEq_curvatureC hq

lemma t1Val_curvatureC_pos {q : ℝ} (hq : q < 1) :
    0 < WeakCurvature.t1Val (curvatureC q) := by
  rw [t1Val_curvatureC hq]
  exact div_pos (oneStepDenominator_pos q) (by linarith)

lemma one_le_t1Val_curvatureC {q : ℝ} (hq : q < 1) :
    1 ≤ WeakCurvature.t1Val (curvatureC q) := by
  have ht1 := t1Val_curvatureC_pos hq
  have ht := oneStepT_pos hq
  have htlt := oneStepT_lt_one hq
  have hprod := t1Val_mul_oneStepT hq
  have hmul : WeakCurvature.t1Val (curvatureC q) * oneStepT q ≤
      WeakCurvature.t1Val (curvatureC q) * 1 := by
    exact mul_le_mul_of_nonneg_left htlt.le ht1.le
  nlinarith

/-- The explicit one-step terminal-gradient bound for the source's nonpositive
curvature regime. Its only analytic inputs are the interpolation residuals and
terminal descent floor; all coefficient equations are proved. -/
lemma oneStep_explicit_upper_bound {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0)
    (f0 f1 fs g0 g1 x0 : ℝ)
    (hI01 : 0 ≤ WeakCurvature.InterpResidual (curvatureC q) f0 f1 g0 g1 x0
      (x0 - WeakCurvature.hVal (curvatureC q) * g0))
    (hI10 : 0 ≤ WeakCurvature.InterpResidual (curvatureC q) f1 f0 g1 g0
      (x0 - WeakCurvature.hVal (curvatureC q) * g0) x0)
    (hDescent : 0 ≤ f1 - fs - 1 / 2 * g1 ^ 2) :
    g1 ^ 2 ≤ oneStepNu q * (f0 - fs) := by
  exact WeakCurvature.oneStep_upper_bound (curvatureC q) (oneStepNu q)
    (WeakCurvature.t1Val (curvatureC q)) (WeakCurvature.hVal (curvatureC q))
    (oneStepCoeffEq_oneStepNu hq) f0 f1 fs g0 g1 x0
    (oneStepNu_pos (show q < 1 by linarith [hq.2]))
    (t1Val_curvatureC_pos (show q < 1 by linarith [hq.2])).le
    (by linarith [one_le_t1Val_curvatureC (show q < 1 by linarith [hq.2])])
    hI01 hI10 hDescent

#print axioms sVal_curvatureC
#print axioms t1Val_curvatureC
#print axioms t1Val_mul_oneStepT
#print axioms hVal_curvatureC_of_ne_zero
#print axioms hVal_curvatureC_eq_one_add_t
#print axioms hVal_curvatureC_zero
#print axioms hVal_curvatureC
#print axioms nuVal_curvatureC
#print axioms oneStepCoeffEq_curvatureC
#print axioms oneStepCoeffEq_oneStepNu
#print axioms t1Val_curvatureC_pos
#print axioms one_le_t1Val_curvatureC
#print axioms oneStep_explicit_upper_bound

end Submission2026.WeakCurvature
