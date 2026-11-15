module
public import Submission2026.WeakCurvature.Core

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

lemma oneStepD_pos (q : ℝ) : 0 < oneStepD q := by
  unfold oneStepD
  nlinarith [sq_nonneg (q - 1 / 2)]

lemma oneStepD_nonneg (q : ℝ) : 0 ≤ oneStepD q := (oneStepD_pos q).le

lemma sqrt_oneStepD_pos (q : ℝ) : 0 < Real.sqrt (oneStepD q) :=
  Real.sqrt_pos.2 (oneStepD_pos q)

lemma oneStepDenominator_pos (q : ℝ) : 0 < 1 + Real.sqrt (oneStepD q) := by
  positivity

lemma oneStepDenominator_ne (q : ℝ) : 1 + Real.sqrt (oneStepD q) ≠ 0 :=
  ne_of_gt (oneStepDenominator_pos q)

lemma curvatureA_eq_one_sub_two_mul_c {q : ℝ} (hq : q ≠ 1) :
    curvatureA q = 1 - 2 * curvatureC q := by
  have h : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  unfold curvatureA curvatureC
  field_simp [h]
  ring

lemma curvatureA_pos {q : ℝ} (hq : q < 1) : 0 < curvatureA q := by
  unfold curvatureA
  positivity

lemma oneStepT_pos {q : ℝ} (hq : q < 1) : 0 < oneStepT q := by
  unfold oneStepT
  exact div_pos (by linarith) (oneStepDenominator_pos q)

lemma oneStepNu_pos {q : ℝ} (hq : q < 1) : 0 < oneStepNu q := by
  unfold oneStepNu
  have ht := oneStepT_pos hq
  positivity

lemma oneStepNu_nonneg {q : ℝ} (hq : q < 1) : 0 ≤ oneStepNu q :=
  (oneStepNu_pos hq).le

lemma oneStepT_lt_one {q : ℝ} (hq : q < 1) : oneStepT q < 1 := by
  rw [oneStepT, div_lt_one (oneStepDenominator_pos q)]
  by_cases hq0 : 0 ≤ q
  · have hs := sqrt_oneStepD_pos q
    linarith
  · have hq0' : q < 0 := lt_of_not_ge hq0
    have hs := Real.sqrt_nonneg (oneStepD q)
    have hs2 := Real.sq_sqrt (oneStepD_nonneg q)
    change Real.sqrt (oneStepD q) ^ 2 = 1 - q + q ^ 2 at hs2
    by_contra hn
    have hle : Real.sqrt (oneStepD q) ≤ -q := by linarith
    have hsquare : Real.sqrt (oneStepD q) * Real.sqrt (oneStepD q) ≤ (-q) * (-q) :=
      mul_le_mul hle hle hs (by linarith)
    have hsquare' : Real.sqrt (oneStepD q) ^ 2 ≤ q ^ 2 := by
      nlinarith [hsquare]
    rw [hs2] at hsquare'
    nlinarith

/-- The explicit scalar `t_q` satisfies the quadratic tightness equation. -/
lemma oneStepT_equation (q : ℝ) :
    q * oneStepT q ^ 2 - 2 * oneStepT q + (1 - q) = 0 := by
  have hs := Real.sq_sqrt (oneStepD_nonneg q)
  change Real.sqrt (oneStepD q) ^ 2 = 1 - q + q ^ 2 at hs
  rw [oneStepT]
  field_simp [oneStepDenominator_ne q]
  have he : q * (1 - q) - (1 + Real.sqrt (oneStepD q)) * 2 +
      (1 + Real.sqrt (oneStepD q)) ^ 2 = 0 := by
    nlinarith [hs]
  rw [he]
  ring

/-- The one-step tail condition `2*t*(a+c*t)=1`. -/
lemma oneStep_tail_relation {q : ℝ} (hq : q < 1) :
    2 * oneStepT q * (curvatureA q + curvatureC q * oneStepT q) = 1 := by
  have h1q : 1 - q ≠ 0 := by linarith
  have hp := oneStepT_equation q
  unfold curvatureA curvatureC
  field_simp [h1q]
  nlinarith

/-- The one-step zeroth tightness condition. -/
lemma oneStep_zeroth_relation {q : ℝ} (hq : q < 1) :
    oneStepNu q = 4 * curvatureC q +
      2 * curvatureA q * (1 - oneStepT q) ^ 2 := by
  have h1q : 1 - q ≠ 0 := by linarith
  have hp := oneStepT_equation q
  unfold oneStepNu curvatureA curvatureC
  field_simp [h1q]
  nlinarith

/-- Uniqueness of the positive sub-unital solution of the tail equation. -/
lemma eq_oneStepT_of_tail_relation {q t : ℝ} (hq : q < 1)
    (ht : 0 < t) (ht1 : t < 1)
    (hrel : 2 * t * (curvatureA q + curvatureC q * t) = 1) :
    t = oneStepT q := by
  have h1q : 1 - q ≠ 0 := by linarith
  have hp : q * t ^ 2 - 2 * t + (1 - q) = 0 := by
    unfold curvatureA curvatureC at hrel
    field_simp [h1q] at hrel
    nlinarith
  have hp0 := oneStepT_equation q
  have ht0 := oneStepT_pos hq
  have ht01 := oneStepT_lt_one hq
  have hsum : 0 < t + oneStepT q := by linarith
  have hsum2 : t + oneStepT q < 2 := by linarith
  have hprod : q * (t + oneStepT q) < 2 := by
    by_cases hq0 : 0 ≤ q
    · calc
        q * (t + oneStepT q) < 1 * (t + oneStepT q) :=
          (mul_lt_mul_of_pos_right hq hsum)
        _ < 2 := by simpa using hsum2
    · have hq0' : q < 0 := lt_of_not_ge hq0
      have : q * (t + oneStepT q) < 0 := mul_neg_of_neg_of_pos hq0' hsum
      linarith
  have hfactor : (t - oneStepT q) * (q * (t + oneStepT q) - 2) = 0 := by
    nlinarith
  have hne : q * (t + oneStepT q) - 2 ≠ 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hne)

/-- The explicit value satisfies the first scalar condition in `Psi_c` form. -/
lemma oneStep_tailPsi {q : ℝ} (hq : q < 1) :
    tailPsi (curvatureC q) (curvatureA q) (oneStepT q) 0 = oneStepNu q := by
  have ht := oneStepT_pos hq
  have hrel := oneStep_tail_relation hq
  have hpack : curvatureA q + curvatureC q * oneStepT q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hrel
    norm_num at hrel
  have hden : curvatureA q / oneStepT q + curvatureC q ≠ 0 := by
    intro h
    have hz : curvatureA q + curvatureC q * oneStepT q = 0 := by
      field_simp [ne_of_gt ht] at h
      nlinarith
    exact hpack hz
  have hzero : tailPsi (curvatureC q) (curvatureA q) (oneStepT q) 0 =
      1 / (curvatureA q / oneStepT q + curvatureC q) := by
    norm_num [tailPsi]
  rw [hzero, oneStepNu, div_eq_iff hden]
  field_simp [ne_of_gt ht]
  nlinarith

/-- The root-balance equation from Appendix F at horizon one. -/
lemma oneStep_root_balance {q : ℝ} (hq : q < 1) :
    oneStepT q + Real.sqrt ((oneStepNu q - 4 * curvatureC q) /
      (2 * curvatureA q)) = 1 := by
  have ha := curvatureA_pos hq
  have ht1 := oneStepT_lt_one hq
  have hz := oneStep_zeroth_relation hq
  have hrw : (oneStepNu q - 4 * curvatureC q) / (2 * curvatureA q) =
      (1 - oneStepT q) ^ 2 := by
    apply (div_eq_iff (by positivity : 2 * curvatureA q ≠ 0)).2
    nlinarith
  rw [hrw, Real.sqrt_sq (by linarith : 0 ≤ 1 - oneStepT q)]
  ring

/-- At horizon one the uncapped capacity root at zero is exactly `t_q`. -/
lemma oneStep_capacityRoot_zero {q : ℝ} (hq : q < 1) :
    capacityRoot (curvatureC q) (curvatureA q) (oneStepNu q) 0 = oneStepT q := by
  have ht := oneStepT_pos hq
  have ha := curvatureA_pos hq
  have hν := oneStepNu_nonneg hq
  have hrel := oneStep_tail_relation hq
  have hden : 1 - curvatureC q * oneStepNu q = 2 * curvatureA q * oneStepT q := by
    unfold oneStepNu
    nlinarith
  unfold capacityRoot capacityA capacityB
  simp only [mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [Real.sqrt_sq hν]
  change curvatureA q * (oneStepNu q + oneStepNu q) /
    (2 * (1 - curvatureC q * oneStepNu q)) = oneStepT q
  rw [hden]
  unfold oneStepNu
  field_simp [ne_of_gt ht, ne_of_gt ha]
  ring

/-- At horizon one the cap is inactive. -/
lemma oneStep_capacity_zero {q : ℝ} (hq : q < 1) :
    capacity (curvatureC q) (curvatureA q) (oneStepNu q) 0 = oneStepT q := by
  unfold capacity
  rw [oneStep_capacityRoot_zero hq]
  exact min_eq_right (oneStepT_lt_one hq).le

/-- The explicit one-step value is strictly above the lower endpoint `4*c`. -/
lemma four_mul_c_lt_oneStepNu {q : ℝ} (hq : q < 1) :
    4 * curvatureC q < oneStepNu q := by
  have ha := curvatureA_pos hq
  have ht1 := oneStepT_lt_one hq
  have hz := oneStep_zeroth_relation hq
  have hpos : 0 < 2 * curvatureA q * (1 - oneStepT q) ^ 2 := by
    positivity
  linarith

/-- The explicit one-step value is below the upper endpoint `u_c`. -/
lemma oneStepNu_lt_capacityUpper {q : ℝ} (hq : q < 1) :
    oneStepNu q < capacityUpper (curvatureC q) := by
  have ha := curvatureA_pos hq
  have ht := oneStepT_pos hq
  have ht1 := oneStepT_lt_one hq
  have haeq := curvatureA_eq_one_sub_two_mul_c (ne_of_lt hq)
  have hapos : 0 < 1 - 2 * curvatureC q := by rwa [← haeq]
  have huc : 0 < 1 - curvatureC q := by linarith
  have hrel := oneStep_tail_relation hq
  rw [haeq] at hrel
  have hmul : oneStepT q * (1 - 2 * curvatureC q) < 1 - 2 * curvatureC q := by
    nlinarith
  unfold capacityUpper
  apply (lt_div_iff₀ huc).2
  unfold oneStepNu
  nlinarith

lemma oneStepNu_mem_rootInterval {q : ℝ} (hq : q < 1) :
    4 * curvatureC q < oneStepNu q ∧
      oneStepNu q < capacityUpper (curvatureC q) :=
  ⟨four_mul_c_lt_oneStepNu hq, oneStepNu_lt_capacityUpper hq⟩

/-- The explicit one-step value satisfies the actual Appendix F root predicate. -/
lemma isScalarRoot_one_oneStepNu {q : ℝ} (hq : q < 1) :
    IsScalarRoot 1 q (oneStepNu q) := by
  unfold IsScalarRoot scalarBalance
  rw [Function.iterate_one, oneStep_capacity_zero hq]
  exact oneStep_root_balance hq

#print axioms oneStepT_equation
#print axioms oneStep_tail_relation
#print axioms oneStep_zeroth_relation
#print axioms eq_oneStepT_of_tail_relation
#print axioms oneStep_tailPsi
#print axioms oneStep_root_balance
#print axioms oneStep_capacityRoot_zero
#print axioms oneStep_capacity_zero
#print axioms four_mul_c_lt_oneStepNu
#print axioms oneStepNu_lt_capacityUpper
#print axioms oneStepNu_mem_rootInterval
#print axioms isScalarRoot_one_oneStepNu

end Submission2026.WeakCurvature
