module
public import Submission2026.WeakCurvature.ScalarParams
public import Submission2026.WeakCurvature.OneStep
public import Submission2026.WeakCurvature.CapacityAlgebra

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

lemma curvature_c_mem_interval {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) :
    0 ≤ curvatureC q ∧ curvatureC q ≤ 1 / 4 := by
  exact ⟨c_nonneg_of_mem_Icc hq, c_le_quarter_of_mem_Icc hq⟩

lemma four_mul_c_le_capacityUpper_curvature {q : ℝ}
    (hq : q ∈ Set.Icc (-1 : ℝ) 0) :
    4 * curvatureC q ≤ capacityUpper (curvatureC q) := by
  exact four_mul_c_le_capacityUpper (c_nonneg_of_mem_Icc hq) (c_le_quarter_of_mem_Icc hq)

lemma curvature_capacityA_pos {q ν t : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0)
    (ht1 : t ≤ 1) (hν : ν ≤ capacityUpper (curvatureC q)) :
    0 < capacityA (curvatureC q) (curvatureA q) ν t := by
  have hq1 : q ≠ 1 := by linarith [hq.2]
  exact capacityA_pos_of_nonneg_c (curvatureA_eq_one_sub_two_mul_c hq1)
    (c_nonneg_of_mem_Icc hq) (c_le_quarter_of_mem_Icc hq) ht1 hν

lemma curvature_capacityRadicand_nonneg {q ν t : ℝ}
    (hq : q ∈ Set.Icc (-1 : ℝ) 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hν0 : 4 * curvatureC q ≤ ν) (hν1 : ν ≤ capacityUpper (curvatureC q)) :
    0 ≤ capacityB (curvatureC q) ν t ^ 2 -
      4 * capacityA (curvatureC q) (curvatureA q) ν t * t ^ 2 := by
  have hq1 : q ≠ 1 := by linarith [hq.2]
  exact capacityRadicand_nonneg_of_nonneg_c (curvatureA_eq_one_sub_two_mul_c hq1)
    (c_nonneg_of_mem_Icc hq) (c_le_quarter_of_mem_Icc hq) ht0 ht1 hν0 hν1

/-- In the nonpositive-curvature regime the displayed upper root is well-defined
and satisfies the exact quadratic capacity equation. -/
lemma curvature_capacityRoot_quadratic {q ν t : ℝ}
    (hq : q ∈ Set.Icc (-1 : ℝ) 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hν0 : 4 * curvatureC q ≤ ν) (hν1 : ν ≤ capacityUpper (curvatureC q)) :
    capacityA (curvatureC q) (curvatureA q) ν t *
        capacityRoot (curvatureC q) (curvatureA q) ν t ^ 2
      - curvatureA q * capacityB (curvatureC q) ν t *
        capacityRoot (curvatureC q) (curvatureA q) ν t
      + curvatureA q ^ 2 * t ^ 2 = 0 := by
  exact capacityRoot_quadratic
    (ne_of_gt (curvature_capacityA_pos hq ht1 hν1))
    (curvature_capacityRadicand_nonneg hq ht0 ht1 hν0 hν1)

#print axioms curvature_c_mem_interval
#print axioms four_mul_c_le_capacityUpper_curvature
#print axioms curvature_capacityA_pos
#print axioms curvature_capacityRadicand_nonneg
#print axioms curvature_capacityRoot_quadratic

end Submission2026.WeakCurvature
