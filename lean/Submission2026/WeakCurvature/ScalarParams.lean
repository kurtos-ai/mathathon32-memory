module
public import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace Submission2026.WeakCurvature
def cParam (q : ℝ) : ℝ := -q / (2 * (1 - q))
def aParam (q : ℝ) : ℝ := 1 / (1 - q)
def ucParam (q : ℝ) : ℝ := 1 / (1 - cParam q)
lemma one_sub_ne_zero_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : (1 - q) ≠ 0 := by
  have : 1 - q ≥ 1 := by linarith [hq.2]
  linarith
lemma one_sub_pos_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : 0 < 1 - q := by
  have : 1 - q ≥ 1 := by linarith [hq.2]
  linarith
theorem a_eq_one_sub_two_c (q : ℝ) (hq1 : (1 - q) ≠ 0) : aParam q = 1 - 2 * cParam q := by
  unfold aParam cParam
  have h2 : (2 * (1 - q)) ≠ 0 := by
    intro h
    apply hq1
    linarith
  field_simp
  ring
theorem four_c_eq (q : ℝ) (hq1 : (1 - q) ≠ 0) : 4 * cParam q = -2 * q / (1 - q) := by
  unfold cParam
  have h2 : (2 * (1 - q)) ≠ 0 := by
    intro h
    apply hq1
    linarith
  field_simp
  ring
theorem c_nonneg_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : 0 ≤ cParam q := by
  unfold cParam
  have hpos : 0 < 1 - q := one_sub_pos_of_mem_Icc hq
  have h2pos : 0 < 2 * (1 - q) := by linarith
  have h_num : 0 ≤ -q := by linarith [hq.2]
  exact div_nonneg h_num (le_of_lt h2pos)
theorem c_le_quarter_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : cParam q ≤ 1/4 := by
  unfold cParam
  have h2pos : 0 < 2 * (1 - q) := by have := one_sub_pos_of_mem_Icc hq; linarith
  rw [div_le_iff₀ h2pos]
  nlinarith [hq.1]
theorem a_ge_half_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : (1 : ℝ)/2 ≤ aParam q := by
  unfold aParam
  have hpos : 0 < 1 - q := one_sub_pos_of_mem_Icc hq
  have hle : 1 - q ≤ 2 := by linarith [hq.1]
  calc (1 : ℝ)/2 = 1/2 := rfl
    _ ≤ 1 / (1 - q) := by
        rw [div_le_div_iff₀ (by norm_num) hpos]
        nlinarith
theorem a_le_one_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : aParam q ≤ 1 := by
  unfold aParam
  have hpos : 0 < 1 - q := one_sub_pos_of_mem_Icc hq
  have hge : 1 ≤ 1 - q := by linarith [hq.2]
  calc 1 / (1 - q) ≤ 1 / 1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hge
    _ = 1 := by simp
theorem c_lt_one_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : cParam q < 1 := by
  have := c_le_quarter_of_mem_Icc hq
  linarith
theorem one_sub_c_pos_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : 0 < 1 - cParam q := by
  have := c_lt_one_of_mem_Icc hq
  linarith
theorem one_sub_c_ne_zero_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : (1 - cParam q) ≠ 0 := by
  have := one_sub_c_pos_of_mem_Icc hq
  linarith
theorem uc_pos_of_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0) : 0 < ucParam q := by
  unfold ucParam
  exact div_pos one_pos (one_sub_c_pos_of_mem_Icc hq)
theorem c_eq_one_sub_a_div_two (q : ℝ) (hq1 : (1 - q) ≠ 0) : cParam q = (1 - aParam q) / 2 := by
  have ha := a_eq_one_sub_two_c q hq1
  linarith
theorem c_neg_of_pos_q {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) : cParam q < 0 := by
  unfold cParam
  have h1q_pos : 0 < 1 - q := by linarith
  have h2pos : 0 < 2 * (1 - q) := by linarith
  apply div_neg_of_neg_of_pos
  · linarith
  · linarith
theorem a_gt_one_of_pos_q {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) : 1 < aParam q := by
  unfold aParam
  have hpos : 0 < 1 - q := by linarith
  have hlt : 1 - q < 1 := by linarith
  calc 1 = 1/1 := by simp
    _ < 1 / (1 - q) := by
        apply div_lt_div_of_pos_left (by norm_num) (by linarith) hlt

#print axioms cParam
#print axioms aParam
#print axioms ucParam
#print axioms a_eq_one_sub_two_c
#print axioms four_c_eq

end Submission2026.WeakCurvature
