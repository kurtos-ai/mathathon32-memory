module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace Submission2026.Separation.Current

/-- The exact rate used in Theorem 7.2. -/
def separationRate : ℚ := 261 / 5000

/-- The larger rate used for the a priori certificate bounds. -/
def certificateRate : ℚ := 523 / 10000

/-- The hinge-width cap used in Theorem 7.2. -/
def hingeWidthCap : ℚ := 1 / 10

theorem separationRate_pos : 0 < separationRate := by
  unfold separationRate
  norm_num

theorem separationRate_lt_certificateRate : separationRate < certificateRate := by
  unfold separationRate certificateRate
  norm_num

theorem certificateRate_pos : 0 < certificateRate := by
  unfold certificateRate
  norm_num

theorem separationRate_half_eq : separationRate / 2 = (261 / 10000 : ℚ) := by
  unfold separationRate
  norm_num

/-- The smaller-positive-root balance slope from Appendix B.6. -/
def hingeBalance (E r : ℝ) : ℝ := (1 - Real.sqrt (1 - 2 * r * E)) / (2 * E)

theorem hingeBalance_pos {E r : ℝ} (hE : 0 < E) (hr : 0 < r)
    (hrad : 0 ≤ 1 - 2 * r * E) : 0 < hingeBalance E r := by
  have hrE : 0 < r * E := mul_pos hr hE
  have hs_lt : Real.sqrt (1 - 2 * r * E) < 1 := by
    have h := Real.sqrt_lt_sqrt hrad
      (show 1 - 2 * r * E < (1 : ℝ) ^ 2 by nlinarith)
    simpa using h
  exact div_pos (sub_pos.mpr hs_lt) (by positivity)

theorem hingeBalance_le_inv_two_mul {E r : ℝ} (hE : 0 < E) (r : ℝ)
    (hrad : 0 ≤ 1 - 2 * r * E) : hingeBalance E r ≤ 1 / (2 * E) := by
  unfold hingeBalance
  have hnum : 1 - Real.sqrt (1 - 2 * r * E) ≤ 1 := by
    linarith [Real.sqrt_nonneg (1 - 2 * r * E)]
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- The defining slope balances the worst ridge loss exactly at `r / 2`.
This is the algebraic root computation, not a numerical approximation. -/
theorem hingeBalance_loss {E r : ℝ} (hE : 0 < E) (r : ℝ)
    (hrad : 0 ≤ 1 - 2 * r * E) :
    hingeBalance E r * (1 - hingeBalance E r * E) = r / 2 := by
  have hs : Real.sqrt (1 - 2 * r * E) ^ 2 = 1 - 2 * r * E :=
    Real.sq_sqrt hrad
  have hEne : E ≠ 0 := ne_of_gt hE
  unfold hingeBalance
  field_simp
  nlinarith

/-- The path-program formula for `E(r)` converts positivity of its radicand
to the exact condition `2 * |ν|^2 < 1` used in Appendix B.6. -/
theorem one_sub_two_mul_rate_mul_pathValue (r nuSq : ℝ) (hr : r ≠ 0) :
    1 - 2 * r * (((1 / r - 1) / 2) + nuSq) = r * (1 - 2 * nuSq) := by
  field_simp
  ring

theorem pathValue_radicand_pos_of_nuSq_lt_half {r nuSq : ℝ}
    (hr : 0 < r) (hnu : 2 * nuSq < 1) :
    0 < 1 - 2 * r * (((1 / r - 1) / 2) + nuSq) := by
  rw [one_sub_two_mul_rate_mul_pathValue r nuSq (ne_of_gt hr)]
  positivity

end Submission2026.Separation.Current
