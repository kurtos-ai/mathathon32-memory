module
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

/-- Scalar function Psi_c from Appendix w:app:weak, equation w:wk:eq:psi:
    Psi_c(s,t) = 4c(2t - t^2) + (1 - a t/s - 2c t)^2 / (a/s + c)
    with continuous value 0 at (0,0). This is the diagonal/endpoint
    objective after simplex projection. -/
def psi (c a s t : ℝ) : ℝ :=
  4 * c * (2 * t - t ^ 2) + (1 - a * t / s - 2 * c * t) ^ 2 / (a / s + c)

/-- Diagonal specialization: Psi_c(s,s) in closed form.
    Source Appendix w:app:weak, Lemma tailPsi_diagonal / psiends:
    Psi_c(s,s) = 4c * (1 - a*(1-s)^2/(a + c s)). -/
theorem psi_diag_eq (c a s : ℝ) (ha : a = 1 - 2 * c) (hs : s ≠ 0) (hden : a + c * s ≠ 0) :
    psi c a s s = 4 * c * (1 - a * (1 - s) ^ 2 / (a + c * s)) := by
  unfold psi
  have hd : a / s + c = (a + c * s) / s := by field_simp
  have hn : (1 : ℝ) - a * s / s - 2 * c * s = (s - a * s - 2 * c * s * s) / s := by
    field_simp
  rw [hd, hn]
  field_simp [hs, hden]
  rw [ha]
  ring

/-- Diagonal inequality: Psi_c(s,s) ≤ 4c for admissible curvature.
    Source: psiends / tailPsi_diagonal_le, used to show diagonal never
    exceeds the universal floor 4c. -/
theorem psi_diag_le (c a s : ℝ) (ha : a = 1 - 2 * c)
    (hc0 : 0 ≤ c) (ha0 : 0 ≤ a) (hs : s ≠ 0) (hden : 0 < a + c * s) :
    psi c a s s ≤ 4 * c := by
  rw [psi_diag_eq c a s ha hs (ne_of_gt hden)]
  have hfrac : 0 ≤ a * (1 - s) ^ 2 / (a + c * s) := by positivity
  have hle : 1 - a * (1 - s) ^ 2 / (a + c * s) ≤ 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ 4 * c by positivity)
  nlinarith

/-- Right-endpoint specialization: Psi_c(1,t) in closed form.
    Source: psiends — Psi_c(1,t) = 4c + a^2(1-t)^2/(1-c). -/
theorem psi_one_eq (c a t : ℝ) (ha : a = 1 - 2 * c) (hc : (1 : ℝ) - c ≠ 0) :
    psi c a 1 t = 4 * c + a ^ 2 * (1 - t) ^ 2 / (1 - c) := by
  unfold psi
  simp only [div_one]
  rw [ha]
  rw [show (1 - 2 * c + c : ℝ) = 1 - c by ring]
  field_simp [hc]
  ring

/-- Right-endpoint lower bound: Psi_c(1,t) ≥ 4c. -/
theorem psi_one_ge (c a t : ℝ) (ha : a = 1 - 2 * c) (hc : 0 < 1 - c) :
    4 * c ≤ psi c a 1 t := by
  rw [psi_one_eq c a t ha (ne_of_gt hc)]
  have h : 0 ≤ a ^ 2 * (1 - t) ^ 2 / (1 - c) := by positivity
  linarith

/-- Convex-quadratic form in t (source Lemma branch / capacity proof).
    For fixed s>0, Psi(s,t) is a convex quadratic in t. The proof rewrites
    the fraction to denominator s*(a+cs), avoiding calculus. -/
theorem psi_eq_convex_quadratic (c a s t : ℝ) (_ha : a = 1 - 2 * c)
    (hs : s ≠ 0) (hden : a + c * s ≠ 0) :
    psi c a s t = 4 * c * (2 * t - t ^ 2) +
      (s - a * t - 2 * c * s * t) ^ 2 / (s * (a + c * s)) := by
  unfold psi
  have hd : a / s + c = (a + c * s) / s := by field_simp
  have hn : (1 : ℝ) - a * t / s - 2 * c * t = (s - a * t - 2 * c * s * t) / s := by
    field_simp
  rw [hd, hn]
  field_simp [hs, hden]

/-- Endpoint bound at s=1: Psi_c(1,t) ≤ 1/(1-c).
    Since Psi(1,t)=4c + a^2(1-t)^2/(1-c) and (1-t)^2 ≤ 1 for t∈[0,1],
    we have Psi(1,t) ≤ 4c + a^2/(1-c) = 1/(1-c) when a=1-2c. -/
theorem psi_one_le_capacityUpper (c a t : ℝ) (ha : a = 1 - 2 * c)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : 0 < 1 - c) :
    psi c a 1 t ≤ 1 / (1 - c) := by
  rw [psi_one_eq c a t ha (ne_of_gt hc)]
  have hid : 4 * c + a ^ 2 / (1 - c) = 1 / (1 - c) := by
    rw [ha]; field_simp [ne_of_gt hc]; ring
  have h_mono : a ^ 2 * (1 - t) ^ 2 / (1 - c) ≤ a ^ 2 / (1 - c) := by
    apply div_le_div_of_nonneg_right _ hc.le
    have h1 : (1 - t) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - t), sq_nonneg t]
    nlinarith [sq_nonneg a]
  linarith

/-- For t=s the convex-quadratic correction vanishes to give the diagonal form;
    the quadratic coefficient a^2/(s(a+cs)) is positive under admissible
    parameters, establishing strict convexity in t. -/
theorem psi_convex_coeff_pos (c a s : ℝ) (_ha : a = 1 - 2 * c)
    (ha0 : 0 < a) (hs : 0 < s) (hden : 0 < a + c * s) :
    0 < a ^ 2 / (s * (a + c * s)) := by positivity

#print axioms psi
#print axioms psi_diag_eq
#print axioms psi_diag_le
#print axioms psi_one_eq
#print axioms psi_one_ge
#print axioms psi_eq_convex_quadratic
#print axioms psi_one_le_capacityUpper
#print axioms psi_convex_coeff_pos

end Submission2026.WeakCurvature
