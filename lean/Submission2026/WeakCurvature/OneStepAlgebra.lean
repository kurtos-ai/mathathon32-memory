module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace Submission2026.WeakCurvature

def D (q : ℝ) : ℝ := 1 - q + q ^ 2

def t (q : ℝ) : ℝ := (1 - q) / (1 + Real.sqrt (D q))

def nu (q : ℝ) : ℝ := 2 * (t q) ^ 2

theorem D_pos (q : ℝ) : 0 < D q := by
  unfold D
  nlinarith [sq_nonneg (q - 1/2 : ℝ), sq_nonneg q]

theorem D_nonneg (q : ℝ) : 0 ≤ D q := le_of_lt (D_pos q)

theorem sqrt_D_nonneg (q : ℝ) : 0 ≤ Real.sqrt (D q) :=
  Real.sqrt_nonneg _

theorem one_plus_sqrt_D_pos (q : ℝ) : 0 < 1 + Real.sqrt (D q) := by
  linarith [sqrt_D_nonneg q]

theorem one_plus_sqrt_D_ne_zero (q : ℝ) : (1 + Real.sqrt (D q)) ≠ 0 :=
  ne_of_gt (one_plus_sqrt_D_pos q)

theorem D_ge_three_quarters (q : ℝ) : 3/4 ≤ D q := by
  unfold D
  nlinarith [sq_nonneg (q - 1/2 : ℝ)]

theorem t_pos_of_lt_one {q : ℝ} (hq : q < 1) : 0 < t q := by
  unfold t
  apply div_pos <;> linarith [one_plus_sqrt_D_pos q]

theorem t_nonneg_of_le_one {q : ℝ} (hq : q ≤ 1) : 0 ≤ t q := by
  unfold t
  apply div_nonneg <;> linarith [sqrt_D_nonneg q]

theorem t_eq_zero_of_one {q : ℝ} (hq : q = 1) : t q = 0 := by
  unfold t; simp [hq]

theorem t_mul_one_plus_sqrt (q : ℝ) : t q * (1 + Real.sqrt (D q)) = 1 - q := by
  unfold t
  have hne := one_plus_sqrt_D_ne_zero q
  rw [div_mul_cancel₀ _ hne]

theorem t_characterization {q t₀ : ℝ} (h : t₀ * (1 + Real.sqrt (D q)) = 1 - q) :
    t₀ = t q := by
  have hne := one_plus_sqrt_D_ne_zero q
  have ht := t_mul_one_plus_sqrt q
  have : t₀ * (1 + Real.sqrt (D q)) = t q * (1 + Real.sqrt (D q)) := by rw [h, ht]
  exact mul_right_cancel₀ hne this

theorem one_sub_q_sub_t_eq_t_sqrt (q : ℝ) : 1 - q - t q = t q * Real.sqrt (D q) := by
  have h := t_mul_one_plus_sqrt q
  nlinarith

theorem radical_squared (q : ℝ) : (1 - q - t q) ^ 2 = (t q) ^ 2 * D q := by
  have h := one_sub_q_sub_t_eq_t_sqrt q
  calc (1 - q - t q) ^ 2 = (t q * Real.sqrt (D q)) ^ 2 := by rw [h]
    _ = (t q) ^ 2 * (Real.sqrt (D q)) ^ 2 := by ring
    _ = (t q) ^ 2 * D q := by rw [Real.sq_sqrt (D_nonneg q)]

theorem one_plus_t_eq (q : ℝ) : 1 + t q = (2 - q + Real.sqrt (D q)) / (1 + Real.sqrt (D q)) := by
  unfold t
  have hne := one_plus_sqrt_D_ne_zero q
  rw [add_div' _ _ _ hne]
  congr 1; ring

theorem nu_eq (q : ℝ) : nu q = 2 * ((1 - q) / (1 + Real.sqrt (D q))) ^ 2 := by
  unfold nu t; rfl

theorem nu_eq_div_pow (q : ℝ) : nu q = 2 * (1 - q) ^ 2 / (1 + Real.sqrt (D q)) ^ 2 := by
  rw [nu_eq, div_pow]
  ring

theorem nu_nonneg (q : ℝ) : 0 ≤ nu q := by
  unfold nu; positivity

theorem nu_pos_of_lt_one {q : ℝ} (hq : q < 1) : 0 < nu q := by
  unfold nu
  have ht := t_pos_of_lt_one hq
  positivity

theorem U1_eq_nu (q : ℝ) : nu q = 2 * ((1 - q) / (1 + Real.sqrt (1 - q + q ^ 2))) ^ 2 := by
  unfold nu t D; rfl

theorem D_zero : D 0 = 1 := by unfold D; ring
theorem D_one : D 1 = 1 := by unfold D; ring
theorem t_zero : t 0 = 1 / 2 := by unfold t D; norm_num
theorem t_one : t 1 = 0 := by unfold t D; simp
theorem nu_zero : nu 0 = 1 / 2 := by unfold nu; rw [t_zero]; norm_num
theorem nu_one : nu 1 = 0 := by unfold nu; rw [t_one]; simp

#print axioms D_pos
#print axioms t_pos_of_lt_one
#print axioms t_mul_one_plus_sqrt
#print axioms radical_squared
#print axioms one_plus_t_eq
#print axioms nu_eq_div_pow

end Submission2026.WeakCurvature
