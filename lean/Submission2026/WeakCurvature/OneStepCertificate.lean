module
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace WeakCurvature

def InterpResidual (c : ℝ) (f_i f_j g_i g_j x_i x_j : ℝ) : ℝ :=
  f_i - f_j - g_j * (x_i - x_j) - (1/2) * (g_i - g_j) ^ 2 + c * (x_i - x_j - (g_i - g_j)) ^ 2

def OneStepCoeffEq (c ν t1 h : ℝ) : Prop :=
  (-2 * c * h ^ 2 * t1 + c * h ^ 2 + 4 * c * h * t1 - 2 * c * h - 2 * c * t1 + c
    - h * t1 + h + t1 - 1/2 = 0)
  ∧ (-4 * c * h * t1 + 2 * c * h + 4 * c * t1 - 2 * c + h * t1 - 2 * t1 + 1 = 0)
  ∧ (-2 * c * ν * t1 + c * ν + ν * t1 - 1 = 0)

def sVal (c : ℝ) : ℝ := Real.sqrt (4 * c ^ 2 - 2 * c + 1)
def t1Val (c : ℝ) : ℝ := -2 * c + sVal c + 1
def hVal (c : ℝ) : ℝ := if c = 0 then 3/2 else (4 * c + sVal c - 1) / (2 * c)
def nuVal (c : ℝ) : ℝ := 1 / (t1Val c * (1 - 2 * c) + c)

theorem coeff_nu_ne_zero {c ν t1 h : ℝ} (hCoeff : OneStepCoeffEq c ν t1 h) : ν ≠ 0 := by
  intro hν0; have h3 := hCoeff.2.2; rw [hν0] at h3; simp at h3

theorem oneStep_certificate_identity
    (c ν t1 h : ℝ) (hCoeff : OneStepCoeffEq c ν t1 h)
    (f0 f1 fs g0 g1 x0 : ℝ) :
    let x1 := x0 - h * g0
    let I01 := InterpResidual c f0 f1 g0 g1 x0 x1
    let I10 := InterpResidual c f1 f0 g1 g0 x1 x0
    f0 - fs - g1 ^ 2 / ν = (f1 - fs - 1/2 * g1 ^ 2) + t1 * I01 + (t1 - 1) * I10 := by
  intro x1 I01 I10
  have h1 := hCoeff.1; have h2 := hCoeff.2.1; have h3 := hCoeff.2.2
  have hν_ne : ν ≠ 0 := coeff_nu_ne_zero hCoeff
  simp only [InterpResidual, x1, I01, I10] at *
  have h_mul : ν * (f0 - fs - g1 ^ 2 / ν) = ν * ((f1 - fs - 1/2 * g1 ^ 2) + t1 * (f0 - f1 - g1 * (x0 - (x0 - h * g0)) - 1/2 * (g0 - g1) ^ 2 + c * (x0 - (x0 - h * g0) - (g0 - g1)) ^ 2) + (t1 - 1) * (f1 - f0 - g0 * (x0 - h * g0 - x0) - 1/2 * (g1 - g0) ^ 2 + c * (x0 - h * g0 - x0 - (g1 - g0)) ^ 2)) := by
    have hf : ν * (f0 - fs - g1 ^ 2 / ν) - ν * ((f1 - fs - 1/2 * g1 ^ 2) + t1 * (f0 - f1 - g1 * (x0 - (x0 - h * g0)) - 1/2 * (g0 - g1) ^ 2 + c * (x0 - (x0 - h * g0) - (g0 - g1)) ^ 2) + (t1 - 1) * (f1 - f0 - g0 * (x0 - h * g0 - x0) - 1/2 * (g1 - g0) ^ 2 + c * (x0 - h * g0 - x0 - (g1 - g0)) ^ 2)) =
        (-2 * c * h ^ 2 * t1 + c * h ^ 2 + 4 * c * h * t1 - 2 * c * h - 2 * c * t1 + c - h * t1 + h + t1 - 1/2) * ν * g0 ^ 2 + (-4 * c * h * t1 + 2 * c * h + 4 * c * t1 - 2 * c + h * t1 - 2 * t1 + 1) * ν * g0 * g1 + (-2 * c * ν * t1 + c * ν + ν * t1 - 1) * g1 ^ 2 := by field_simp [hν_ne]; ring
    have h_zero : (-2 * c * h ^ 2 * t1 + c * h ^ 2 + 4 * c * h * t1 - 2 * c * h - 2 * c * t1 + c - h * t1 + h + t1 - 1/2) * ν * g0 ^ 2 + (-4 * c * h * t1 + 2 * c * h + 4 * c * t1 - 2 * c + h * t1 - 2 * t1 + 1) * ν * g0 * g1 + (-2 * c * ν * t1 + c * ν + ν * t1 - 1) * g1 ^ 2 = 0 := by
      have hg0 : (-2 * c * h ^ 2 * t1 + c * h ^ 2 + 4 * c * h * t1 - 2 * c * h - 2 * c * t1 + c - h * t1 + h + t1 - 1/2) * ν * g0 ^ 2 = 0 := by rw [h1]; ring
      have hg01 : (-4 * c * h * t1 + 2 * c * h + 4 * c * t1 - 2 * c + h * t1 - 2 * t1 + 1) * ν * g0 * g1 = 0 := by rw [h2]; ring
      have hg1 : (-2 * c * ν * t1 + c * ν + ν * t1 - 1) * g1 ^ 2 = 0 := by rw [h3]; ring
      linarith
    linarith
  exact mul_left_cancel₀ hν_ne h_mul

theorem radicand_nonneg (c : ℝ) : 0 ≤ 4 * c ^ 2 - 2 * c + 1 := by
  have : 4 * c ^ 2 - 2 * c + 1 = 4 * (c - 1/4) ^ 2 + 3/4 := by ring
  linarith [sq_nonneg (c - 1/4)]

theorem sVal_sq (c : ℝ) : sVal c ^ 2 = 4 * c ^ 2 - 2 * c + 1 := by
  unfold sVal; rw [Real.sq_sqrt (radicand_nonneg c)]

theorem explicit_N1_satisfies_coeffEq (c : ℝ) (hc0 : c ≠ 0) (hc_le : c ≤ 1/4) (hc_ge : 0 ≤ c) :
    OneStepCoeffEq c (nuVal c) (t1Val c) (hVal c) := by
  unfold OneStepCoeffEq nuVal t1Val hVal sVal
  simp only [if_neg hc0]
  have hs2 : Real.sqrt (4 * c ^ 2 - 2 * c + 1) ^ 2 = 4 * c ^ 2 - 2 * c + 1 :=
    Real.sq_sqrt (radicand_nonneg c)
  set s := Real.sqrt (4 * c ^ 2 - 2 * c + 1) with hs_def
  have hs_sq : s ^ 2 = 4 * c ^ 2 - 2 * c + 1 := hs2
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hden_pos : 0 < (-2 * c + s + 1) * (1 - 2 * c) + c := by
    nlinarith [hs_sq, hs_nn, sq_nonneg c, sq_nonneg s, hc_ge, hc_le]
  have hden_ne : ((-2 * c + s + 1) * (1 - 2 * c) + c) ≠ 0 := ne_of_gt hden_pos
  constructor
  · field_simp; nlinarith [hs_sq, sq_nonneg s, sq_nonneg c]
  constructor
  · field_simp; nlinarith [hs_sq, sq_nonneg s, sq_nonneg c]
  · have hν_den : (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) * ((-2 * c + s + 1) * (1 - 2 * c) + c) = 1 :=
      one_div_mul_cancel hden_ne
    have h_eq : -2 * c * (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) * (-2 * c + s + 1) + c * (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) + (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) * (-2 * c + s + 1) - 1 = 0 := by
      have h1 : -2 * c * (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) * (-2 * c + s + 1) + c * (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) + (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) * (-2 * c + s + 1) = (1 / ((-2 * c + s + 1) * (1 - 2 * c) + c)) * ((-2 * c + s + 1) * (1 - 2 * c) + c) := by ring
      rw [h1, hν_den]; ring
    exact h_eq

theorem explicit_N1_c0 : OneStepCoeffEq 0 (1/2) 2 (3/2) := by
  unfold OneStepCoeffEq; constructor; norm_num; constructor; norm_num; norm_num

theorem oneStep_upper_bound
    (c ν t1 h : ℝ) (hCoeff : OneStepCoeffEq c ν t1 h)
    (f0 f1 fs g0 g1 x0 : ℝ)
    (hν_pos : 0 < ν) (ht1_pos : 0 ≤ t1) (ht1m1_pos : 0 ≤ t1 - 1)
    (hI01 : 0 ≤ InterpResidual c f0 f1 g0 g1 x0 (x0 - h * g0))
    (hI10 : 0 ≤ InterpResidual c f1 f0 g1 g0 (x0 - h * g0) x0)
    (hDescent : 0 ≤ f1 - fs - 1/2 * g1 ^ 2) :
    g1 ^ 2 ≤ ν * (f0 - fs) := by
  have hcert := oneStep_certificate_identity c ν t1 h hCoeff f0 f1 fs g0 g1 x0
  simp only at hcert
  have hI01_nn : 0 ≤ t1 * InterpResidual c f0 f1 g0 g1 x0 (x0 - h * g0) := mul_nonneg ht1_pos hI01
  have hI10_nn : 0 ≤ (t1 - 1) * InterpResidual c f1 f0 g1 g0 (x0 - h * g0) x0 := mul_nonneg ht1m1_pos hI10
  have hRHS_nn : 0 ≤ (f1 - fs - 1/2 * g1 ^ 2) + t1 * InterpResidual c f0 f1 g0 g1 x0 (x0 - h * g0) + (t1 - 1) * InterpResidual c f1 f0 g1 g0 (x0 - h * g0) x0 := by linarith
  have h_eq : f0 - fs - g1 ^ 2 / ν = (f1 - fs - 1/2 * g1 ^ 2) + t1 * InterpResidual c f0 f1 g0 g1 x0 (x0 - h * g0) + (t1 - 1) * InterpResidual c f1 f0 g1 g0 (x0 - h * g0) x0 := hcert
  have h_ge : f0 - fs - g1 ^ 2 / ν ≥ 0 := by linarith
  have h_le : g1 ^ 2 / ν ≤ f0 - fs := by linarith
  have hν_ne : ν ≠ 0 := ne_of_gt hν_pos
  have : g1 ^ 2 ≤ ν * (f0 - fs) := by
    have hmul : g1 ^ 2 / ν * ν = g1 ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h_le (le_of_lt hν_pos)]
  exact this

#print axioms oneStep_certificate_identity
#print axioms explicit_N1_satisfies_coeffEq
#print axioms oneStep_upper_bound
end WeakCurvature
