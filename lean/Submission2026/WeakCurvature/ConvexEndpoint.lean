module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

def Psi0 (s t : ℝ) : ℝ := (s - t) ^ 2 / s

theorem tail_last_eq {S_N ν : ℝ} (hSpos : 0 < S_N)
    (h : Psi0 S_N 0 = ν) : S_N = ν := by
  unfold Psi0 at h
  simp at h
  have hSne : S_N ≠ 0 := ne_of_gt hSpos
  have hmul : S_N ^ 2 / S_N * S_N = ν * S_N := congrArg (· * S_N) h
  have hcan : S_N ^ 2 / S_N * S_N = S_N ^ 2 := by
    rw [div_mul_cancel₀ _ hSne]
  have hsq : S_N ^ 2 = ν * S_N := by linarith
  have : S_N * S_N = ν * S_N := by nlinarith
  exact mul_right_cancel₀ hSne this

theorem psi0_tightness_sqrt {s t ν : ℝ} (hs : 0 < s) (_hν : 0 ≤ ν)
    (hle : t ≤ s) (h : Psi0 s t = ν) : s - t = Real.sqrt (ν * s) := by
  unfold Psi0 at h
  have hsne : s ≠ 0 := ne_of_gt hs
  have hmul : (s - t) ^ 2 / s * s = ν * s := congrArg (· * s) h
  have hcan : (s - t) ^ 2 / s * s = (s - t) ^ 2 := div_mul_cancel₀ _ hsne
  have hsq : (s - t) ^ 2 = ν * s := by linarith
  have hnn : 0 ≤ s - t := by linarith
  calc s - t = Real.sqrt ((s - t) ^ 2) := (Real.sqrt_sq hnn).symm
    _ = Real.sqrt (ν * s) := by rw [hsq]

theorem sqrt_tightness_imp_psi0 {s t ν : ℝ} (hs : 0 < s) (hνs : 0 ≤ ν * s)
    (h : s - t = Real.sqrt (ν * s)) : Psi0 s t = ν := by
  unfold Psi0
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsq : (s - t) ^ 2 = ν * s := by
    calc (s - t) ^ 2 = Real.sqrt (ν * s) ^ 2 := by rw [← h]
      _ = ν * s := Real.sq_sqrt hνs
  calc (s - t) ^ 2 / s = ν * s / s := by rw [hsq]
    _ = ν := by rw [mul_div_cancel_right₀ _ hsne]

theorem delta_eq_nu_beta {s t ν β : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β)
    (hs : s = ν * β ^ 2) (hδ : s - t = Real.sqrt (ν * s)) :
    s - t = ν * β := by
  have hsqrt : Real.sqrt (ν * s) = ν * β := by
    rw [hs]
    have h1 : ν * (ν * β ^ 2) = (ν * β) ^ 2 := by ring
    rw [h1, Real.sqrt_sq (by positivity)]
  linarith

theorem beta_recurrence {S_i S_next ν β_i β_next : ℝ}
    (hν : 0 < ν)
    (hSi : S_i = ν * β_i ^ 2) (hSnext : S_next = ν * β_next ^ 2)
    (hδ : S_i - S_next = ν * β_i) :
    β_i ^ 2 - β_i = β_next ^ 2 := by
  have h : ν * β_i ^ 2 - ν * β_next ^ 2 = ν * β_i := by
    rw [← hSi, ← hSnext]; linarith
  have hνne : ν ≠ 0 := ne_of_gt hν
  have h1 : ν * (β_i ^ 2 - β_i - β_next ^ 2) = 0 := by nlinarith
  have h2 : β_i ^ 2 - β_i - β_next ^ 2 = 0 := by
    have : ν * (β_i ^ 2 - β_i - β_next ^ 2) = 0 := h1
    exact (mul_eq_zero.mp this).resolve_left hνne
  linarith

theorem psi0_beta_eq {S_i S_next ν β_i β_next : ℝ}
    (hs : 0 < S_i) (hν : 0 < ν) (hβi : 0 ≤ β_i)
    (hle : S_next ≤ S_i)
    (hSi : S_i = ν * β_i ^ 2) (hSnext : S_next = ν * β_next ^ 2)
    (hPsi : Psi0 S_i S_next = ν) :
    β_i ^ 2 - β_i = β_next ^ 2 := by
  have hδ_sqrt : S_i - S_next = Real.sqrt (ν * S_i) :=
    psi0_tightness_sqrt hs hν.le hle hPsi
  have hδ : S_i - S_next = ν * β_i :=
    delta_eq_nu_beta hν hβi hSi hδ_sqrt
  exact beta_recurrence hν hSi hSnext hδ

theorem beta_last_one {S_N ν β_N : ℝ} (hν : 0 < ν) (_hβN : 0 ≤ β_N)
    (hS : S_N = ν) (hβ : β_N = Real.sqrt (S_N / ν)) : β_N = 1 := by
  rw [hS] at hβ
  have : ν / ν = (1 : ℝ) := div_self (ne_of_gt hν)
  rw [this] at hβ
  simp at hβ
  exact hβ

theorem beta_last_one' {ν β_N : ℝ} (hν : 0 < ν) (hβN : 0 ≤ β_N)
    (h : ν * β_N ^ 2 = ν) : β_N = 1 := by
  have hνne : ν ≠ 0 := ne_of_gt hν
  have h1 : β_N ^ 2 = 1 := mul_left_cancel₀ hνne (by linarith)
  nlinarith [sq_nonneg (β_N - 1), sq_nonneg β_N, hβN]

theorem zeroth_to_theta {S₁ ν β₁ θ : ℝ} (hν : 0 < ν) (_hβ1 : 0 ≤ β₁)
    (_hθpos : 0 < θ)
    (hS : S₁ = ν * β₁ ^ 2)
    (hθ : θ = Real.sqrt (2 / ν))
    (h0 : 1 - S₁ = Real.sqrt (ν / 2)) :
    θ ^ 2 - θ = 2 * β₁ ^ 2 := by
  have hνne : ν ≠ 0 := ne_of_gt hν
  have hνs : 0 ≤ 2 / ν := by positivity
  have hθνs : 0 ≤ ν / 2 := by positivity
  have hθsq : θ ^ 2 = 2 / ν := by rw [hθ, Real.sq_sqrt hνs]
  -- product of the two square roots is 1
  have hprod : Real.sqrt (2 / ν) * Real.sqrt (ν / 2) = 1 := by
    have hmul : (2 / ν) * (ν / 2) = 1 := by field_simp
    have hnn1 : 0 ≤ 2 / ν := hνs
    have hnn2 : 0 ≤ ν / 2 := hθνs
    calc Real.sqrt (2 / ν) * Real.sqrt (ν / 2) = Real.sqrt ((2 / ν) * (ν / 2)) := by
          rw [Real.sqrt_mul hnn1]
      _ = Real.sqrt 1 := by rw [hmul]
      _ = 1 := by simp
  have hθne : θ ≠ 0 := by rw [hθ]; exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have h1 : θ * Real.sqrt (ν / 2) = 1 := by
    calc θ * Real.sqrt (ν / 2) = Real.sqrt (2 / ν) * Real.sqrt (ν / 2) := by rw [hθ]
      _ = 1 := hprod
  have hsqrt_eq : Real.sqrt (ν / 2) = 1 / θ := by
    rw [eq_div_iff hθne]
    linarith [h1]
  have h0' : 1 - ν * β₁ ^ 2 = 1 / θ := by
    have : S₁ = ν * β₁ ^ 2 := hS
    rw [this] at h0
    rw [hsqrt_eq] at h0
    linarith
  have hνβ : ν * β₁ ^ 2 = 1 - 1 / θ := by linarith
  have h2 : 2 * β₁ ^ 2 = (2 / ν) * (1 - 1 / θ) := by
    have h_a : (2 / ν) * (ν * β₁ ^ 2) = 2 * β₁ ^ 2 := by field_simp
    have h_b : (2 / ν) * (1 - 1 / θ) = (2 / ν) * (ν * β₁ ^ 2) := by rw [hνβ]
    linarith [h_a, h_b]
  have h3 : (2 / ν) * (1 - 1 / θ) = θ ^ 2 - θ := by
    rw [← hθsq]
    field_simp [hθne]
  calc θ ^ 2 - θ = (2 / ν) * (1 - 1 / θ) := by rw [h3.symm]
    _ = 2 * β₁ ^ 2 := by rw [← h2]

-- If β satisfies β² - β = γ² and β ≥ 1/2 then β is the larger root
theorem beta_of_gamma {β γ : ℝ} (hβ : 1 / 2 ≤ β) (h : β ^ 2 - β = γ ^ 2) :
    β = (1 + Real.sqrt (1 + 4 * γ ^ 2)) / 2 := by
  have h1 : (2 * β - 1) ^ 2 = 1 + 4 * γ ^ 2 := by nlinarith
  have hnn : 0 ≤ 1 + 4 * γ ^ 2 := by positivity
  have hge : 0 ≤ 2 * β - 1 := by linarith
  have hsqrt_eq : Real.sqrt ((2 * β - 1) ^ 2) = 2 * β - 1 := Real.sqrt_sq hge
  calc β = ((2 * β - 1) + 1) / 2 := by ring
    _ = (Real.sqrt ((2 * β - 1) ^ 2) + 1) / 2 := by rw [hsqrt_eq]
    _ = (Real.sqrt (1 + 4 * γ ^ 2) + 1) / 2 := by rw [h1]
    _ = (1 + Real.sqrt (1 + 4 * γ ^ 2)) / 2 := by ring

#print axioms Psi0
#print axioms tail_last_eq
#print axioms psi0_tightness_sqrt
#print axioms sqrt_tightness_imp_psi0
#print axioms delta_eq_nu_beta
#print axioms beta_recurrence
#print axioms psi0_beta_eq
#print axioms beta_last_one
#print axioms beta_last_one'
#print axioms zeroth_to_theta
#print axioms beta_of_gamma

end Submission2026.WeakCurvature
