module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace Submission2026.Separation.Current

/-- The upper square-root consequence of Appendix B.11's inequality (B.12),
using only `0 ≤ b ≤ 1` and nonnegativity of the weight and prefix sum. -/
theorem weight_le_sqrt_of_B12 {rho delta b D : ℝ}
    (hrho : 0 < rho) (hdelta : 0 ≤ delta) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hD : 0 ≤ D) (hB12 : delta ^ 2 ≤ 2 * rho * b * D) :
    delta ≤ Real.sqrt (2 * rho * D) := by
  have hbound : delta ^ 2 ≤ 2 * rho * D := by
    calc
      delta ^ 2 ≤ 2 * rho * b * D := hB12
      _ ≤ 2 * rho * D := by
        have hcoef : 0 ≤ 2 * rho * D := by positivity
        calc
          2 * rho * b * D = (2 * rho * D) * b := by ring
          _ ≤ (2 * rho * D) * 1 := mul_le_mul_of_nonneg_left hb1 hcoef
          _ = 2 * rho * D := by ring
  have h := Real.sqrt_le_sqrt hbound
  rwa [Real.sqrt_sq hdelta] at h

/-- The next-prefix upper estimate used in Step 1 of Lemma B.11. -/
theorem next_prefix_le_of_B12 {rho delta b D : ℝ}
    (hrho : 0 < rho) (hdelta : 0 ≤ delta) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hD : 0 ≤ D) (hB12 : delta ^ 2 ≤ 2 * rho * b * D) :
    D + delta ≤ D + Real.sqrt (2 * rho * D) := by
  have h := weight_le_sqrt_of_B12 hrho hdelta hb0 hb1 hD hB12
  linarith

/-- The nonterminal `b_i` lower bound in Step 2 of Lemma B.11.  The
lower/upper constants remain arbitrary, so this theorem is independent of any
decimal enclosure. -/
theorem b_lower_of_B12 {rho delta b D lower upper : ℝ}
    (hrho : 0 < rho) (hU : 0 < upper) (hdelta : 0 ≤ delta) (hlower : 0 ≤ lower)
    (hb : 0 ≤ b) (hB12 : delta ^ 2 ≤ 2 * rho * b * D)
    (hDU : D ≤ upper) (hlo : lower ≤ delta) :
    lower ^ 2 / (2 * rho * upper) ≤ b := by
  have hloSq : lower ^ 2 ≤ delta ^ 2 := by nlinarith
  have hmul : 2 * rho * b * D ≤ 2 * rho * b * upper := by
    exact mul_le_mul_of_nonneg_left hDU (by positivity)
  have hbound : lower ^ 2 ≤ 2 * rho * b * upper := hloSq.trans (hB12.trans hmul)
  apply (div_le_iff₀ (show 0 < 2 * rho * upper by positivity)).mpr
  nlinarith

/-- The terminal quadratic consequence of (B.12), algebraically equivalent to
`(1 - b4)^2 ≤ 1 - δ4^2 / ρ0`; here the numerator can be any valid lower
weight enclosure. -/
theorem one_sub_terminal_b_sq_le_of_B12 {rho delta b lower : ℝ}
    (hrho : 0 < rho) (hdelta : 0 ≤ delta) (hlower : 0 ≤ lower)
    (hB12 : delta ^ 2 ≤ rho * (2 * b - b ^ 2)) (hlo : lower ≤ delta) :
    (1 - b) ^ 2 ≤ 1 - lower ^ 2 / rho := by
  have hloSq : lower ^ 2 ≤ delta ^ 2 := by nlinarith
  have hdiv : lower ^ 2 / rho ≤ 2 * b - b ^ 2 := by
    apply (div_le_iff₀ hrho).mpr
    nlinarith
  nlinarith

/-- The corresponding square-root lower bound for the terminal component,
with the radicand nonnegativity needed to use the square root explicitly. -/
theorem terminal_b_lower_of_sq {rho b lower : ℝ}
    (hrad : 0 ≤ 1 - lower ^ 2 / rho) (hb1 : b ≤ 1)
    (hsq : (1 - b) ^ 2 ≤ 1 - lower ^ 2 / rho) :
    1 - Real.sqrt (1 - lower ^ 2 / rho) ≤ b := by
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by linarith)] at h
  linarith

/-- Combined terminal Step 2 consequence of (B.12). -/
theorem terminal_b_lower_of_B12 {rho delta b lower : ℝ}
    (hrho : 0 < rho) (hdelta : 0 ≤ delta) (hlower : 0 ≤ lower)
    (hB12 : delta ^ 2 ≤ rho * (2 * b - b ^ 2)) (hlo : lower ≤ delta)
    (hb1 : b ≤ 1) (hrad : 0 ≤ 1 - lower ^ 2 / rho) :
    1 - Real.sqrt (1 - lower ^ 2 / rho) ≤ b := by
  exact terminal_b_lower_of_sq hrad hb1
    (one_sub_terminal_b_sq_le_of_B12 hrho hdelta hlower hB12 hlo)

end Submission2026.Separation.Current
