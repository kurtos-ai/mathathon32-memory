module

public import Submission2026.Separation.RidgeBalance
public import Continuation.Smooth.WeightedCoefficient
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace Submission2026.Separation.Current

open SmoothBenchmark OGMWeighted Submission2026.Separation

/-- Derive the sole elementary theta identity needed here directly from the
canonical recurrence, without importing the remote baseline copies. -/
private theorem theta4_one_exact : theta 4 1 = (1 + Real.sqrt 5) / 2 := by
  have h := theta_recurrence_standard 4 1 (by omega) (by omega)
  norm_num [theta_zero] at h
  exact h

private lemma le_sqrt_of_sq_le {x b : ℝ} (hb : 0 ≤ b) (h : b ^ 2 ≤ x) :
    b ≤ Real.sqrt x := by
  have hs := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hb] at hs

private lemma sqrt_le_of_sq_le {x b : ℝ} (hb : 0 ≤ b) (h : x ≤ b ^ 2) :
    Real.sqrt x ≤ b := by
  calc
    Real.sqrt x ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
    _ = b := Real.sqrt_sq hb

/-- `ρ0` and the four upper prefix envelopes from Lemma B.11. -/
def rho0 : ℝ := 523 / 10000
def U0 : ℝ := 2 * rho0 * theta 4 0 ^ 2
def U1 : ℝ := 2 * rho0 * theta 4 1 ^ 2
def U2 : ℝ := 2 * rho0 * theta 4 2 ^ 2
def U3 : ℝ := 2 * rho0 * theta 4 3 ^ 2

/-- The backward lower envelopes from Lemma B.11. -/
def L3 : ℝ := 1 - Real.sqrt rho0
def L2 : ℝ := L3 - Real.sqrt (2 * rho0 * L3)
def L1 : ℝ := L2 - Real.sqrt (2 * rho0 * L2)
def L0 : ℝ := L1 - Real.sqrt (2 * rho0 * L1)

theorem theta4_one_sq : theta 4 1 ^ 2 = theta 4 1 + 1 := by
  have h := theta_mul_sub_one_standard 4 1 (by omega) (by omega)
  rw [theta_zero] at h
  nlinarith

theorem theta4_two_sq : theta 4 2 ^ 2 = theta 4 2 + theta 4 1 ^ 2 := by
  have h := theta_mul_sub_one_standard 4 2 (by omega) (by omega)
  norm_num at h
  nlinarith

theorem theta4_three_sq : theta 4 3 ^ 2 = theta 4 3 + theta 4 2 ^ 2 := by
  have h := theta_mul_sub_one_standard 4 3 (by omega) (by omega)
  norm_num at h
  nlinarith

theorem theta4_one_tight_upper : theta 4 1 ≤ (1618034 / 1000000 : ℝ) := by
  rw [theta4_one_exact]
  have hs : Real.sqrt 5 ≤ (2236068 / 1000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  linarith

theorem theta4_two_tight_upper : theta 4 2 ≤ (2193528 / 1000000 : ℝ) := by
  have hrec := theta_recurrence_standard 4 2 (by omega) (by omega)
  norm_num at hrec
  have hsq1 : theta 4 1 ^ 2 ≤ (1618034 / 1000000 : ℝ) + 1 := by
    rw [theta4_one_sq]
    linarith [theta4_one_tight_upper]
  have hs : Real.sqrt (1 + 4 * theta 4 1 ^ 2) ≤ (3387056 / 1000000 : ℝ) := by
    apply sqrt_le_of_sq_le (by norm_num)
    nlinarith
  rw [hrec]
  linarith

theorem theta4_three_tight_upper : theta 4 3 ≤ (2749792 / 1000000 : ℝ) := by
  have hrec := theta_recurrence_standard 4 3 (by omega) (by omega)
  norm_num at hrec
  have hsq1 : theta 4 1 ^ 2 ≤ (1618034 / 1000000 : ℝ) + 1 := by
    rw [theta4_one_sq]
    linarith [theta4_one_tight_upper]
  have hsq2 : theta 4 2 ^ 2 ≤
      (2193528 / 1000000 : ℝ) + ((1618034 / 1000000 : ℝ) + 1) := by
    rw [theta4_two_sq]
    nlinarith [theta4_two_tight_upper]
  have hs : Real.sqrt (1 + 4 * theta 4 2 ^ 2) ≤ (4499584 / 1000000 : ℝ) := by
    apply sqrt_le_of_sq_le (by norm_num)
    nlinarith
  rw [hrec]
  linarith

theorem U0_exact : U0 = (1046 / 10000 : ℝ) := by
  unfold U0 rho0
  rw [theta_zero]
  norm_num

theorem U1_upper : U1 ≤ (2738464 / 10000000 : ℝ) := by
  have hsq : theta 4 1 ^ 2 ≤ (1618034 / 1000000 : ℝ) + 1 := by
    rw [theta4_one_sq]
    linarith [theta4_one_tight_upper]
  unfold U1 rho0
  nlinarith

theorem U2_upper : U2 ≤ (5032894 / 10000000 : ℝ) := by
  have hsq1 : theta 4 1 ^ 2 ≤ (1618034 / 1000000 : ℝ) + 1 := by
    rw [theta4_one_sq]
    linarith [theta4_one_tight_upper]
  have hsq2 : theta 4 2 ^ 2 ≤
      (2193528 / 1000000 : ℝ) + ((1618034 / 1000000 : ℝ) + 1) := by
    rw [theta4_two_sq]
    nlinarith [theta4_two_tight_upper]
  unfold U2 rho0
  nlinarith

theorem U3_upper : U3 ≤ (7909177 / 10000000 : ℝ) := by
  have hsq1 : theta 4 1 ^ 2 ≤ (1618034 / 1000000 : ℝ) + 1 := by
    rw [theta4_one_sq]
    linarith [theta4_one_tight_upper]
  have hsq2 : theta 4 2 ^ 2 ≤
      (2193528 / 1000000 : ℝ) + ((1618034 / 1000000 : ℝ) + 1) := by
    rw [theta4_two_sq]
    nlinarith [theta4_two_tight_upper]
  have hsq3 : theta 4 3 ^ 2 ≤
      (2749792 / 1000000 : ℝ) +
        ((2193528 / 1000000 : ℝ) + ((1618034 / 1000000 : ℝ) + 1)) := by
    rw [theta4_three_sq]
    nlinarith [theta4_three_tight_upper]
  unfold U3 rho0
  nlinarith

theorem sqrt_rho0_bounds :
    (2286919 / 10000000 : ℝ) ≤ Real.sqrt rho0 ∧
      Real.sqrt rho0 ≤ (228692 / 1000000 : ℝ) := by
  constructor
  · apply le_sqrt_of_sq_le (by norm_num)
    unfold rho0
    norm_num
  · apply sqrt_le_of_sq_le (by norm_num)
    unfold rho0
    norm_num

theorem L3_bounds :
    (771308 / 1000000 : ℝ) ≤ L3 ∧ L3 ≤ (7713081 / 10000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := sqrt_rho0_bounds
  unfold L3
  constructor <;> linarith

private theorem backward_lower {rho x lo hi next : ℝ}
    (hrho : 0 < rho) (hx : 0 ≤ x) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hcap : 0 ≤ lo - next) (hsq : 2 * rho * hi ≤ (lo - next) ^ 2) :
    next ≤ x - Real.sqrt (2 * rho * x) := by
  have hs : Real.sqrt (2 * rho * x) ≤ lo - next := by
    apply sqrt_le_of_sq_le hcap
    exact le_trans (mul_le_mul_of_nonneg_left hhi (by positivity)) hsq
  linarith

private theorem backward_upper {rho x lo hi next : ℝ}
    (hrho : 0 < rho) (hx : 0 ≤ x) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hcap : 0 ≤ hi - next) (hsq : (hi - next) ^ 2 ≤ 2 * rho * lo) :
    x - Real.sqrt (2 * rho * x) ≤ next := by
  have hs : hi - next ≤ Real.sqrt (2 * rho * x) := by
    apply le_sqrt_of_sq_le hcap
    exact hsq.trans (mul_le_mul_of_nonneg_left hlo (by positivity))
  linarith

theorem L2_bounds :
    (487267 / 1000000 : ℝ) ≤ L2 ∧ L2 ≤ (4872681 / 10000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := L3_bounds
  have hx : 0 ≤ L3 := by linarith
  constructor
  · exact backward_lower (by unfold rho0; norm_num) hx hlo hhi (by norm_num)
      (by unfold rho0; norm_num)
  · exact backward_upper (by unfold rho0; norm_num) hx hlo hhi (by norm_num)
      (by unfold rho0; norm_num)

theorem L1_bounds :
    (261505 / 1000000 : ℝ) ≤ L1 ∧ L1 ≤ (261507 / 1000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := L2_bounds
  have hx : 0 ≤ L2 := by linarith
  constructor
  · exact backward_lower (by unfold rho0; norm_num) hx hlo hhi (by norm_num)
      (by unfold rho0; norm_num)
  · exact backward_upper (by unfold rho0; norm_num) hx hlo hhi (by norm_num)
      (by unfold rho0; norm_num)

theorem L0_lower : (961 / 10000 : ℝ) ≤ L0 := by
  obtain ⟨hlo, hhi⟩ := L1_bounds
  have hx : 0 ≤ L1 := by linarith
  exact backward_lower (by unfold rho0; norm_num) hx hlo hhi (by norm_num)
    (by unfold rho0; norm_num)

/-- A tighter intermediate enclosure needed for the `β0` estimate. -/
theorem L0_lower_tight : (96115 / 1000000 : ℝ) ≤ L0 := by
  obtain ⟨hlo, hhi⟩ := L1_bounds
  have hx : 0 ≤ L1 := by linarith
  exact backward_lower (by unfold rho0; norm_num) hx hlo hhi (by norm_num)
    (by unfold rho0; norm_num)

/-- The printed `δ⁻` inequalities, derived from the recurrence enclosures. -/
theorem delta0_lower : (961 / 10000 : ℝ) ≤ L0 := by
  have h := L0_lower_tight
  linarith
theorem delta1_lower : (1569 / 10000 : ℝ) ≤ L1 - U0 := by
  have h := L1_bounds.1
  rw [U0_exact]
  linarith
theorem delta2_lower : (2134 / 10000 : ℝ) ≤ L2 - U1 := by
  have h := L2_bounds.1
  have hu := U1_upper
  linarith
theorem delta3_lower : (2680 / 10000 : ℝ) ≤ L3 - U2 := by
  have h := L3_bounds.1
  have hu := U2_upper
  linarith
theorem delta4_lower : (2090 / 10000 : ℝ) ≤ 1 - U3 := by
  have hu := U3_upper
  linarith

/-- The printed `δ⁺` inequalities, with exact outward arithmetic. -/
theorem delta0_upper : U0 ≤ (1046 / 10000 : ℝ) := le_of_eq U0_exact
theorem delta1_upper : U1 - L0 ≤ (1778 / 10000 : ℝ) := by
  have h := L0_lower
  have hu := U1_upper
  linarith
theorem delta2_upper : U2 - L1 ≤ (2418 / 10000 : ℝ) := by
  have h := L1_bounds.1
  have hu := U2_upper
  linarith
theorem delta3_upper : U3 - L2 ≤ (3037 / 10000 : ℝ) := by
  have h := L2_bounds.1
  have hu := U3_upper
  linarith
theorem delta4_upper : Real.sqrt rho0 ≤ (2287 / 10000 : ℝ) := by
  have h := sqrt_rho0_bounds.2
  linarith

/-- Exact `β` expressions from Step 2 of Lemma B.11. -/
def beta0Cert : ℝ := L0 ^ 2 / (2 * rho0 * U0)
def beta1Cert : ℝ := (L1 - U0) ^ 2 / (2 * rho0 * U1)
def beta2Cert : ℝ := (L2 - U1) ^ 2 / (2 * rho0 * U2)
def beta3Cert : ℝ := (L3 - U2) ^ 2 / (2 * rho0 * U3)
def beta4Cert : ℝ := 1 - Real.sqrt (1 - (1 - U3) ^ 2 / rho0)

private theorem ratio_lower {rho x y a b : ℝ}
    (hrho : 0 < rho) (hy : 0 < y) (hyb : y ≤ b) (ha : 0 ≤ a) (hax : a ≤ x) :
    a ^ 2 / (2 * rho * b) ≤ x ^ 2 / (2 * rho * y) := by
  apply div_le_div₀ (sq_nonneg x) (by nlinarith) (by positivity)
  exact mul_le_mul_of_nonneg_left hyb (by positivity)

theorem beta0_lower : (8443 / 10000 : ℝ) ≤ beta0Cert := by
  have hu : 0 < U0 := by rw [U0_exact]; norm_num
  calc
    (8443 / 10000 : ℝ) ≤ (96115 / 1000000 : ℝ) ^ 2 / (2 * rho0 * U0) := by
      rw [U0_exact]
      unfold rho0
      norm_num
    _ ≤ beta0Cert := ratio_lower (by unfold rho0; norm_num) hu le_rfl (by norm_num)
      L0_lower_tight

theorem beta1_lower : (8594 / 10000 : ℝ) ≤ beta1Cert := by
  have hu : 0 < U1 := by
    unfold U1 rho0
    have h := theta_pos 4 1 (by omega)
    positivity
  calc
    (8594 / 10000 : ℝ) ≤
        (1569 / 10000 : ℝ) ^ 2 / (2 * rho0 * (2738464 / 10000000 : ℝ)) := by
      unfold rho0
      norm_num
    _ ≤ beta1Cert := ratio_lower (by unfold rho0; norm_num) hu U1_upper (by norm_num)
      delta1_lower

theorem beta2_lower : (8652 / 10000 : ℝ) ≤ beta2Cert := by
  have hu : 0 < U2 := by
    unfold U2 rho0
    have h := theta_pos 4 2 (by omega)
    positivity
  have hx : ((487267 / 1000000 : ℝ) - (2738464 / 10000000 : ℝ)) ≤ L2 - U1 := by
    have hl := L2_bounds.1
    have hu1 := U1_upper
    linarith
  calc
    (8652 / 10000 : ℝ) ≤
        ((487267 / 1000000 : ℝ) - (2738464 / 10000000 : ℝ)) ^ 2 /
          (2 * rho0 * (5032894 / 10000000 : ℝ)) := by
      unfold rho0
      norm_num
    _ ≤ beta2Cert := ratio_lower (by unfold rho0; norm_num) hu U2_upper (by norm_num) hx

theorem beta3_lower : (8682 / 10000 : ℝ) ≤ beta3Cert := by
  have hu : 0 < U3 := by
    unfold U3 rho0
    have h := theta_pos 4 3 (by omega)
    positivity
  have hx : ((771308 / 1000000 : ℝ) - (5032894 / 10000000 : ℝ)) ≤ L3 - U2 := by
    have hl := L3_bounds.1
    have hu2 := U2_upper
    linarith
  calc
    (8682 / 10000 : ℝ) ≤
        ((771308 / 1000000 : ℝ) - (5032894 / 10000000 : ℝ)) ^ 2 /
          (2 * rho0 * (7909177 / 10000000 : ℝ)) := by
      unfold rho0
      norm_num
    _ ≤ beta3Cert := ratio_lower (by unfold rho0; norm_num) hu U3_upper (by norm_num) hx

theorem beta4_lower : (5948 / 10000 : ℝ) ≤ beta4Cert := by
  have hx : (2090823 / 10000000 : ℝ) ≤ 1 - U3 := by
    have hu := U3_upper
    norm_num at hu ⊢
    linarith
  have hxpos : 0 ≤ 1 - U3 := by linarith
  have hrho : 0 < rho0 := by unfold rho0; norm_num
  have hxSq : (2090823 / 10000000 : ℝ) ^ 2 ≤ (1 - U3) ^ 2 := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hxSq (show 0 ≤ rho0 by positivity)
  have hsqrt : Real.sqrt (1 - (1 - U3) ^ 2 / rho0) ≤ (4052 / 10000 : ℝ) := by
    apply sqrt_le_of_sq_le (by norm_num)
    calc
      1 - (1 - U3) ^ 2 / rho0 ≤ 1 - (2090823 / 10000000 : ℝ) ^ 2 / rho0 := by linarith
      _ ≤ (4052 / 10000 : ℝ) ^ 2 := by unfold rho0; norm_num
  unfold beta4Cert
  linarith

/-- All five Step 2 numerical lower bounds in one certificate. -/
theorem B11_beta_enclosures :
    (8443 / 10000 : ℝ) ≤ beta0Cert ∧
    (8594 / 10000 : ℝ) ≤ beta1Cert ∧
    (8652 / 10000 : ℝ) ≤ beta2Cert ∧
    (8682 / 10000 : ℝ) ≤ beta3Cert ∧
    (5948 / 10000 : ℝ) ≤ beta4Cert := by
  exact ⟨beta0_lower, beta1_lower, beta2_lower, beta3_lower, beta4_lower⟩

end Submission2026.Separation.Current
