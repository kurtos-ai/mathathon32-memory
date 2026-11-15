module

public import Continuation.Smooth.Energy
public import Continuation.Smooth.OGM
public import Benchmarks.Smooth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace OGMWeighted
open SmoothBenchmark SmoothOGM

noncomputable def A (N k : ℕ) : ℝ := if k < N then 2 * theta N k ^ 2 else theta N k ^ 2
noncomputable def B (N k : ℕ) : ℝ := if k < N then 2 * theta N k else theta N k

theorem theta_mul_sub_one_standard (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    theta N k * (theta N k - 1) = theta N (k - 1) ^ 2 := by
  have hrec := theta_recurrence_standard N k hk hkN
  have hpos : 0 ≤ 1 + 4 * theta N (k - 1) ^ 2 := by positivity
  have h_eq : theta N k = (1 + Real.sqrt (1 + 4 * theta N (k - 1) ^ 2)) / 2 := hrec
  rw [h_eq]
  have hsq : Real.sqrt (1 + 4 * theta N (k - 1) ^ 2) ^ 2 = 1 + 4 * theta N (k - 1) ^ 2 := Real.sq_sqrt hpos
  nlinarith [hsq]

theorem theta_mul_sub_one_final (N : ℕ) (hN : 1 ≤ N) :
    theta N N * (theta N N - 1) = 2 * theta N (N - 1) ^ 2 := by
  have hrec := theta_recurrence_final N hN
  have hpos : 0 ≤ 1 + 8 * theta N (N - 1) ^ 2 := by positivity
  have h_eq : theta N N = (1 + Real.sqrt (1 + 8 * theta N (N - 1) ^ 2)) / 2 := hrec
  rw [h_eq]
  have hsq : Real.sqrt (1 + 8 * theta N (N - 1) ^ 2) ^ 2 = 1 + 8 * theta N (N - 1) ^ 2 := Real.sq_sqrt hpos
  nlinarith [hsq]

theorem a_add_e (N : ℕ) (L : ℝ) (hL : L ≠ 0) (k j : ℕ) (hj : j < k) (hk : k ≤ N) :
    ogmACoeff N L k j + ogmECoeff N L k j = -2 * theta N j / L := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hjk : j < n
    · have hk' : n ≤ N := by omega
      have hkN : n < N := by omega
      have h1 : ogmACoeff N L (n+1) j = ogmACoeff N L n j + (1 / theta N (n+1)) * ogmECoeff N L n j := aCoeff_succ_lt N L n j hkN hjk
      have h2 : ogmECoeff N L (n+1) j = (1 - 1 / theta N (n+1)) * ogmECoeff N L n j := eCoeff_succ_lt N L n j hkN hjk
      have hih : ogmACoeff N L n j + ogmECoeff N L n j = -2 * theta N j / L := ih hjk hk'
      calc ogmACoeff N L (n+1) j + ogmECoeff N L (n+1) j
          = ogmACoeff N L n j + 1 / theta N (n+1) * ogmECoeff N L n j + (1 - 1 / theta N (n+1)) * ogmECoeff N L n j := by rw [h1, h2]
        _ = ogmACoeff N L n j + ogmECoeff N L n j := by ring
        _ = -2 * theta N j / L := hih
    · have hj_eq : j = n := by omega
      have hkN : n < N := by omega
      have h1 : ogmACoeff N L (n+1) n = -(1 + (2 * theta N n - 1) / theta N (n+1)) / L := aCoeff_succ_eq N L n hkN
      have h2 : ogmECoeff N L (n+1) n = -(2 * theta N n - 1) * (1 - 1 / theta N (n+1)) / L := eCoeff_succ_eq N L n hkN
      have hθ_ne : theta N (n+1) ≠ 0 := ne_of_gt (theta_pos N (n+1) (by omega))
      rw [hj_eq, h1, h2]
      field_simp
      ring

theorem a_add_e_one (N k j : ℕ) (hj : j < k) (hk : k ≤ N) :
    ogmACoeff N (1:ℝ) k j + ogmECoeff N (1:ℝ) k j = -2 * theta N j := by
  have h := a_add_e N (1:ℝ) (by norm_num) k j hj hk
  simpa using h

theorem ogmACoeff_self_zero (N : ℕ) (k : ℕ) (hk : k ≤ N) : ogmACoeff N (1:ℝ) k k = 0 := by
  cases k with
  | zero => simp [ogmACoeff, ogmCoeffs]
  | succ n =>
    have hkN : n < N := by omega
    simp only [ogmACoeff, ogmCoeffs, hkN, dite_true]
    simp only [show ¬(n+1 < n) from by omega, show ¬(n+1 = n) from by omega, ite_false]

theorem A_eq_B_mul_theta (N k : ℕ) (hk : k ≤ N) : A N k = B N k * theta N k := by
  unfold A B
  by_cases hkN : k < N
  · simp [hkN, pow_two]
    ring
  · simp [hkN]
    ring

theorem A_mul_one_sub_inv (N k : ℕ) (hk : k < N) :
    A N (k+1) * (1 - 1 / theta N (k+1)) = A N k := by
  have htheta_pos : 0 < theta N (k+1) := theta_pos N (k+1) (by omega)
  have htheta_ne : theta N (k+1) ≠ 0 := ne_of_gt htheta_pos
  by_cases hk1 : k + 1 < N
  · have hAk1 : A N (k+1) = 2 * theta N (k+1) ^ 2 := by unfold A; simp [hk1]
    have hAk : A N k = 2 * theta N k ^ 2 := by unfold A; simp [show k < N from by omega]
    rw [hAk1, hAk]
    have hprod : theta N (k+1) * (theta N (k+1) - 1) = theta N k ^ 2 := by
      have hk_le : 1 ≤ k+1 := by omega
      have h := theta_mul_sub_one_standard N (k+1) hk_le hk1
      have hkm1 : k+1 - 1 = k := by omega
      rw [hkm1] at h
      exact h
    have h1 : (1 - 1 / theta N (k+1)) = (theta N (k+1) - 1) / theta N (k+1) := by field_simp
    rw [h1]
    have h2 : 2 * theta N (k+1) ^ 2 * ((theta N (k+1) - 1) / theta N (k+1)) = 2 * theta N (k+1) * (theta N (k+1) - 1) := by field_simp
    rw [h2]
    nlinarith
  · have hk_eq : k + 1 = N := by omega
    have hAk1 : A N (k+1) = theta N (k+1) ^ 2 := by unfold A; simp [hk1]
    have hAk : A N k = 2 * theta N k ^ 2 := by unfold A; simp [show k < N from by omega]
    rw [hAk1, hAk]
    have htheta_eq : theta N (k+1) = theta N N := by rw [hk_eq]
    rw [htheta_eq]
    have hprod : theta N N * (theta N N - 1) = 2 * theta N k ^ 2 := by
      have h := theta_mul_sub_one_final N (by omega)
      have hk_eq2 : N - 1 = k := by omega
      rw [hk_eq2] at h
      exact h
    have hthN_ne : theta N N ≠ 0 := ne_of_gt (theta_pos N N le_rfl)
    have h1 : (1 - 1 / theta N N) = (theta N N - 1) / theta N N := by field_simp
    rw [h1]
    have h2 : theta N N ^ 2 * ((theta N N - 1) / theta N N) = theta N N * (theta N N - 1) := by field_simp
    rw [h2]
    exact hprod

theorem A_sub_B_eq_A_prev (N k : ℕ) (hk : k < N) : A N (k+1) - B N (k+1) = A N k := by
  have hA_eq : A N (k+1) = B N (k+1) * theta N (k+1) := A_eq_B_mul_theta N (k+1) (by omega)
  have htheta_pos : 0 < theta N (k+1) := theta_pos N (k+1) (by omega)
  have htheta_ne : theta N (k+1) ≠ 0 := ne_of_gt htheta_pos
  have hmain := A_mul_one_sub_inv N k hk
  have h1 : A N (k+1) * (1 - 1 / theta N (k+1)) = A N (k+1) - A N (k+1) / theta N (k+1) := by field_simp
  rw [h1] at hmain
  have h2 : A N (k+1) / theta N (k+1) = B N (k+1) := by rw [hA_eq]; field_simp
  rw [h2] at hmain
  linarith

theorem A_div_theta_eq_B (N k : ℕ) (hk : k < N) : A N (k+1) / theta N (k+1) = B N (k+1) := by
  have hA_eq : A N (k+1) = B N (k+1) * theta N (k+1) := A_eq_B_mul_theta N (k+1) (by omega)
  have htheta_pos : 0 < theta N (k+1) := theta_pos N (k+1) (by omega)
  have htheta_ne : theta N (k+1) ≠ 0 := ne_of_gt htheta_pos
  rw [hA_eq]
  field_simp

theorem B_pos (N k : ℕ) (hk : k ≤ N) : 0 < B N k := by
  unfold B
  by_cases hkN : k < N
  · simp [hkN]
    exact theta_pos N k (by omega)
  · simp [hkN]
    exact theta_pos N k hk

theorem weightedRecurrence (N j k : ℕ) (hj : j ≤ k) (hk : k < N) :
    A N (k+1) * ogmACoeff N (1:ℝ) (k+1) j =
      A N k * ogmACoeff N (1:ℝ) k j - B N j * B N (k+1) - (if j = k then A N k else 0) := by
  have hA_sub_B : A N (k+1) - B N (k+1) = A N k := A_sub_B_eq_A_prev N k hk
  have hA_div_B : A N (k+1) / theta N (k+1) = B N (k+1) := A_div_theta_eq_B N k hk
  by_cases hjk : j < k
  · have hj_lt : j < k := hjk
    have hj_lt_N : j < N := by omega
    have hk_le_N : k ≤ N := by omega
    have ha_succ : ogmACoeff N (1:ℝ) (k+1) j = ogmACoeff N (1:ℝ) k j + (1 / theta N (k+1)) * ogmECoeff N (1:ℝ) k j :=
      aCoeff_succ_lt N (1:ℝ) k j hk hj_lt
    have he_eq : ogmECoeff N (1:ℝ) k j = -2 * theta N j - ogmACoeff N (1:ℝ) k j := by
      have h_ae := a_add_e_one N k j hj_lt hk_le_N
      linarith
    have hB_j : B N j = 2 * theta N j := by unfold B; simp [hj_lt_N]
    have h1 : A N (k+1) * ogmACoeff N (1:ℝ) (k+1) j =
        A N (k+1) * ogmACoeff N (1:ℝ) k j + A N (k+1) / theta N (k+1) * ogmECoeff N (1:ℝ) k j := by
      rw [ha_succ]
      ring
    rw [h1, hA_div_B, he_eq]
    have h2 : A N (k+1) * ogmACoeff N (1:ℝ) k j + B N (k+1) * (-2 * theta N j - ogmACoeff N (1:ℝ) k j) =
        (A N (k+1) - B N (k+1)) * ogmACoeff N (1:ℝ) k j - 2 * theta N j * B N (k+1) := by ring
    rw [h2, hA_sub_B]
    have hB_j_eq : 2 * theta N j * B N (k+1) = B N j * B N (k+1) := by rw [← hB_j]
    rw [hB_j_eq]
    have hif : (if j = k then A N k else (0:ℝ)) = 0 := by simp [show j ≠ k from by omega]
    rw [hif]
    ring
  · have hj_eq : j = k := by omega
    have ha_zero : ogmACoeff N (1:ℝ) k j = 0 := by rw [hj_eq]; exact ogmACoeff_self_zero N k (by omega)
    have ha_succ : ogmACoeff N (1:ℝ) (k+1) j = -(1 + (2 * theta N k - 1) / theta N (k+1)) := by
      rw [hj_eq]
      have h := aCoeff_succ_eq N (1:ℝ) k hk
      simpa using h
    have hB_k : B N k = 2 * theta N k := by unfold B; simp [show k < N from hk]
    have hB_j_eq : B N j = B N k := by rw [hj_eq]
    have hLHS : A N (k+1) * ogmACoeff N (1:ℝ) (k+1) j = A N (k+1) * (-(1 + (2 * theta N k - 1) / theta N (k+1))) := by rw [ha_succ]
    rw [hLHS]
    have h1 : A N (k+1) * (-(1 + (2 * theta N k - 1) / theta N (k+1))) =
        -A N (k+1) - A N (k+1) / theta N (k+1) * (2 * theta N k - 1) := by
      have hdiv : (2 * theta N k - 1) / theta N (k+1) = (1 / theta N (k+1)) * (2 * theta N k - 1) := by ring
      rw [hdiv]
      have hring : A N (k+1) * (-(1 + 1 / theta N (k+1) * (2 * theta N k - 1))) =
          -(A N (k+1) * 1) - A N (k+1) * (1 / theta N (k+1) * (2 * theta N k - 1)) := by ring
      rw [hring]
      have hdiv2 : A N (k+1) * (1 / theta N (k+1) * (2 * theta N k - 1)) = A N (k+1) / theta N (k+1) * (2 * theta N k - 1) := by ring
      rw [hdiv2]
      ring
    rw [h1, hA_div_B]
    have hif : (if j = k then A N k else (0:ℝ)) = A N k := by simp [hj_eq]
    have ha_zero_rw : A N k * ogmACoeff N (1:ℝ) k j = 0 := by rw [ha_zero]; ring
    have hB_jk : B N j * B N (k+1) = B N k * B N (k+1) := by rw [hB_j_eq]
    have hRHS : A N k * ogmACoeff N (1:ℝ) k j - B N j * B N (k+1) - (if j = k then A N k else 0) =
        - B N k * B N (k+1) - A N k := by rw [ha_zero_rw, hB_jk, hif]; ring
    rw [hRHS, hB_k]
    nlinarith [hA_sub_B]


end OGMWeighted
end
