module
public import Mathlib
public import Benchmarks.Smooth

open EuclideanSpace

@[expose] public section
noncomputable section
namespace SmoothDrori

theorem theta_final_gt_one_local (N : ℕ) (hN : 1 ≤ N) :
    1 < SmoothBenchmark.theta N N := by
  have hrec := SmoothBenchmark.theta_recurrence_final N hN
  have hge : 1 ≤ SmoothBenchmark.theta N (N-1) :=
    SmoothBenchmark.theta_ge_one N (N-1) (by omega)
  have h5 : 1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2 ≥ 9 := by nlinarith
  have h6 : Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) ≥ 3 := by
    have h7 : Real.sqrt 9 = (3 : ℝ) := by
      have h8 : (3 : ℝ) ≥ 0 := by positivity
      have h9 : (3 : ℝ) ^ 2 = 9 := by ring
      rw [← h9, Real.sqrt_sq h8]
    have h10 : Real.sqrt 9 ≤ Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) :=
      Real.sqrt_le_sqrt h5
    linarith
  linarith

theorem hardF_algebra (N : ℕ) (hN : 1 ≤ N) (L R : ℝ) :
    L / 2 * ((SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) + 1) *
      ((SmoothBenchmark.theta N N - 1) /
        (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2)) =
      L * R ^ 2 / (2 * SmoothBenchmark.theta N N ^ 2) := by
  have hpos : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
  have hgt : 1 < SmoothBenchmark.theta N N := theta_final_gt_one_local N hN
  have hne0 : SmoothBenchmark.theta N N ≠ 0 := ne_of_gt hpos
  have hne1 : SmoothBenchmark.theta N N - 1 ≠ 0 := by linarith
  have hne2 : 2 * SmoothBenchmark.theta N N - 1 ≠ 0 := by linarith
  field_simp
  ring

noncomputable def zetaStar (N : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  if h1 : n = N+2 then 0
  else if h2 : n = N+1 then (SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2
  else if h3 : n = N then SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) * zetaStar N R (N+1)
  else if h4 : n < N then (2 * SmoothBenchmark.theta N n / (2 * SmoothBenchmark.theta N n - 1)) * zetaStar N R (n+1)
  else 0
termination_by N+1 - n

theorem zetaStar_last (N : ℕ) (R : ℝ) : zetaStar N R (N+2) = 0 := by
  unfold zetaStar
  simp

noncomputable def hardG (N : ℕ) (L R : ℝ) (i : ℕ) : EuclideanSpace ℝ (Fin (N+1)) :=
  if h : i ≤ N then
    EuclideanSpace.single (⟨i, by omega⟩ : Fin (N+1)) (L * Real.sqrt (zetaStar N R i - zetaStar N R (i+1)))
  else 0

noncomputable def hardX (N : ℕ) (R : ℝ) (i : ℕ) : EuclideanSpace ℝ (Fin (N+1)) :=
  ∑ j : Fin (N+1), if h : j.val < i then
    let d_j := zetaStar N R j.val - zetaStar N R (j.val + 1)
    (-(zetaStar N R j.val - zetaStar N R (i+1)) / Real.sqrt d_j) • EuclideanSpace.single j (1 : ℝ)
  else 0

noncomputable def hardF (N : ℕ) (L R : ℝ) (i : ℕ) : ℝ :=
  if h : i ≤ N then L / 2 * (zetaStar N R i + zetaStar N R (i+1)) else 0

theorem hardG_norm_sq (N : ℕ) (L R : ℝ) (i : ℕ) (hi : i ≤ N) (hd : 0 ≤ zetaStar N R i - zetaStar N R (i+1)) :
    ‖hardG N L R i‖ ^ 2 = L ^ 2 * (zetaStar N R i - zetaStar N R (i+1)) := by
  unfold hardG
  simp only [hi, dite_true]
  have h1 : ‖EuclideanSpace.single (⟨i, by omega⟩ : Fin (N+1)) (L * Real.sqrt (zetaStar N R i - zetaStar N R (i+1)))‖ = ‖L * Real.sqrt (zetaStar N R i - zetaStar N R (i+1))‖ := by
    rw [PiLp.norm_single]
  have h2 : ‖L * Real.sqrt (zetaStar N R i - zetaStar N R (i+1))‖ ^ 2 = (L * Real.sqrt (zetaStar N R i - zetaStar N R (i+1))) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [h1, h2]
  have hsq : Real.sqrt (zetaStar N R i - zetaStar N R (i+1)) ^ 2 = zetaStar N R i - zetaStar N R (i+1) := Real.sq_sqrt hd
  calc (L * Real.sqrt (zetaStar N R i - zetaStar N R (i+1))) ^ 2
      = L ^ 2 * Real.sqrt (zetaStar N R i - zetaStar N R (i+1)) ^ 2 := by ring
    _ = L ^ 2 * (zetaStar N R i - zetaStar N R (i+1)) := by rw [hsq]

theorem zetaStar_pos_aux (N : ℕ) (hN : 1 ≤ N) (R : ℝ) (hR : 0 < R) : 0 < (SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2 := by
  have h1 : 1 < SmoothBenchmark.theta N N := by
    have h2 : SmoothBenchmark.theta N N = (1 + Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2)) / 2 := SmoothBenchmark.theta_recurrence_final N hN
    have h3 : 0 < SmoothBenchmark.theta N (N-1) := SmoothBenchmark.theta_pos N (N-1) (by omega)
    have h4 : 1 ≤ SmoothBenchmark.theta N (N-1) := SmoothBenchmark.theta_ge_one N (N-1) (by omega)
    have h5 : 1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2 ≥ 9 := by nlinarith
    have h6 : Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) ≥ 3 := by
      have h7 : Real.sqrt 9 = (3 : ℝ) := by
        have h8 : (3 : ℝ) ≥ 0 := by positivity
        have h9 : (3 : ℝ) ^ 2 = 9 := by ring
        rw [← h9, Real.sqrt_sq h8]
      have h10 : Real.sqrt 9 ≤ Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) := Real.sqrt_le_sqrt h5
      linarith
    linarith
  have h2 : 0 < SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1) := by
    have h3 : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
    have h4 : 0 < 2 * SmoothBenchmark.theta N N - 1 := by linarith
    positivity
  have h3 : 0 < SmoothBenchmark.theta N N - 1 := by linarith
  positivity

theorem zetaStar_Nplus1_eq (N : ℕ) (R : ℝ) : zetaStar N R (N+1) = (SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2 := by
  conv => lhs; unfold zetaStar
  simp

theorem zetaStar_N_eq (N : ℕ) (R : ℝ) (hN : 1 ≤ N) : zetaStar N R N = SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) * zetaStar N R (N+1) := by
  conv => lhs; unfold zetaStar
  simp

theorem zetaStar_ltN_eq (N : ℕ) (R : ℝ) (n : ℕ) (hn : n < N) : zetaStar N R n = (2 * SmoothBenchmark.theta N n / (2 * SmoothBenchmark.theta N n - 1)) * zetaStar N R (n+1) := by
  conv => lhs; unfold zetaStar
  have h1 : ¬ (n = N+2) := by omega
  have h2 : ¬ (n = N+1) := by omega
  have h3 : ¬ (n = N) := by omega
  simp [h1, h2, h3, hn]

theorem theta_gt_one_final (N : ℕ) (hN : 1 ≤ N) : 1 < SmoothBenchmark.theta N N := by
  have hrec := SmoothBenchmark.theta_recurrence_final N hN
  have h5 : 1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2 ≥ 9 := by have hge : 1 ≤ SmoothBenchmark.theta N (N-1) := SmoothBenchmark.theta_ge_one N (N-1) (by omega); nlinarith
  have h6 : Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) ≥ 3 := by
    have h7 : Real.sqrt 9 = (3 : ℝ) := by
      have h8 : (3 : ℝ) ≥ 0 := by positivity
      have h9 : (3 : ℝ) ^ 2 = 9 := by ring
      rw [← h9, Real.sqrt_sq h8]
    have h10 : Real.sqrt 9 ≤ Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) := Real.sqrt_le_sqrt h5
    linarith
  linarith

theorem theta_two_mul_sub_one_pos (N n : ℕ) (hn : n ≤ N) : 0 < 2 * SmoothBenchmark.theta N n - 1 := by have h1 : 1 ≤ SmoothBenchmark.theta N n := SmoothBenchmark.theta_ge_one N n hn; linarith

theorem coeff_pos_N (N : ℕ) (hN : 1 ≤ N) : 0 < SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) := by
  have h1 : 1 < SmoothBenchmark.theta N N := theta_gt_one_final N hN
  positivity

theorem coeff_pos_ltN (N n : ℕ) (hn : n < N) : 0 < 2 * SmoothBenchmark.theta N n / (2 * SmoothBenchmark.theta N n - 1) := by
  have h1 : 1 ≤ SmoothBenchmark.theta N n := SmoothBenchmark.theta_ge_one N n (by omega)
  have h2 : 0 < 2 * SmoothBenchmark.theta N n - 1 := by linarith
  positivity

theorem zetaStar_nonneg_aux (N : ℕ) (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : k ≤ N+1) : 0 ≤ zetaStar N R (N+1 - k) := by
  induction k with
  | zero =>
    simp
    rw [zetaStar_Nplus1_eq]
    by_cases hN0 : N = 0
    · have htheta : SmoothBenchmark.theta 0 0 = 1 := SmoothBenchmark.theta_zero 0
      subst hN0
      rw [htheta]
      simp
    · have hN1 : 1 ≤ N := by omega
      have h1 : 1 < SmoothBenchmark.theta N N := theta_gt_one_final N hN1
      have hpos : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
      have h4 : 0 < 2 * SmoothBenchmark.theta N N - 1 := by linarith
      have h2 : 0 < SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1) := by positivity
      have h3 : 0 ≤ (SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) := by apply div_nonneg (by linarith) (le_of_lt h2)
      exact mul_nonneg h3 (sq_nonneg _)
  | succ k ih =>
    have hk' : k ≤ N+1 := by omega
    have ih0 := ih hk'
    have h_eq : N+1 - (k+1) + 1 = N+1 - k := by omega
    by_cases h_eqN : N+1 - (k+1) = N
    · by_cases hN0 : N = 0
      · subst hN0
        have hn0 : 0+1 - (k+1) = 0 := by omega
        rw [hn0]
        have h0 : zetaStar 0 R 0 = 0 := by
          unfold zetaStar
          simp [SmoothBenchmark.theta_zero 0]
        rw [h0]
      · have hN1 : 1 ≤ N := by omega
        have hkey : zetaStar N R (N+1 - (k+1)) = SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) * zetaStar N R (N+1 - k) := by
          have hn : N+1 - (k+1) = N := h_eqN
          rw [hn]
          rw [zetaStar_N_eq N R hN1]
          have : N+1 - k = N+1 := by omega
          rw [this]
        rw [hkey]
        have h1 : 1 < SmoothBenchmark.theta N N := theta_gt_one_final N hN1
        have hpos : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
        have hpos2 : 0 < SmoothBenchmark.theta N N - 1 := by linarith
        have hcoeff : 0 ≤ SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) := by
          apply div_nonneg
          · exact le_of_lt hpos
          · exact le_of_lt hpos2
        exact mul_nonneg hcoeff ih0
    · have hlt : N+1 - (k+1) < N := by omega
      have hkey : zetaStar N R (N+1 - (k+1)) = (2 * SmoothBenchmark.theta N (N+1 - (k+1)) / (2 * SmoothBenchmark.theta N (N+1 - (k+1)) - 1)) * zetaStar N R (N+1 - k) := by
        rw [zetaStar_ltN_eq N R (N+1 - (k+1)) hlt]
        rw [h_eq]
      rw [hkey]
      have hpos2 : 0 < 2 * SmoothBenchmark.theta N (N+1 - (k+1)) - 1 := theta_two_mul_sub_one_pos N (N+1 - (k+1)) (by omega)
      have htheta_pos : 0 < SmoothBenchmark.theta N (N+1 - (k+1)) := SmoothBenchmark.theta_pos N (N+1 - (k+1)) (by omega)
      have hpos3 : 0 < 2 * SmoothBenchmark.theta N (N+1 - (k+1)) := by positivity
      have hcoeff : 0 ≤ 2 * SmoothBenchmark.theta N (N+1 - (k+1)) / (2 * SmoothBenchmark.theta N (N+1 - (k+1)) - 1) := by
        apply div_nonneg
        · exact le_of_lt hpos3
        · exact le_of_lt hpos2
      exact mul_nonneg hcoeff ih0

theorem zetaStar_nonneg (N : ℕ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) : 0 ≤ zetaStar N R n := by
  by_cases h : n ≤ N+1
  · have hk : N+1 - (N+1 - n) = n := by omega
    have hle : N+1 - n ≤ N+1 := by omega
    have h := zetaStar_nonneg_aux N R hR (N+1 - n) hle
    rw [hk] at h
    exact h
  · have h0 : zetaStar N R n = 0 := by
      have hgt : n > N+1 := by omega
      by_cases hn2 : n = N+2
      · unfold zetaStar
        simp [hn2]
      · have hneN2 : ¬ n = N+2 := hn2
        have hneN1 : ¬ n = N+1 := by omega
        have hneN : ¬ n = N := by omega
        have hlt_false : ¬ n < N := by omega
        unfold zetaStar
        simp [hneN2, hneN1, hneN, hlt_false]
    rw [h0]

theorem zetaStar_pos_aux2 (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R) (k : ℕ) (hk : k ≤ N+1) : 0 < zetaStar N R (N+1 - k) := by
  induction k with
  | zero =>
    simp
    rw [zetaStar_Nplus1_eq]
    exact zetaStar_pos_aux N hN R hR
  | succ k ih =>
    have hk' : k ≤ N+1 := by omega
    have ih0 := ih hk'
    have h_eq : N+1 - (k+1) + 1 = N+1 - k := by omega
    by_cases h_eqN : N+1 - (k+1) = N
    · have hN1 : 1 ≤ N := by omega
      have hkey : zetaStar N R (N+1 - (k+1)) = SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) * zetaStar N R (N+1 - k) := by
        have hn : N+1 - (k+1) = N := h_eqN
        rw [hn]
        rw [zetaStar_N_eq N R hN1]
        have : N+1 - k = N+1 := by omega
        rw [this]
      rw [hkey]
      exact mul_pos (coeff_pos_N N hN1) ih0
    · have hlt : N+1 - (k+1) < N := by omega
      have hkey : zetaStar N R (N+1 - (k+1)) = (2 * SmoothBenchmark.theta N (N+1 - (k+1)) / (2 * SmoothBenchmark.theta N (N+1 - (k+1)) - 1)) * zetaStar N R (N+1 - k) := by
        rw [zetaStar_ltN_eq N R (N+1 - (k+1)) hlt]
        rw [h_eq]
      rw [hkey]
      exact mul_pos (coeff_pos_ltN N (N+1 - (k+1)) hlt) ih0

theorem zetaStar_pos (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R) (n : ℕ) (hn : n ≤ N+1) : 0 < zetaStar N R n := by
  have hk : N+1 - (N+1 - n) = n := by omega
  have hle : N+1 - n ≤ N+1 := by omega
  have h := zetaStar_pos_aux2 N R hN hR (N+1 - n) hle
  rw [hk] at h
  exact h

theorem coeff_gt_one_N (N : ℕ) (hN : 1 ≤ N) : 1 < SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) := by
  have h1 : 1 < SmoothBenchmark.theta N N := theta_gt_one_final N hN
  have hpos : 0 < SmoothBenchmark.theta N N - 1 := by linarith
  have h1 : SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) = 1 + 1 / (SmoothBenchmark.theta N N - 1) := by
    have hne : SmoothBenchmark.theta N N - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h1]
  have h2 : 0 < 1 / (SmoothBenchmark.theta N N - 1) := by positivity
  linarith

theorem coeff_gt_one_ltN (N n : ℕ) (hn : n < N) : 1 < 2 * SmoothBenchmark.theta N n / (2 * SmoothBenchmark.theta N n - 1) := by
  have h1 : 1 ≤ SmoothBenchmark.theta N n := SmoothBenchmark.theta_ge_one N n (by omega)
  have h2 : 0 < 2 * SmoothBenchmark.theta N n - 1 := by linarith
  have h : 2 * SmoothBenchmark.theta N n / (2 * SmoothBenchmark.theta N n - 1) = 1 + 1 / (2 * SmoothBenchmark.theta N n - 1) := by
    have hne : (2 * SmoothBenchmark.theta N n - 1) ≠ 0 := by linarith
    field_simp
    ring
  rw [h]
  have h3 : 0 < 1 / (2 * SmoothBenchmark.theta N n - 1) := by positivity
  linarith

theorem zetaStar_strictAnti (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R) (n : ℕ) (hn : n ≤ N) : zetaStar N R (n+1) < zetaStar N R n := by
  by_cases h : n = N
  · rw [h, zetaStar_N_eq N R hN]
    have hcoeff : 1 < SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) := coeff_gt_one_N N hN
    have hpos : 0 < zetaStar N R (N+1) := zetaStar_pos N R hN hR (N+1) (by omega)
    calc zetaStar N R (N+1) = 1 * zetaStar N R (N+1) := by ring
      _ < SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) * zetaStar N R (N+1) := mul_lt_mul_of_pos_right hcoeff hpos
  · have hlt : n < N := by omega
    rw [zetaStar_ltN_eq N R n hlt]
    have hcoeff : 1 < 2 * SmoothBenchmark.theta N n / (2 * SmoothBenchmark.theta N n - 1) := coeff_gt_one_ltN N n hlt
    have hpos : 0 < zetaStar N R (n+1) := zetaStar_pos N R hN hR (n+1) (by omega)
    calc zetaStar N R (n+1) = 1 * zetaStar N R (n+1) := by ring
      _ < 2 * SmoothBenchmark.theta N n / (2 * SmoothBenchmark.theta N n - 1) * zetaStar N R (n+1) := mul_lt_mul_of_pos_right hcoeff hpos

theorem hardF_value (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) : hardF N L R N = L * R ^ 2 / (2 * SmoothBenchmark.theta N N ^ 2) := by
  have h1 : hardF N L R N = L / 2 * (zetaStar N R N + zetaStar N R (N+1)) := by
    unfold hardF
    simp
  have h2 : zetaStar N R N = SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) * zetaStar N R (N+1) := zetaStar_N_eq N R hN
  have h3 : zetaStar N R (N+1) = (SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2 := zetaStar_Nplus1_eq N R
  rw [h1, h2, h3]
  calc L / 2 * (SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) * ((SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2) + (SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2)
      = L / 2 * ((SmoothBenchmark.theta N N / (SmoothBenchmark.theta N N - 1) + 1) * ((SmoothBenchmark.theta N N - 1) / (SmoothBenchmark.theta N N ^ 2 * (2 * SmoothBenchmark.theta N N - 1)) * R ^ 2)) := by ring
    _ = L * R ^ 2 / (2 * SmoothBenchmark.theta N N ^ 2) := hardF_algebra N hN L R


end SmoothDrori
end
