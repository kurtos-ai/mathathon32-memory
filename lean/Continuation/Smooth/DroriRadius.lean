module
public import Continuation.Smooth.DroriCoordinates
public import Continuation.GJP.Simplex
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace SmoothDrori
open SmoothBenchmark

lemma zetaStar_step_mul (N : ℕ) (R : ℝ) (j : ℕ) (hj : j < N) :
    (2*theta N j-1)*zetaStar N R j = 2*theta N j*zetaStar N R (j+1) := by
  rw [zetaStar_ltN_eq N R j hj]
  have hn := ne_of_gt (theta_two_mul_sub_one_pos N j hj.le)
  field_simp

lemma zetaStar_last_mul (N : ℕ) (R : ℝ) (hN : 1 ≤ N) :
    (theta N N-1)*zetaStar N R N = theta N N*zetaStar N R (N+1) := by
  rw [zetaStar_N_eq N R hN]
  have hn : theta N N-1 ≠ 0 := ne_of_gt (sub_pos.mpr (theta_gt_one_final N hN))
  field_simp

lemma zetaStar_square_div_step (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (j : ℕ) (hj : j < N) :
    (zetaStar N R j)^2/(zetaStar N R j-zetaStar N R (j+1)) =
      2*theta N j*zetaStar N R j := by
  have hd : 0 < zetaStar N R j-zetaStar N R (j+1) :=
    sub_pos.mpr (zetaStar_strictAnti N R hN hR j hj.le)
  apply (div_eq_iff (ne_of_gt hd)).2
  have h := zetaStar_step_mul N R j hj
  nlinarith [congrArg (fun a : ℝ => a*zetaStar N R j) h]

lemma zetaStar_square_div_last (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R) :
    (zetaStar N R N)^2/(zetaStar N R N-zetaStar N R (N+1)) =
      theta N N*zetaStar N R N := by
  have hd : 0 < zetaStar N R N-zetaStar N R (N+1) :=
    sub_pos.mpr (zetaStar_strictAnti N R hN hR N le_rfl)
  apply (div_eq_iff (ne_of_gt hd)).2
  have h := zetaStar_last_mul N R hN
  nlinarith [congrArg (fun a : ℝ => a*zetaStar N R N) h]

lemma zetaStar_weighted_sum (N : ℕ) (R : ℝ) (k : ℕ) (hk0 : 1 ≤ k) (hkN : k ≤ N) :
    (∑ j ∈ Finset.range k, 2*theta N j*zetaStar N R j) =
      4*(theta N (k-1))^2*zetaStar N R k := by
  induction k, hk0 using Nat.le_induction with
  | base =>
    simp only [Finset.sum_range_one, Nat.sub_self, theta_zero]
    have hz := zetaStar_step_mul N R 0 (by omega)
    simp only [theta_zero, zero_add] at hz
    nlinarith [hz]
  | succ k hk ih =>
    have hrec := GJP.theta_sq_standard N k hk (by omega)
    have hz := zetaStar_step_mul N R k (by omega)
    rw [Finset.sum_range_succ, ih (by omega)]
    simp only [Nat.add_sub_cancel]
    nlinarith [congrArg (fun a : ℝ => a*zetaStar N R k) hrec,
      congrArg (fun a : ℝ => (2*theta N k)*a) hz]

lemma hardX_minimizer_norm_sq_sum (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R) :
    ‖hardX N R (N+1)‖^2 =
      ∑ j ∈ Finset.range (N+1), (zetaStar N R j)^2 /
        (zetaStar N R j-zetaStar N R (j+1)) := by
  rw [EuclideanSpace.real_norm_sq_eq, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [hardX_apply]
  have hj : j.val < N+1 := j.isLt
  simp only [hj, ite_true, show N+1+1=N+2 by omega, zetaStar_last, sub_zero,
    div_pow, neg_sq]
  rw [Real.sq_sqrt (sub_nonneg.mpr
    (zetaStar_strictAnti N R hN hR j.val (by omega)).le)]

/-- The hard minimizer has exactly the prescribed radius. -/
theorem hardX_minimizer_norm (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R) :
    ‖hardX N R (N+1)‖ = R := by
  have hs : ‖hardX N R (N+1)‖^2 = R^2 := by
    rw [hardX_minimizer_norm_sq_sum N R hN hR, Finset.sum_range_succ,
      zetaStar_square_div_last N R hN hR]
    have he : (∑ j ∈ Finset.range N,
        (zetaStar N R j)^2/(zetaStar N R j-zetaStar N R (j+1))) =
        ∑ j ∈ Finset.range N, 2*theta N j*zetaStar N R j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact zetaStar_square_div_step N R hN hR j (Finset.mem_range.mp hj)
    rw [he,zetaStar_weighted_sum N R N hN le_rfl]
    have ht := GJP.theta_sq_final N hN
    have hz := zetaStar_last_mul N R hN
    have hN1 := zetaStar_Nplus1_eq N R
    have h0 := ne_of_gt (theta_pos N N le_rfl)
    have h1 : theta N N-1 ≠ 0 := ne_of_gt (sub_pos.mpr (theta_gt_one_final N hN))
    have h2 : 2*theta N N-1 ≠ 0 := ne_of_gt (theta_two_mul_sub_one_pos N N le_rfl)
    calc
      _ = theta N N*(2*theta N N-1)*zetaStar N R N := by
        nlinarith [congrArg (fun a : ℝ => a*zetaStar N R N) ht]
      _ = R^2 := by
        rw [zetaStar_N_eq N R hN,hN1]
        field_simp [h0,h1,h2,mul_comm (theta N N) 2]
        <;> ring
  nlinarith [norm_nonneg (hardX N R (N+1))]

end SmoothDrori
