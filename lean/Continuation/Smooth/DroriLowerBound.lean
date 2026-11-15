module
public import Continuation.Smooth.DroriTailCost
public import Continuation.Smooth.GramModel
@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace
namespace SmoothDrori
open DroriTail

lemma zetaStar_antitone_through_zero (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ N+2) : zetaStar N R j ≤ zetaStar N R i := by
  by_cases hj' : j ≤ N+1
  · exact zetaStar_antitone_bounded N R hN hR i j hij hj'
  · have he : j = N+2 := by omega
    rw [he,zetaStar_last]
    exact zetaStar_nonneg N R hR.le i

lemma hardDual_candidate_small_sum (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (t : Fin (N+1) → ℝ) (ht : ∀ j, 0 ≤ t j) (k : ℕ) (hk0 : 1 ≤ k) (hkN : k ≤ N)
    (hS : prefixSum t k ≤ 1) :
    hardDual N L R (hardUnscale N L R (candidate t k (1-prefixSum t k))) ≤
      hardDual N L R (hardUnscale N L R t) := by
  let z := zetaStar N R
  let a := 1-prefixSum t k
  have ha : 0 ≤ a := sub_nonneg.mpr hS
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [prefixSum_nonneg t ht k]
  have hz : ∀ j ≤ N, z (j+1) ≤ z j :=
    fun j hj => (zetaStar_strictAnti N R hN hR j hj).le
  obtain ⟨i,hi,hpiece⟩ := hardDual_unscale_eq_piece N L R hN hL hR (candidate t k a)
  change hardDual N L R (hardUnscale N L R (candidate t k a)) ≤ _
  rw [hpiece]
  have hB : base z t k ≤ B N z (candidate t k a) i := by
    rw [B_eq_base]
    exact candidate_base_bound_small_sum z t ht k hkN (fun j hj => hz j (by omega)) hS (i+1)
  by_cases hta : a ≤ t ⟨k,by omega⟩
  · have hq := candidate_cost_large_coordinate z t hz k hkN a ha hta
    have hcost : quad z (candidate t k a)/2-B N z (candidate t k a) i ≤ quad z t/2-base z t k := by
      linarith
    have hm := mul_le_mul_of_nonneg_left hcost hL.le
    have hge := hardDual_unscale_ge N L R hN hL hR (k-1) (by omega) t
    rw [B_eq_base,show k-1+1=k by omega] at hge
    nlinarith [hm]
  · have hq := candidate_cost_small_coordinate z t hz k hkN a (ht ⟨k,by omega⟩)
      (le_of_not_ge hta) ha1 (by dsimp [a]; ring)
    have hcost : quad z (candidate t k a)/2-B N z (candidate t k a) i ≤ quad z t/2-B N z t k := by
      linarith
    have hm := mul_le_mul_of_nonneg_left hcost hL.le
    have hge := hardDual_unscale_ge N L R hN hL hR k (by omega) t
    nlinarith [hm]

lemma hardDual_candidate_large_sum (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (t : Fin (N+1) → ℝ) (k : ℕ) (hk0 : 1 ≤ k) (hkN : k ≤ N)
    (hS : 1 ≤ prefixSum t k) :
    hardDual N L R (hardUnscale N L R (candidate t k 0)) ≤
      hardDual N L R (hardUnscale N L R t) := by
  let z := zetaStar N R
  have hz : ∀ j ≤ N, z (j+1) ≤ z j :=
    fun j hj => (zetaStar_strictAnti N R hN hR j hj).le
  obtain ⟨i,hi,hpiece⟩ := hardDual_unscale_eq_piece N L R hN hL hR (candidate t k 0)
  rw [hpiece]
  have hq := quad_candidate_zero_le z t hz k hkN
  by_cases hik : i+1 ≤ k
  · have hB : B N z (candidate t k 0) i = B N z t i := by
      rw [B_eq_base,B_eq_base,base_candidate_small z t k (i+1) 0 hik]
    have hge := hardDual_unscale_ge N L R hN hL hR i hi t
    have hm := mul_le_mul_of_nonneg_left hq hL.le
    change L/2*quad z (candidate t k 0)-L*B N z (candidate t k 0) i ≤ _
    rw [hB]
    nlinarith [hm]
  · have hB : base z t k ≤ B N z (candidate t k 0) i := by
      rw [B_eq_base]
      exact candidate_base_bound_large_sum z t k (i+1) hkN (by omega)
        (zetaStar_antitone_through_zero N R hN hR k (i+1) (by omega) (by omega)) hS
    have hcost : quad z (candidate t k 0)/2-B N z (candidate t k 0) i ≤ quad z t/2-base z t k := by
      linarith
    have hm := mul_le_mul_of_nonneg_left hcost hL.le
    have hge := hardDual_unscale_ge N L R hN hL hR (k-1) (by omega) t
    rw [B_eq_base,show k-1+1=k by omega] at hge
    nlinarith [hm]

/-- The actual everywhere-defined hard gradient reveals at most one coordinate
    at every prefix-supported query. This is a property of the constructed
    orthant conjugate, not a consequence postulated from interpolation. -/
theorem hardGradient_zero_chain (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (k : ℕ) (hk : k < N) (p : Space N) (hp : p ∈ prefixSpace N k) :
    hardGradient N L R hN hL hR p ∈ prefixSpace N (k+1) := by
  by_cases hk0 : k = 0
  · subst k
    exact hardGradient_prefix_zero N L R hN hL hR p hp
  let q := hardGradient N L R hN hL hR p
  let t := hardScale N L R q
  have ht : ∀ j, 0 ≤ t j := hardScale_nonneg N L R hL q
    ((hardGradient_spec N L R hN hL hR).1 p)
  have hqt : hardUnscale N L R t = q := hardUnscale_hardScale N L R hN hL hR q
  by_cases hS : prefixSum t k ≤ 1
  · have ha : 0 ≤ 1-prefixSum t k := sub_nonneg.mpr hS
    have hcost := hardDual_candidate_small_sum N L R hN hL hR t ht k (by omega) hk.le hS
    rw [hqt] at hcost
    have he := hardGradient_eq_tail_candidate N L R hN hL hR p k hp (1-prefixSum t k) ha hcost
    rw [he]
    exact hardUnscale_candidate_mem_prefix N L R t k (1-prefixSum t k)
  · have hcost := hardDual_candidate_large_sum N L R hN hL hR t k (by omega) hk.le (le_of_not_ge hS)
    rw [hqt] at hcost
    have he := hardGradient_eq_tail_candidate N L R hN hL hR p k hp 0 le_rfl hcost
    rw [he]
    exact hardUnscale_candidate_mem_prefix N L R t k 0

/-- Every predetermined linear-history first-order method incurs the sharp
    smooth-convex lower bound on the same explicit Drori hard instance. -/
theorem hardInstance_all_linear_history_lower (N : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    L*R^2/(2*(SmoothBenchmark.theta N N)^2) ≤
      SmoothGramModel.terminalLoss (hardInstance N L R hN hL hR) W := by
  have hp := OracleTrajectory.zero_chain W (hardGradient N L R hN hL hR)
    (prefixSpace N) (prefixSpace_mono N)
    (hardGradient_zero_chain N L R hN hL hR) (Fin.last N)
  exact hardFunction_terminal_lower N L R hN hL hR _ hp

/-- The lower bound is witnessed by an actual smooth oracle in the operational
    loss set, for every history matrix W. -/
theorem actualLossSet_has_sharp_lower_witness (N : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    ∃ loss ∈ SmoothGramModel.actualLossSet N W L R,
      L*R^2/(2*(SmoothBenchmark.theta N N)^2) ≤ loss := by
  refine ⟨SmoothGramModel.terminalLoss (hardInstance N L R hN hL hR) W,?_,
    hardInstance_all_linear_history_lower N L R hN hL hR W⟩
  exact ⟨N,hardInstance N L R hN hL hR,rfl⟩

end SmoothDrori
