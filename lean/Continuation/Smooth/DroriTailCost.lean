module
public import Continuation.Smooth.DroriTailGeometry
@[expose] public section
noncomputable section
namespace DroriTail

lemma prefixSum_succ {N : ℕ} (t : Fin (N+1) → ℝ) (k : ℕ) (hk : k ≤ N) :
    prefixSum t (k+1) = prefixSum t k+t ⟨k,by omega⟩ := by
  classical
  have hs : (∑ j : Fin (N+1), if j.val = k then t j else 0) = t ⟨k,by omega⟩ := by
    rw [Finset.sum_eq_single (⟨k,by omega⟩ : Fin (N+1))]
    · simp
    · intro b _ hb
      have hbk : b.val ≠ k := by intro he; apply hb; exact Fin.ext he
      simp [hbk]
    · simp
  rw [← hs]
  simp only [prefixSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · simp [hj,show j.val<k+1 by omega,show j.val≠k by omega]
  · by_cases he : j.val = k
    · simp [he]
    · simp [hj,he,show ¬j.val<k+1 by omega]

lemma B_at_next {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) (hk : k ≤ N) :
    B N z t k = base z t k+(z k-z (k+1))*(prefixSum t k+t ⟨k,by omega⟩-1) := by
  have hs := base_step z t k
  rw [prefixSum_succ t k hk] at hs
  rw [B_eq_base]
  linarith

/-- Completing the first unexposed coordinate cannot increase the scalar dual
    quadratic minus its baseline, when the original coordinate is already larger. -/
lemma candidate_cost_large_coordinate {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ)
    (hz : ∀ j ≤ N, z (j+1) ≤ z j) (k : ℕ) (hk : k ≤ N) (a : ℝ)
    (ha : 0 ≤ a) (ht : a ≤ t ⟨k,by omega⟩) :
    quad z (candidate t k a)/2 ≤ quad z t/2 := by
  rw [quad_candidate z t k hk,quad_split z t k hk]
  have hsq : a^2 ≤ (t ⟨k,by omega⟩)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr (hz k hk))
  have htail := tailQuad_nonneg z t hz k
  linarith

/-- If the original coordinate is too small, its adjacent B-piece compensates
    for the increase in the squared coordinate exactly. -/
lemma candidate_cost_small_coordinate {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ)
    (hz : ∀ j ≤ N, z (j+1) ≤ z j) (k : ℕ) (hk : k ≤ N) (a : ℝ)
    (ht0 : 0 ≤ t ⟨k,by omega⟩) (hta : t ⟨k,by omega⟩ ≤ a) (ha1 : a ≤ 1)
    (hS : prefixSum t k+a=1) :
    quad z (candidate t k a)/2-base z t k ≤ quad z t/2-B N z t k := by
  rw [quad_candidate z t k hk,quad_split z t k hk,B_at_next z t k hk]
  have hscalar := scalar_tail_bound (t ⟨k,by omega⟩) a ht0 (ht0.trans hta) ha1
  rw [min_eq_right (sub_nonpos.mpr hta)] at hscalar
  have hmul := mul_le_mul_of_nonneg_left hscalar (sub_nonneg.mpr (hz k hk))
  have htail := tailQuad_nonneg z t hz k
  have he : prefixSum t k+t ⟨k,by omega⟩-1 = t ⟨k,by omega⟩-a := by linarith
  rw [he]
  nlinarith [hmul]

end DroriTail
