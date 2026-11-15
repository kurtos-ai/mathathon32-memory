module
public import Mathlib
@[expose] public section
noncomputable section

namespace DroriTail

def prefixSum {N : ℕ} (t : Fin (N+1) → ℝ) (k : ℕ) : ℝ :=
  ∑ j, if j.val < k then t j else 0

def base {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) : ℝ :=
  z k + ∑ j, if j.val < k then (z j.val-z k)*t j else 0

def B (N : ℕ) (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (i : ℕ) : ℝ :=
  z (i+1) + ∑ j, if j.val ≤ i then (z j.val-z (i+1))*t j else 0

theorem B_eq_base {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (i : ℕ) :
    B N z t i = base z t (i+1) := by
  simp only [B,base,Nat.lt_succ_iff]

theorem prefixSum_nonneg {N : ℕ} (t : Fin (N+1) → ℝ) (ht : ∀ j, 0 ≤ t j) (k : ℕ) :
    0 ≤ prefixSum t k := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact ht j
  · exact le_rfl

theorem prefixSum_mono {N : ℕ} (t : Fin (N+1) → ℝ) (ht : ∀ j, 0 ≤ t j) :
    Monotone (prefixSum t) := by
  intro i k hik
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hi hk hk
  · exact le_rfl
  · omega
  · exact ht j
  · exact le_rfl

theorem base_step {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) :
    base z t (k+1)-base z t k = (z k-z (k+1))*(prefixSum t (k+1)-1) := by
  have hs :
      (∑ j : Fin (N+1), if j.val < k+1 then (z j.val-z (k+1))*t j else 0) -
      (∑ j : Fin (N+1), if j.val < k then (z j.val-z k)*t j else 0) =
      (z k-z (k+1))*prefixSum t (k+1) := by
    rw [← Finset.sum_sub_distrib]
    simp only [prefixSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < k
    · simp only [hj,show j.val<k+1 by omega,ite_true]; ring
    · by_cases he : j.val = k
      · simp only [he,Nat.lt_succ_self,lt_self_iff_false,ite_true,ite_false]; ring
      · simp only [hj,show ¬j.val<k+1 by omega,ite_false,mul_zero,sub_self]
  dsimp [base]
  linarith

theorem scalar_tail_bound (t a : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    -t^2/2 + min 0 (t-a) ≤ -a^2/2 := by
  by_cases h : t ≤ a
  · rw [min_eq_right (sub_nonpos.mpr h)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 2-t-a by linarith)]
  · rw [min_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (add_nonneg ht ha)]

def candidate {N : ℕ} (t : Fin (N+1) → ℝ) (k : ℕ) (a : ℝ) : Fin (N+1) → ℝ :=
  fun j => if j.val < k then t j else if j.val = k then a else 0

theorem candidate_nonneg {N : ℕ} (t : Fin (N+1) → ℝ) (ht : ∀ j, 0 ≤ t j)
    (k : ℕ) (a : ℝ) (ha : 0 ≤ a) : ∀ j, 0 ≤ candidate t k a j := by
  intro j
  simp only [candidate]
  split_ifs
  · exact ht j
  · exact ha
  · exact le_rfl

theorem base_le_of_prefixSum_le_one {N : ℕ} (z : ℕ → ℝ)
    (t : Fin (N+1) → ℝ) (ht : ∀ j, 0 ≤ t j) (k : ℕ) :
    (∀ j, j < k → z (j+1) ≤ z j) → prefixSum t k ≤ 1 →
    ∀ i, i ≤ k → base z t k ≤ base z t i := by
  induction k with
  | zero =>
    intro _ _ i hi
    have he : i = 0 := by omega
    subst i; exact le_rfl
  | succ k ih =>
    intro hz hS i hi
    by_cases he : i = k+1
    · subst i; exact le_rfl
    have hstep : base z t (k+1) ≤ base z t k := by
      have h := base_step z t k
      have hm := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr (hz k (by omega))) (sub_nonpos.mpr hS)
      linarith
    exact hstep.trans (ih (fun j hj => hz j (by omega))
      ((prefixSum_mono t ht (by omega : k ≤ k+1)).trans hS) i (by omega))

theorem base_candidate_small {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ)
    (k l : ℕ) (a : ℝ) (hl : l ≤ k) :
    base z (candidate t k a) l = base z t l := by
  dsimp only [base]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < l
  · simp [hj,candidate,show j.val<k by omega]
  · simp [hj]

theorem base_candidate_large {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ)
    (k l : ℕ) (a : ℝ) (hk : k ≤ N) (hl : k < l) :
    base z (candidate t k a) l =
      base z t k + (z k-z l)*(prefixSum t k+a-1) := by
  let j₀ : Fin (N+1) := ⟨k,by omega⟩
  have hs :
      (∑ j : Fin (N+1), if j.val < l then (z j.val-z l)*candidate t k a j else 0) =
      (∑ j : Fin (N+1), if j.val < k then (z j.val-z l)*t j else 0) + (z k-z l)*a := by
    calc
      _ = ∑ j : Fin (N+1), ((if j.val < k then (z j.val-z l)*t j else 0) +
          (if j.val = k then (z k-z l)*a else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val < k
        · simp [candidate,hj,show j.val<l by omega,show j.val≠k by omega]
        · by_cases he : j.val = k
          · simp [candidate,hj,he,hl]
          · simp [candidate,hj,he]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single j₀]
        · simp [j₀]
        · intro j _ hj
          have he : j.val ≠ k := by intro h; apply hj; apply Fin.ext; exact h
          simp [he]
        · simp
  have hp :
      (∑ j : Fin (N+1), if j.val < k then (z j.val-z l)*t j else 0) =
      (∑ j : Fin (N+1), if j.val < k then (z j.val-z k)*t j else 0) +
        (z k-z l)*prefixSum t k := by
    simp only [prefixSum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < k <;> simp only [hj,ite_true,ite_false,mul_zero] <;> ring
  dsimp only [base]
  rw [hs,hp]
  ring

theorem candidate_base_bound_small_sum {N : ℕ} (z : ℕ → ℝ)
    (t : Fin (N+1) → ℝ) (ht : ∀ j, 0 ≤ t j) (k : ℕ) (hk : k ≤ N)
    (hz : ∀ j, j < k → z (j+1) ≤ z j) (hS : prefixSum t k ≤ 1) (l : ℕ) :
    base z t k ≤ base z (candidate t k (1-prefixSum t k)) l := by
  by_cases hl : l ≤ k
  · rw [base_candidate_small z t k l _ hl]
    exact base_le_of_prefixSum_le_one z t ht k hz hS l hl
  · rw [base_candidate_large z t k l _ hk (by omega)]
    ring_nf
    exact le_rfl

theorem candidate_base_bound_large_sum {N : ℕ} (z : ℕ → ℝ)
    (t : Fin (N+1) → ℝ) (k l : ℕ) (hk : k ≤ N) (hl : k < l)
    (hz : z l ≤ z k) (hS : 1 ≤ prefixSum t k) :
    base z t k ≤ base z (candidate t k 0) l := by
  rw [base_candidate_large z t k l 0 hk hl]
  have h := mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hS)
  linarith

end DroriTail
