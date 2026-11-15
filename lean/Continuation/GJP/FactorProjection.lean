module
public import Continuation.GJP.TriangularOrder
public import Continuation.GJP.Simplex

@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- Precisely the triangular, sign, row, and column constraints on `T,C` in (15). -/
structure TCAdmissible (last : n) (T C : Matrix n n ℝ) : Prop where
  upper : T.IsUpperTriangular
  diagNonneg : ∀ i, 0 ≤ T i i
  upperNonpos : ∀ i j, i < j → T i j ≤ 0
  unitLower : UnitLower C
  lowerNonpos : ∀ i j, j < i → C i j ≤ 0
  productOffdiag : ∀ i j, i ≠ j → (T*C) i j ≤ 0
  rowBound : ∀ i, (Pi.single last (1 : ℝ) : n → ℝ) i ≤ ((T*C) *ᵥ (fun _ => 1)) i
  columnBound : ∀ i, 0 ≤ ((T*C)ᵀ *ᵥ (fun _ => 1)) i

lemma UnitLower.row_sum_le_one {C : Matrix n n ℝ} (hC : UnitLower C)
    (hs : ∀ i j, j < i → C i j ≤ 0) (i : n) :
    (C *ᵥ (fun _ => (1 : ℝ))) i ≤ 1 := by
  have hsum : (∑ j ∈ Finset.univ.erase i, C i j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    rcases lt_or_gt_of_ne (Finset.mem_erase.mp hj).1 with h | h
    · exact hs i j h
    · rw [hC.1 h]
  change (∑ j, C i j * 1) ≤ 1
  simp only [mul_one]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hC.2 i]
  linarith

lemma TCAdmissible.colsum_nonneg {last : n} {T C : Matrix n n ℝ}
    (h : TCAdmissible last T C) (i : n) : 0 ≤ ∑ j, T j i := by
  have hp : ∀ i, 0 ≤ (Tᵀ *ᵥ (fun _ => (1 : ℝ))) i := by
    apply upper_comparison h.unitLower.1.transpose
      (fun i => by change 0 < C i i; rw [h.unitLower.2 i]; norm_num)
      (fun i j hij => h.lowerNonpos j i hij)
    intro j
    change 0 ≤ (Cᵀ *ᵥ (Tᵀ *ᵥ (fun _ => (1 : ℝ)))) j
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
    exact h.columnBound j
  simpa only [← colSum_eq] using hp i

/-- The bounded vector (18) exists for the actual constraints in (15), including singular factors. -/
theorem TCAdmissible.exists_b {last : n} {T C : Matrix n n ℝ}
    (h : TCAdmissible last T C) :
    ∃ b : n → ℝ, T *ᵥ b = Pi.single last 1 ∧ (∀ i, 0 ≤ b i) ∧ (∀ i, b i ≤ 1) ∧
      (∀ i, T i i ≠ 0 → b i ≤ (C *ᵥ (fun _ => 1)) i) ∧
      (∀ i, T i i = 0 → b i = 0) := by
  apply upper_exists_solution_bounded T h.upper h.diagNonneg h.upperNonpos h.colsum_nonneg
    (Pi.single last 1) (C *ᵥ (fun _ => 1))
  · intro i; simp [Pi.single_apply]; split <;> norm_num
  · exact h.unitLower.row_sum_le_one h.lowerNonpos
  · intro i
    simpa only [Matrix.mulVec_mulVec] using h.rowBound i

/-- Prefix flow mass for an upper triangular system. -/
theorem upper_prefix_bound (last : n) (T : Matrix n n ℝ) (b : n → ℝ)
    (hT : T.IsUpperTriangular) (hs : ∀ i j, i < j → T i j ≤ 0)
    (hb : ∀ i, 0 ≤ b i) (hTb : T *ᵥ b = Pi.single last 1)
    (i : n) (hi : i < last) :
    T i i * b i ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), (∑ k, T k j) * b j := by
  let s := Finset.univ.filter (fun j : n => j ≤ i)
  have hprefix (k : n) : 0 ≤ ∑ j ∈ s, T k j * b j := by
    by_cases hk : k ≤ i
    · have hkLast : k ≠ last := ne_of_lt (lt_of_le_of_lt hk hi)
      have hrow := congrFun hTb k
      have hrow0 : ∑ j, T k j * b j = 0 := by simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hkLast] using hrow
      have hrest : (∑ j ∈ Finset.univ.filter (fun j => ¬ j ≤ i), T k j * b j) ≤ 0 := by
        apply Finset.sum_nonpos
        intro j hj
        have hij : i < j := lt_of_not_ge (Finset.mem_filter.mp hj).2
        exact mul_nonpos_of_nonpos_of_nonneg (hs k j (lt_of_le_of_lt hk hij)) (hb j)
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : n => j ≤ i)
        (fun j => T k j * b j)
      dsimp [s]
      linarith
    · apply le_of_eq
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≤ i := (Finset.mem_filter.mp hj).2
      rw [hT (lt_of_le_of_lt hji (lt_of_not_ge hk)), zero_mul]
  have hrowi : (∑ j ∈ s, T i j * b j) = T i i * b i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hle : j ≤ i := (Finset.mem_filter.mp hj).2
      rw [hT (lt_of_le_of_ne hle hji), zero_mul]
    · intro hni
      exact False.elim (hni (by simp [s]))
  have hmass : (∑ j ∈ s, (∑ k, T k j) * b j) = ∑ k, ∑ j ∈ s, T k j * b j := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  rw [show Finset.univ.filter (fun j : n => j ≤ i) = s from rfl, hmass, ← hrowi]
  exact Finset.single_le_sum (fun k _ => hprefix k) (Finset.mem_univ i)

/-- The terminal row of an upper triangular system at its largest index. -/
lemma upper_terminal_row (last : n) (hlast : ∀ j, j ≤ last) (T : Matrix n n ℝ)
    (hT : T.IsUpperTriangular) (b : n → ℝ) (hTb : T *ᵥ b = Pi.single last 1) :
    T last last * b last = 1 := by
  have heq : (T *ᵥ b) last = T last last * b last := by
    apply Finset.sum_eq_single last
    · intro j _ hj
      change T last j * b j = 0
      rw [hT (lt_of_le_of_ne (hlast j) hj), zero_mul]
    · simp
  rw [← heq, hTb]
  simp

end GJP
