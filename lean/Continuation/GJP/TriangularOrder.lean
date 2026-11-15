module
public import Continuation.GJP.Completion
public import Mathlib.Order.WellFounded

@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- The elementary comparison principle for triangular matrices with nonpositive off-diagonal
entries and positive pivots. -/
theorem lower_comparison {A : Matrix n n ℝ} (hA : A.IsLowerTriangular)
    (hd : ∀ i, 0 < A i i) (hs : ∀ i j, j < i → A i j ≤ 0)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ (A *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hsum : (∑ j ∈ Finset.univ.erase i, A i j * x j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rcases lt_or_gt_of_ne hji with h | h
      · exact mul_nonpos_of_nonpos_of_nonneg (hs i j h) (ih j h)
      · rw [hA h, zero_mul]
    have hi := hx i
    change 0 ≤ ∑ j, A i j * x j at hi
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hi
    have hp := hd i
    nlinarith

/-- The reverse-order version used for the upper factor `T`. -/
theorem upper_comparison {A : Matrix n n ℝ} (hA : A.IsUpperTriangular)
    (hd : ∀ i, 0 < A i i) (hs : ∀ i j, i < j → A i j ≤ 0)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ (A *ᵥ x) i) : ∀ i, 0 ≤ x i :=
  @lower_comparison nᵒᵈ _ _ _ A hA hd hs x hx

lemma upper_zero_column_of_colsum {T : Matrix n n ℝ} (hT : T.IsUpperTriangular)
    (hs : ∀ i j, i < j → T i j ≤ 0) (hp : ∀ i, 0 ≤ ∑ j, T j i)
    (i : n) (hi : T i i = 0) : ∀ j, T j i = 0 := by
  apply upper_zero_column hT hs i hi
  apply le_antisymm _ (hp i)
  apply Finset.sum_nonpos
  intro j _
  rcases lt_trichotomy j i with h | h | h
  · exact hs j i h
  · subst j; exact hi.le
  · rw [hT h]

/-- A singular upper triangular supersolution yields a bounded nonnegative exact solution.
Zero pivots are removed by a diagonal regularization whose contribution is proved to vanish. -/
theorem upper_exists_solution_bounded (T : Matrix n n ℝ)
    (hT : T.IsUpperTriangular) (hd : ∀ i, 0 ≤ T i i)
    (hs : ∀ i j, i < j → T i j ≤ 0) (hp : ∀ i, 0 ≤ ∑ j, T j i)
    (v y : n → ℝ) (hv : ∀ i, 0 ≤ v i) (hy : ∀ i, y i ≤ 1)
    (hTy : ∀ i, v i ≤ (T *ᵥ y) i) :
    ∃ b : n → ℝ, T *ᵥ b = v ∧ (∀ i, 0 ≤ b i) ∧ (∀ i, b i ≤ 1) ∧
      (∀ i, T i i ≠ 0 → b i ≤ y i) ∧ (∀ i, T i i = 0 → b i = 0) := by
  let z : n → ℝ := fun i => if T i i = 0 then 1 else 0
  let B := T + Matrix.diagonal z
  let ybar : n → ℝ := fun i => if T i i = 0 then 0 else y i
  have hB : B.IsUpperTriangular := hT.add (Matrix.blockTriangular_diagonal z)
  have hBd : ∀ i, 0 < B i i := by
    intro i
    by_cases hi : T i i = 0
    · simp [B, z, hi]
    · simpa [B, z, hi] using lt_of_le_of_ne (hd i) (Ne.symm hi)
  have hBs : ∀ i j, i < j → B i j ≤ 0 := by
    intro i j hij
    simpa [B, Matrix.diagonal_apply, ne_of_lt hij] using hs i j hij
  have hBunit : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (hB.det_ne_zero_iff.mpr (fun i => ne_of_gt (hBd i)))
  letI : Invertible B := hBunit.invertible
  have hTzero := upper_zero_column_of_colsum hT hs hp
  have hBybar : B *ᵥ ybar = T *ᵥ y := by
    rw [Matrix.add_mulVec]
    have hTbar : T *ᵥ ybar = T *ᵥ y := by
      funext i
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : T j j = 0
      · simp [ybar, hj, hTzero j hj i]
      · simp [ybar, hj]
    have hZbar : Matrix.diagonal z *ᵥ ybar = 0 := by
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : T i i = 0 <;> simp [z, ybar, hi]
    rw [hTbar, hZbar, add_zero]
  have hybar : ∀ i, 0 ≤ ybar i := by
    apply upper_comparison hB hBd hBs
    intro i
    rw [hBybar]
    exact (hv i).trans (hTy i)
  let b : n → ℝ := B⁻¹ *ᵥ v
  have hBb : B *ᵥ b = v := by simp [b, Matrix.mulVec_mulVec]
  have hb : ∀ i, 0 ≤ b i := by
    apply upper_comparison hB hBd hBs
    intro i; rw [hBb]; exact hv i
  have hdiff : ∀ i, 0 ≤ (ybar - b) i := by
    apply upper_comparison hB hBd hBs
    intro i
    rw [Matrix.mulVec_sub, hBybar, hBb]
    exact sub_nonneg.mpr (hTy i)
  have hble : ∀ i, b i ≤ ybar i := fun i => sub_nonneg.mp (hdiff i)
  have hbzero : ∀ i, T i i = 0 → b i = 0 := by
    intro i hi
    exact le_antisymm (by simpa [ybar, hi] using hble i) (hb i)
  have hZb : Matrix.diagonal z *ᵥ b = 0 := by
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases hi : T i i = 0 <;> simp [z, hi, hbzero i]
  refine ⟨b, ?_, hb, ?_, ?_, hbzero⟩
  · simpa only [B, Matrix.add_mulVec, hZb, add_zero] using hBb
  · intro i
    apply (hble i).trans
    by_cases hi : T i i = 0
    · simp [ybar, hi]
    · simpa [ybar, hi] using hy i
  · intro i hi
    simpa [ybar, hi] using hble i

end GJP
