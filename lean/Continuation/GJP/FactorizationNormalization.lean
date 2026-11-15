module
public import Continuation.GJP.FactorizationAdmissible
@[expose] public section
noncomputable section
open Matrix
namespace GJP

lemma UnitLower.first_row {N : ℕ} {C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ}
    (hC : UnitLower C) (j : Fin (N+1)) : C 0 j = (Pi.single 0 (1 : ℝ) : Fin (N+1) → ℝ) j := by
  by_cases hj : j = 0
  · subst j; simp [hC.2]
  · have hj0 : (0 : Fin (N+1)) < j := Fin.pos_iff_ne_zero.mpr hj
    calc C 0 j = 0 := hC.1 hj0
      _ = _ := by simp [Pi.single_apply,hj]

lemma UnitLower.first_row_sum {N : ℕ} {C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ}
    (hC : UnitLower C) : (C *ᵥ (fun _ => (1 : ℝ))) 0 = 1 := by
  simp [Matrix.mulVec,dotProduct,hC.first_row,Pi.single_apply]

lemma upper_mulVec_first_support {N : ℕ} (T : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hT : T.IsUpperTriangular) (hz : ∀ i, T i i = 0 → ∀ j, T j i = 0)
    (y : Fin (N+1) → ℝ) (hy : T *ᵥ y = Pi.single 0 1) :
    ∀ i, (0 : Fin (N+1)) < i → T i i ≠ 0 → y i = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | ind i ih =>
    intro hi hdiag
    have hs : (T *ᵥ y) i = T i i*y i := by
      change (∑ j, T i j*y j) = _
      apply Finset.sum_eq_single i
      · intro j _ hji
        change T i j*y j = 0
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · rw [hT hlt,zero_mul]
        · by_cases hjdiag : T j j = 0
          · rw [hz j hjdiag i,zero_mul]
          · rw [ih j hgt (hi.trans hgt) hjdiag,mul_zero]
      · simp
    rw [hy] at hs
    have hz' : T i i*y i = 0 := by
      simpa [Pi.single_apply,ne_of_gt hi] using hs.symm
    exact (mul_eq_zero.mp hz').resolve_left hdiag

/-- At the row-normalized endpoint, every nonzero pivot after the first has
    zero row sum in C, and the first pivot is exactly one. -/
lemma TCFactor.row_normalized_pivots {N : ℕ} {A T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ}
    (h : TCFactor A T C) (hA : DDMZ A) (hrow : A *ᵥ (fun _ => 1) = Pi.single 0 1) :
    T 0 0 = 1 ∧ ∀ i, (0 : Fin (N+1)) < i → T i i ≠ 0 → (C *ᵥ (fun _ => 1)) i = 0 := by
  let y := C *ᵥ (fun _ => (1 : ℝ))
  have hTy : T *ᵥ y = Pi.single 0 1 := by
    simpa [y,Matrix.mulVec_mulVec,← h.factor] using hrow
  have hz := upper_zero_column_of_colsum h.upper h.upperNonpos (h.colsum_nonneg hA)
  have htail := upper_mulVec_first_support T h.upper hz y hTy
  refine ⟨?_,htail⟩
  have hs : (T *ᵥ y) 0 = T 0 0*y 0 := by
    change (∑ j, T 0 j*y j) = _
    apply Finset.sum_eq_single 0
    · intro j _ hj
      change T 0 j*y j = 0
      by_cases hd : T j j = 0
      · rw [hz j hd 0,zero_mul]
      · rw [htail j (Fin.pos_iff_ne_zero.mpr hj) hd,mul_zero]
    · simp
  rw [hTy] at hs
  have hy0 : y 0 = 1 := h.unitLower.first_row_sum
  simpa [hy0] using hs.symm

/-- Rows attached to zero pivots can be normalized without changing the product. -/
def normalizeZeroRows {N : ℕ} (T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i =>
  if T i i = 0 then Pi.single i 1-Pi.single 0 1 else C i

lemma TCFactor.normalize_zero_rows {N : ℕ} {A T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ}
    (h : TCFactor A T C) (hA : DDMZ A) (hrow : A *ᵥ (fun _ => 1) = Pi.single 0 1) :
    TCFactor A T (normalizeZeroRows T C) ∧
      normalizeZeroRows T C *ᵥ (fun _ => 1) = Pi.single 0 1 ∧ T 0 0 = 1 := by
  obtain ⟨h00,htail⟩ := h.row_normalized_pivots hA hrow
  have hz := upper_zero_column_of_colsum h.upper h.upperNonpos (h.colsum_nonneg hA)
  have hfact : T*normalizeZeroRows T C=T*C := by
    ext i j
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : T k k = 0
    · simp [hz k hk i]
    · simp [normalizeZeroRows,hk]
  have hunit : UnitLower (normalizeZeroRows T C) := by
    constructor
    · intro i j hij
      change i < j at hij
      by_cases hi : T i i = 0
      · have hji : j ≠ i := ne_of_gt hij
        have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
        simp [normalizeZeroRows,hi,Pi.single_apply,hji,hj0]
      · simpa [normalizeZeroRows,hi] using h.unitLower.1 hij
    · intro i
      by_cases hi : T i i = 0
      · have hi0 : i ≠ 0 := by intro he; subst i; rw [h00] at hi; norm_num at hi
        simp [normalizeZeroRows,hi,Pi.single_apply,hi0]
      · simpa [normalizeZeroRows,hi] using h.unitLower.2 i
  refine ⟨⟨h.factor.trans hfact.symm,h.upper,h.diagNonneg,h.upperNonpos,hunit,?_⟩,?_,h00⟩
  · intro i j hij
    by_cases hi : T i i = 0
    · have hji : j ≠ i := ne_of_lt hij
      simp only [normalizeZeroRows,hi,ite_true,Pi.sub_apply,Pi.single_apply,hji,ite_false,zero_sub]
      split <;> norm_num
    · simpa [normalizeZeroRows,hi] using h.lowerNonpos i j hij
  · funext i
    by_cases hi : T i i = 0
    · have hi0 : i ≠ 0 := by intro he; subst i; rw [h00] at hi; norm_num at hi
      simp [Matrix.mulVec,dotProduct,normalizeZeroRows,hi,Pi.single_apply,Finset.sum_sub_distrib,hi0]
    · by_cases hi0 : i = 0
      · subst i
        simpa using hunit.first_row_sum
      · have ht := htail i (Fin.pos_iff_ne_zero.mpr hi0) hi
        simpa [Matrix.mulVec,dotProduct,normalizeZeroRows,hi,Pi.single_apply,hi0] using ht

/-- The row normalization A1=e0 can be realized by C1=e0 and T00=1,
    even when A and T are singular. -/
theorem exists_TC_row_normalized (N : ℕ) (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hA : DDMZ A) (hrow : A *ᵥ (fun _ => 1) = Pi.single 0 1) :
    ∃ T C, TCFactor A T C ∧ C *ᵥ (fun _ => 1) = Pi.single 0 1 ∧ T 0 0 = 1 := by
  obtain ⟨T,C,h⟩ := exists_TC_factor (N+1) A hA
  exact ⟨T,normalizeZeroRows T C,h.normalize_zero_rows hA hrow⟩

/-- The column normalization propagates through every TC factorization. -/
lemma TCFactor.column_normalized {N : ℕ} {A T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ}
    (h : TCFactor A T C) (hcol : Aᵀ *ᵥ (fun _ => 1) = Pi.single 0 1) :
    Tᵀ *ᵥ (fun _ => 1) = Pi.single 0 1 ∧ T 0 0 = 1 := by
  letI : Invertible C := h.unitLower.isUnit.invertible
  have hc : C⁻¹ᵀ *ᵥ Pi.single 0 1 = (Pi.single 0 1 : Fin (N+1) → ℝ) := by
    funext i
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply,Matrix.transpose_apply] using h.unitLower.inv.first_row i
  have ht := congrArg (fun y => C⁻¹ᵀ *ᵥ y) hcol
  rw [h.factor,Matrix.transpose_mul] at ht
  simp only [Matrix.mulVec_mulVec,← Matrix.transpose_mul,Matrix.mul_inv_of_invertible,
    Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one,Matrix.mul_assoc] at ht
  rw [hc] at ht
  refine ⟨ht,?_⟩
  have hs : (Tᵀ *ᵥ (fun _ => (1 : ℝ))) 0 = T 0 0 := by
    change (∑ j, T j 0*1) = T 0 0
    simp only [mul_one]
    apply Finset.sum_eq_single 0
    · intro j _ hj
      exact h.upper (Fin.pos_iff_ne_zero.mpr hj)
    · simp
  rw [ht] at hs
  simpa using hs.symm

end GJP
