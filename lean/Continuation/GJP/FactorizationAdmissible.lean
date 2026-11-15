module
public import Continuation.GJP.Factorization
@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

lemma UnitLower.inverse_nonneg {C : Matrix n n ℝ} (hC : UnitLower C)
    (hs : ∀ i j, j < i → C i j ≤ 0) : ∀ i j, 0 ≤ C⁻¹ i j := by
  letI : Invertible C := hC.isUnit.invertible
  intro i j
  let x : n → ℝ := C⁻¹ *ᵥ Pi.single j 1
  have hx : C *ᵥ x = Pi.single j 1 := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hp := lower_comparison hC.1 (fun i => by rw [hC.2 i]; norm_num) hs x
    (fun k => by rw [hx]; simp [Pi.single_apply]; split <;> norm_num) i
  simpa [x,Matrix.mulVec,dotProduct,Pi.single_apply] using hp

lemma TCFactor.colsum_nonneg {A T C : Matrix n n ℝ} (h : TCFactor A T C) (hA : DDMZ A) :
    ∀ i, 0 ≤ ∑ j, T j i := by
  have hp : ∀ i, 0 ≤ (Tᵀ *ᵥ (fun _ => (1 : ℝ))) i := by
    apply upper_comparison h.unitLower.1.transpose
      (fun i => by change 0 < C i i; rw [h.unitLower.2 i]; norm_num)
      (fun i j hij => h.lowerNonpos j i hij)
    intro j
    change 0 ≤ (Cᵀ *ᵥ (Tᵀ *ᵥ (fun _ => (1 : ℝ)))) j
    rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,← h.factor]
    rw [← colSum_eq]
    exact hA.cols j
  simpa only [← colSum_eq] using hp

/-- Full existence and inverse/column positivity in Proposition 2.3, with no
    nonsingularity assumption. -/
theorem exists_TC_factor_nonnegative (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : DDMZ A) :
    ∃ T C, TCFactor A T C ∧ (∀ i j, 0 ≤ C⁻¹ i j) ∧ (∀ i, 0 ≤ ∑ j, T j i) := by
  obtain ⟨T,C,h⟩ := exists_TC_factor n A hA
  exact ⟨T,C,h,h.unitLower.inverse_nonneg h.lowerNonpos,h.colsum_nonneg hA⟩

/-- Every actual compact dual matrix in (9) factors into precisely the
    admissible TC domain used by the elimination and uniqueness proofs. -/
theorem exists_TC_admissible (N : ℕ) (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hrow : ∀ i, (Pi.single (Fin.last N) (1 : ℝ) : Fin (N+1) → ℝ) i ≤ (A *ᵥ (fun _ => 1)) i)
    (hcol : ∀ i, 0 ≤ (Aᵀ *ᵥ (fun _ => 1)) i) :
    ∃ T C, A = T*C ∧ TCAdmissible (Fin.last N) T C := by
  have hA : DDMZ A := by
    refine ⟨hoff,?_,?_⟩
    · intro i
      have hz : 0 ≤ (Pi.single (Fin.last N) (1 : ℝ) : Fin (N+1) → ℝ) i := by
        simp [Pi.single_apply]; split <;> norm_num
      simpa [Matrix.mulVec,dotProduct] using hz.trans (hrow i)
    · intro i
      simpa [Matrix.mulVec,dotProduct] using hcol i
  obtain ⟨T,C,h⟩ := exists_TC_factor (N+1) A hA
  refine ⟨T,C,h.factor,h.upper,h.diagNonneg,h.upperNonpos,h.unitLower,h.lowerNonpos,?_,?_,?_⟩
  · simpa only [← h.factor] using hoff
  · simpa only [← h.factor] using hrow
  · simpa only [← h.factor] using hcol

end GJP
