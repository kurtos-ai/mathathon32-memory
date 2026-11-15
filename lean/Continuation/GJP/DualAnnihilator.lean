module
public import Continuation.GJP.DualPairing
public import Continuation.GJP.PositiveKernel
@[expose] public section
noncomputable section
namespace GJPDual

/-- No nonzero positive functional annihilates the canonical conic map. -/
theorem positive_annihilator_zero {N : ℕ} (W : Matrix (Q N) (Q N) ℝ)
    (hW : GJP.UnitLower W) (F : E N →L[ℝ] ℝ)
    (hF : ∀ e ∈ cone N, 0 ≤ F e) (hFA : F.comp (conicMap W) = 0) : F = 0 := by
  have hz (y : Y N) : F (conicMap W y) = 0 := by
    change (F.comp (conicMap W)) y = 0
    rw [hFA]
    rfl
  have hzero : gram F (Sum.inl ()) (Sum.inl ()) = 0 := by
    have h := hz (1,0)
    rw [functional_radius] at h
    linarith
  have hdiag (i : Q N) : 0 ≤ gram F (Sum.inl ()) (Sum.inr i) -
      ∑ j, W i j * gram F (Sum.inr j) (Sum.inr i) := by
    have h := hz (0,Matrix.single i i 1)
    rw [functional_single_diag] at h
    have hr := rowWeight_nonneg F hF i
    have hc := colWeight_nonneg F hF i
    linarith
  have hG : gram F = 0 := triangular_positive_kernel W hW (gram F) (gram_psd F hF) hzero hdiag
  have hr (i : Q N) : rowWeight F i = 0 := by
    have h := hz (0,Matrix.single i i 1)
    rw [functional_single_diag] at h
    simp only [hG,Matrix.zero_apply,mul_zero,Finset.sum_const_zero,neg_zero,zero_add] at h
    have hp := rowWeight_nonneg F hF i
    have hc := colWeight_nonneg F hF i
    linarith
  have hc (i : Q N) : colWeight F i = 0 := by
    have h := hz (0,Matrix.single i i 1)
    rw [functional_single_diag] at h
    simpa [hG,hr] using h
  have ho (ij : Off N) : offWeight F ij = 0 := by
    have h := hz (0,Matrix.single ij.val.1 ij.val.2 1)
    rw [functional_single_offdiag F W ij.val.1 ij.val.2 ij.property] at h
    simpa [hG,hr,hc] using h
  apply ContinuousLinearMap.ext
  intro e
  change F e = 0
  rw [functional_eq]
  simp [hG,hr,hc,ho]

end GJPDual
