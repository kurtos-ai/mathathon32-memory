module
public import Continuation.GJP.DualPairing
public import Continuation.GJP.DualInterpolation
@[expose] public section
noncomputable section
open Matrix
namespace GJPDual

lemma compatible_apply {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) (hcomp : F.comp (conicMap W) = cost N) (y : Y N) :
    F (conicMap W y) = y.1 := by
  have h := congrArg (fun H : Y N →L[ℝ] ℝ => H y) hcomp
  exact h

lemma compatible_radius {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) (hcomp : F.comp (conicMap W) = cost N) :
    gram F (Sum.inl ()) (Sum.inl ()) = 2 := by
  have h := compatible_apply F W hcomp (1,0)
  rw [functional_radius] at h
  norm_num at h ⊢
  linarith

lemma compatible_diagonal {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) (hcomp : F.comp (conicMap W) = cost N) (i : Q N) :
    GJP.shiftedPairing W (gram F) i i = rowWeight F i + colWeight F i := by
  have h := compatible_apply F W hcomp (0,Matrix.single i i 1)
  rw [functional_single_diag] at h
  change -gram F (Sum.inl ()) (Sum.inr i) +
    (∑ k,W i k * gram F (Sum.inr k) (Sum.inr i)) + rowWeight F i + colWeight F i = 0 at h
  unfold GJP.shiftedPairing
  linarith

lemma compatible_pair {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) (hcomp : F.comp (conicMap W) = cost N)
    (hF : ∀ e ∈ cone N,0 ≤ F e) (i j : Q N) :
    GJP.shiftedPairing W (gram F) i j ≤ rowWeight F i + colWeight F j := by
  by_cases hij : i=j
  · subst j
    exact (compatible_diagonal F W hcomp i).le
  have h := compatible_apply F W hcomp (0,Matrix.single i j 1)
  rw [functional_single_offdiag F W i j hij] at h
  change -gram F (Sum.inl ()) (Sum.inr j) +
    (∑ k,W i k * gram F (Sum.inr k) (Sum.inr j)) - offWeight F ⟨(i,j),hij⟩ +
      rowWeight F i + colWeight F j = 0 at h
  have hp := offWeight_nonneg F hF ⟨(i,j),hij⟩
  unfold GJP.shiftedPairing
  linarith

/-- Every positive normalized conic functional is represented by an actual smooth-convex loss. -/
theorem positive_functional_actual_loss {N : ℕ}
    (W : Matrix (Q N) (Q N) ℝ) (hW : GJP.UnitLower W)
    (F : E N →L[ℝ] ℝ) (hF : ∀ e ∈ cone N,0 ≤ F e)
    (hcomp : F.comp (conicMap W) = cost N) :
    F (constant N) ∈ SmoothGramModel.actualLossSet N (GJP.additiveHistory W) 1 (Real.sqrt 2) := by
  rw [functional_constant]
  exact GJP.shifted_coordinates_actual_loss W hW (gram F) (rowWeight F) (colWeight F)
    (gram_psd F hF) (compatible_radius F W hcomp).le
    (rowWeight_nonneg F hF) (colWeight_nonneg F hF)
    (compatible_diagonal F W hcomp) (compatible_pair F W hcomp hF)

/-- An actual uniform performance bound controls all positive normalized conic functionals. -/
theorem positive_functional_bound {N : ℕ}
    (W : Matrix (Q N) (Q N) ℝ) (hW : GJP.UnitLower W) (v : ℝ)
    (hv : ∀ t ∈ SmoothGramModel.actualLossSet N (GJP.additiveHistory W) 1 (Real.sqrt 2), t ≤ v)
    (F : E N →L[ℝ] ℝ) (hF : ∀ e ∈ cone N,0 ≤ F e)
    (hcomp : F.comp (conicMap W) = cost N) : F (constant N) ≤ v :=
  hv _ (positive_functional_actual_loss W hW F hF hcomp)

end GJPDual
