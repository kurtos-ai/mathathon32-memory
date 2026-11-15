module
public import Continuation.GJP.FactorizationAdmissible
@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

lemma TCFactor.isUnit_upper {A T C : Matrix n n ℝ} (h : TCFactor A T C) (hA : IsUnit A) : IsUnit T := by
  have hd := hA
  rw [Matrix.isUnit_iff_isUnit_det] at hd
  rw [h.factor,Matrix.det_mul,h.unitLower.det_eq_one,mul_one] at hd
  rw [Matrix.isUnit_iff_isUnit_det]
  exact hd

lemma TCFactor.diag_pos {A T C : Matrix n n ℝ} (h : TCFactor A T C) (hA : IsUnit A) :
    ∀ i, 0 < T i i := by
  have ht := h.isUnit_upper hA
  rw [Matrix.isUnit_iff_isUnit_det] at ht
  have hdet : T.det ≠ 0 := isUnit_iff_ne_zero.mp ht
  intro i
  exact lt_of_le_of_ne (h.diagNonneg i) (Ne.symm (h.upper.det_ne_zero_iff.mp hdet i))

lemma TCFactor.upper_inverse_nonneg {A T C : Matrix n n ℝ} (h : TCFactor A T C) (hA : IsUnit A) :
    ∀ i j, 0 ≤ T⁻¹ i j := by
  letI : Invertible T := (h.isUnit_upper hA).invertible
  intro i j
  let x : n → ℝ := T⁻¹ *ᵥ Pi.single j 1
  have hx : T *ᵥ x = Pi.single j 1 := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hp := upper_comparison h.upper (h.diag_pos hA) h.upperNonpos x
    (fun k => by rw [hx]; simp [Pi.single_apply]; split <;> norm_num) i
  simpa [x,Matrix.mulVec,dotProduct,Pi.single_apply] using hp

/-- Nonsingular TC factors are unique, including all the sign-constrained
    factors produced on the boundary-free domain of Proposition 2.3. -/
theorem TCFactor.unique {A T₁ C₁ T₂ C₂ : Matrix n n ℝ}
    (h₁ : TCFactor A T₁ C₁) (h₂ : TCFactor A T₂ C₂) (hA : IsUnit A) :
    T₁ = T₂ ∧ C₁ = C₂ := by
  letI : Invertible T₁ := (h₁.isUnit_upper hA).invertible
  letI : Invertible C₂ := h₂.unitLower.isUnit.invertible
  have he : T₁⁻¹*T₂ = C₁*C₂⁻¹ := by
    have he' : T₁*C₁ = T₂*C₂ := h₁.factor.symm.trans h₂.factor
    have h := congrArg (fun M : Matrix n n ℝ => T₁⁻¹*M*C₂⁻¹) he'
    simpa [Matrix.mul_assoc] using h.symm
  have hu : (T₁⁻¹*T₂).IsUpperTriangular :=
    (Matrix.blockTriangular_inv_of_blockTriangular h₁.upper).mul h₂.upper
  have hl := h₁.unitLower.mul h₂.unitLower.inv
  have hI : C₁*C₂⁻¹ = 1 := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [hl.1 hij]
      simp [Matrix.one_apply,ne_of_lt hij]
    · subst j
      simp [hl.2 i]
    · rw [← he,hu hij]
      simp [Matrix.one_apply,ne_of_gt hij]
  have hC : C₁ = C₂ := by
    have hc := congrArg (fun M : Matrix n n ℝ => M*C₂) hI
    simpa [Matrix.mul_assoc] using hc
  have hT : T₁ = T₂ := by
    have he' : T₁*C₂ = T₂*C₂ := by rw [← hC]; exact h₁.factor.symm.trans (h₂.factor.trans (by rw [hC]))
    have ht := congrArg (fun M : Matrix n n ℝ => M*C₂⁻¹) he'
    simpa [Matrix.mul_assoc] using ht
  exact ⟨hT,hC⟩

end GJP
