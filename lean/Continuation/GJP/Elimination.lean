module
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open Matrix
namespace GJP

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Symmetrization over the real field, as in GJP equation (15). -/
def matrixSymm (A : Matrix n n ℝ) : Matrix n n ℝ := (1 / 2 : ℝ) • (A + Aᵀ)

/-- The scalar-bordered matrix in the GJP distance-to-function dual. -/
def borderedMatrix (r : ℝ) (v : n → ℝ) (D : Matrix n n ℝ) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal (fun _ : Unit => r / 2))
    (fun _ j => -v j / 2) (fun i _ => -v i / 2) D

/-- Direct Schur elimination of the scalar radius block. -/
theorem borderedMatrix_posSemidef_iff (r : ℝ) (hr : 0 < r) (v : n → ℝ)
    (D : Matrix n n ℝ) :
    (borderedMatrix r v D).PosSemidef ↔
      (D - (1 / (2 * r)) • Matrix.vecMulVec v v).PosSemidef := by
  let A : Matrix Unit Unit ℝ := Matrix.diagonal (fun _ => r / 2)
  let B : Matrix Unit n ℝ := fun _ j => -v j / 2
  have hA : A.PosDef := Matrix.PosDef.diagonal (fun _ => by change 0 < r / 2; positivity)
  letI : Invertible A := hA.isUnit.invertible
  have hB : Bᴴ = (fun i (_ : Unit) => -v i / 2) := by
    funext i j
    change star (-v i / 2) = -v i / 2
    simp
  have hprod : Bᴴ * A⁻¹ * B = (1 / (2 * r)) • Matrix.vecMulVec v v := by
    funext i j
    change (∑ k : Unit, (∑ l : Unit, star (B l i) * A⁻¹ l k) * B k j) =
      (1 / (2 * r)) * (v i * v j)
    simp [A, B, Matrix.inv_subsingleton]
    field_simp
  have h := Matrix.PosDef.fromBlocks₁₁ B D hA
  rw [hprod] at h
  simpa only [borderedMatrix, A, B, hB] using h

/-- Equation (15), with the distinguished final coordinate supplied explicitly. -/
def equation15Matrix (last : n) (W T C : Matrix n n ℝ) (r : ℝ) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ :=
  borderedMatrix r (fun j => ∑ i, (T * C) i j)
    (matrixSymm (Wᵀ * T * C) -
      (1 / 2 : ℝ) • Matrix.vecMulVec (Pi.single last 1) (Pi.single last 1))

/-- The exact Schur complement of equation (15), before triangular congruence. -/
theorem equation15_schur (last : n) (W T C : Matrix n n ℝ) (r : ℝ) (hr : 0 < r) :
    (equation15Matrix last W T C r).PosSemidef ↔
      (matrixSymm (Wᵀ * T * C) -
        (1 / 2 : ℝ) • Matrix.vecMulVec (Pi.single last 1) (Pi.single last 1) -
        (1 / (2 * r)) • Matrix.vecMulVec
          (fun j => ∑ i, (T * C) i j) (fun j => ∑ i, (T * C) i j)).PosSemidef :=
  borderedMatrix_posSemidef_iff r hr _ _

/-- A real PSD matrix with zero diagonal vanishes. -/
theorem posSemidef_eq_zero_of_diagonal {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (hd : ∀ i, A i i = 0) : A = 0 := by
  ext i j
  have hx : star (Pi.single j (1 : ℝ)) ⬝ᵥ A *ᵥ Pi.single j 1 = 0 := by
    simpa using hd j
  have hz := (hA.dotProduct_mulVec_zero_iff).mp hx
  have hi := congrFun hz i
  simpa using hi

lemma matrixSymm_transpose (A : Matrix n n ℝ) : matrixSymm Aᵀ = matrixSymm A := by
  simp [matrixSymm, add_comm]

lemma matrixSymm_congruence (A D : Matrix n n ℝ) :
    Dᵀ * matrixSymm A * D = matrixSymm (Dᵀ * A * D) := by
  simp only [matrixSymm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  congr 1
  simp only [Matrix.mul_assoc]

lemma outer_congruence (v : n → ℝ) (D : Matrix n n ℝ) :
    Dᵀ * Matrix.vecMulVec v v * D =
      Matrix.vecMulVec (Dᵀ *ᵥ v) (Dᵀ *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]

lemma colSum_eq (A : Matrix n n ℝ) :
    (fun j => ∑ i, A i j) = Aᵀ *ᵥ (fun _ => 1) := by
  funext j
  simp [Matrix.mulVec, dotProduct]

/-- The reduced slack after the Schur complement and congruence by `C⁻¹`. -/
def reducedSlack (last : n) (W T C : Matrix n n ℝ) (r : ℝ) : Matrix n n ℝ :=
  matrixSymm (Tᵀ * W * C⁻¹) -
    (1 / 2 : ℝ) • Matrix.vecMulVec (C⁻¹ᵀ *ᵥ Pi.single last 1)
      (C⁻¹ᵀ *ᵥ Pi.single last 1) -
    (1 / (2 * r)) • Matrix.vecMulVec (Tᵀ *ᵥ (fun _ => 1)) (Tᵀ *ᵥ (fun _ => 1))

lemma equation15_congruence (last : n) (W T C : Matrix n n ℝ) (r : ℝ)
    (hC : IsUnit C) :
    C⁻¹ᵀ * (matrixSymm (Wᵀ * T * C) -
      (1 / 2 : ℝ) • Matrix.vecMulVec (Pi.single last 1) (Pi.single last 1) -
      (1 / (2 * r)) • Matrix.vecMulVec
        (fun j => ∑ i, (T * C) i j) (fun j => ∑ i, (T * C) i j)) * C⁻¹ =
      reducedSlack last W T C r := by
  letI : Invertible C := hC.invertible
  have hcancel : C⁻¹ᵀ *ᵥ ((T * C)ᵀ *ᵥ (fun _ => (1 : ℝ))) =
      Tᵀ *ᵥ (fun _ => 1) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
    simp [Matrix.mul_assoc]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    matrixSymm_congruence, outer_congruence, colSum_eq, hcancel, reducedSlack]
  congr 2
  have heq : C⁻¹ᵀ * (Wᵀ * T * C) * C⁻¹ = (Tᵀ * W * C⁻¹)ᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [heq, matrixSymm_transpose]

/-- The full Schur-and-congruence equivalence, starting from equation (15). -/
theorem equation15_reduced_iff (last : n) (W T C : Matrix n n ℝ) (r : ℝ)
    (hr : 0 < r) (hC : IsUnit C) :
    (equation15Matrix last W T C r).PosSemidef ↔ (reducedSlack last W T C r).PosSemidef := by
  rw [equation15_schur last W T C r hr]
  have hInv : IsUnit C⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hC
  rw [← equation15_congruence last W T C r hC]
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using hInv.posSemidef_star_left_conjugate_iff.symm

section Triangular
variable [LinearOrder n]

/-- The unit diagonal is included separately from lower triangularity. -/
def UnitLower (A : Matrix n n ℝ) : Prop := A.IsLowerTriangular ∧ ∀ i, A i i = 1

lemma UnitLower.det_eq_one {A : Matrix n n ℝ} (hA : UnitLower A) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A hA.1]
  simp [hA.2]

lemma UnitLower.isUnit {A : Matrix n n ℝ} (hA : UnitLower A) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, hA.det_eq_one]
  exact isUnit_one

lemma lower_mul_diag (A B : Matrix n n ℝ) (hA : A.IsLowerTriangular)
    (hB : B.IsLowerTriangular) (i : n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hB hj, mul_zero]
    · rw [hA hj, zero_mul]
  · simp

lemma UnitLower.inv {A : Matrix n n ℝ} (hA : UnitLower A) : UnitLower A⁻¹ := by
  letI : Invertible A := hA.isUnit.invertible
  have ht : A⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hA.1
  refine ⟨ht, fun i => ?_⟩
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (Matrix.mul_inv_of_invertible A)
  rw [lower_mul_diag A A⁻¹ hA.1 ht, hA.2] at h
  simpa using h

lemma UnitLower.mul {A B : Matrix n n ℝ} (hA : UnitLower A) (hB : UnitLower B) :
    UnitLower (A * B) := by
  refine ⟨hA.1.mul hB.1, fun i => ?_⟩
  rw [lower_mul_diag A B hA.1 hB.1, hA.2, hB.2, one_mul]

/-- Symmetrization is injective on lower triangular matrices. -/
theorem matrixSymm_injective_lower {A B : Matrix n n ℝ}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular)
    (h : matrixSymm A = matrixSymm B) : A = B := by
  ext i j
  have hij := congrArg (fun M : Matrix n n ℝ => M i j) h
  simp only [matrixSymm, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    smul_eq_mul] at hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · rw [hA hlt, hB hlt]
  · subst j; linarith
  · rw [hA hgt, hB hgt] at hij
    linarith

lemma transformed_lower {W T C : Matrix n n ℝ} (hW : UnitLower W)
    (hT : T.IsUpperTriangular) (hC : UnitLower C) :
    (Tᵀ * W * C⁻¹).IsLowerTriangular :=
  (hT.transpose.mul hW.1).mul hC.inv.1

lemma transformed_diag {W T C : Matrix n n ℝ} (hW : UnitLower W)
    (hT : T.IsUpperTriangular) (hC : UnitLower C) (i : n) :
    (Tᵀ * W * C⁻¹) i i = T i i := by
  rw [lower_mul_diag _ _ (hT.transpose.mul hW.1) hC.inv.1,
    lower_mul_diag _ _ hT.transpose hW.1, hW.2, hC.inv.2]
  simp

/-- The diagonal computation in Lemma 3.3 uses the original triangular constraints. -/
theorem reducedSlack_diag (last : n) {W T C : Matrix n n ℝ} (r : ℝ)
    (hW : UnitLower W) (hT : T.IsUpperTriangular) (hC : UnitLower C) (i : n) :
    reducedSlack last W T C r i i =
      T i i - (C⁻¹ last i)^2 / 2 - (∑ j, T j i)^2 / (2*r) := by
  have hd := transformed_diag hW hT hC i
  simp only [reducedSlack, matrixSymm, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, Matrix.vecMulVec_apply, hd]
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  change (1/2 : ℝ) * (T i i + T i i) - (1/2 : ℝ) * (C⁻¹ last i * C⁻¹ last i) -
    (1/(2*r)) * ((Tᵀ *ᵥ fun _ => 1) i * (Tᵀ *ᵥ fun _ => 1) i) = _
  rw [← colSum_eq]
  ring

/-- Necessity of all inequalities (16), from the actual block PSD condition (15). -/
theorem equation15_diagonal_necessary (last : n) {W T C : Matrix n n ℝ} (r : ℝ)
    (hr : 0 < r) (hW : UnitLower W) (hT : T.IsUpperTriangular) (hC : UnitLower C)
    (hPSD : (equation15Matrix last W T C r).PosSemidef) (i : n) :
    (∑ j, T j i)^2 / (2*r) ≤ T i i - (C⁻¹ last i)^2 / 2 := by
  have hs := (equation15_reduced_iff last W T C r hr hC.isUnit).mp hPSD
  have hd := hs.diag_nonneg (i := i)
  rw [reducedSlack_diag last r hW hT hC i] at hd
  linarith

/-- Tight diagonal conditions force the complete reduced slack to vanish. -/
theorem equation15_tight_slack_zero (last : n) {W T C : Matrix n n ℝ} (r : ℝ)
    (hr : 0 < r) (hW : UnitLower W) (hT : T.IsUpperTriangular) (hC : UnitLower C)
    (hPSD : (equation15Matrix last W T C r).PosSemidef)
    (htight : ∀ i, (∑ j, T j i)^2 / (2*r) = T i i - (C⁻¹ last i)^2 / 2) :
    reducedSlack last W T C r = 0 := by
  apply posSemidef_eq_zero_of_diagonal
    ((equation15_reduced_iff last W T C r hr hC.isUnit).mp hPSD)
  intro i
  rw [reducedSlack_diag last r hW hT hC i, htight i]
  ring

/-- The tight nonsingular uniqueness part of Lemma 3.3, for equation (15) itself. -/
theorem equation15_tight_unique (last : n) {W₁ W₂ T C : Matrix n n ℝ} (r : ℝ)
    (hr : 0 < r) (hW₁ : UnitLower W₁) (hW₂ : UnitLower W₂)
    (hT : T.IsUpperTriangular) (hC : UnitLower C) (hTunit : IsUnit T)
    (hPSD₁ : (equation15Matrix last W₁ T C r).PosSemidef)
    (hPSD₂ : (equation15Matrix last W₂ T C r).PosSemidef)
    (htight : ∀ i, (∑ j, T j i)^2 / (2*r) = T i i - (C⁻¹ last i)^2 / 2) :
    W₁ = W₂ := by
  have hs₁ := equation15_tight_slack_zero last r hr hW₁ hT hC hPSD₁ htight
  have hs₂ := equation15_tight_slack_zero last r hr hW₂ hT hC hPSD₂ htight
  have heq : matrixSymm (Tᵀ * W₁ * C⁻¹) = matrixSymm (Tᵀ * W₂ * C⁻¹) := by
    funext i j
    have h₁ := congrArg (fun M : Matrix n n ℝ => M i j) hs₁
    have h₂ := congrArg (fun M : Matrix n n ℝ => M i j) hs₂
    simp only [reducedSlack, Matrix.sub_apply, Matrix.zero_apply] at h₁ h₂
    linarith
  have hL := matrixSymm_injective_lower (transformed_lower hW₁ hT hC)
    (transformed_lower hW₂ hT hC) heq
  letI : Invertible C := hC.isUnit.invertible
  have hTtranspose : IsUnit Tᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det T).mp hTunit
  letI : Invertible Tᵀ := hTtranspose.invertible
  have hfinal := congrArg (fun M : Matrix n n ℝ => Tᵀ⁻¹ * M * C) hL
  simpa only [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one,
    ← Matrix.mul_assoc, Matrix.one_mul, Matrix.inv_mul_cancel_right_of_invertible] using hfinal

end Triangular
end GJP
