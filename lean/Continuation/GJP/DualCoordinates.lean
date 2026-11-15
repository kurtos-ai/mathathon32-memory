module
public import Continuation.GJP.DualCone
@[expose] public section
noncomputable section
open Matrix
namespace GJPDual

lemma matrixSymm_symm {n : Type*} (M : Matrix n n ℝ) : (GJP.matrixSymm M).IsSymm := by
  change ((1/2:ℝ) • (M+Mᵀ))ᵀ = (1/2:ℝ) • (M+Mᵀ)
  simp only [Matrix.transpose_smul,Matrix.transpose_add,Matrix.transpose_transpose]
  rw [add_comm]

lemma matrixSymm_of_symm {n : Type*} (M : Matrix n n ℝ) (hM : M.IsSymm) :
    GJP.matrixSymm M=M := by
  rw [GJP.matrixSymm,hM]
  ext i j
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]
  ring

/-- Symmetric projection into the cone's matrix component. -/
def symmetrize (N : ℕ) : Matrix (Index N) (Index N) ℝ →ₗ[ℝ] SymBlock N where
  toFun M := ⟨GJP.matrixSymm M,matrixSymm_symm M⟩
  map_add' M D := by
    apply Subtype.ext
    change GJP.matrixSymm (M+D)=GJP.matrixSymm M+GJP.matrixSymm D
    simp only [GJP.matrixSymm,Matrix.transpose_add,smul_add]
    abel
  map_smul' a M := by
    apply Subtype.ext
    change GJP.matrixSymm (a • M)=a • GJP.matrixSymm M
    simp only [GJP.matrixSymm,Matrix.transpose_smul,← smul_add,smul_smul]
    rw [mul_comm]

def matrixInjection (N : ℕ) : SymBlock N →ₗ[ℝ] E N where
  toFun M := (M,0,0,0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def offInjection (N : ℕ) : (Off N → ℝ) →ₗ[ℝ] E N where
  toFun v := (0,v,0,0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def rowInjection (N : ℕ) : (Q N → ℝ) →ₗ[ℝ] E N where
  toFun v := (0,0,v,0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def colInjection (N : ℕ) : (Q N → ℝ) →ₗ[ℝ] E N where
  toFun v := (0,0,0,v)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def matrixFunctional {N : ℕ} (F : E N →L[ℝ] ℝ) :
    Matrix (Index N) (Index N) ℝ →ₗ[ℝ] ℝ :=
  F.toLinearMap.comp ((matrixInjection N).comp (symmetrize N))

def gram {N : ℕ} (F : E N →L[ℝ] ℝ) : Matrix (Index N) (Index N) ℝ :=
  fun i j => matrixFunctional F (Matrix.single i j 1)

def offWeight {N : ℕ} (F : E N →L[ℝ] ℝ) (ij : Off N) : ℝ :=
  F (offInjection N (Pi.single ij 1))
def rowWeight {N : ℕ} (F : E N →L[ℝ] ℝ) (i : Q N) : ℝ :=
  F (rowInjection N (Pi.single i 1))
def colWeight {N : ℕ} (F : E N →L[ℝ] ℝ) (i : Q N) : ℝ :=
  F (colInjection N (Pi.single i 1))

lemma matrixFunctional_eq {N : ℕ} (F : E N →L[ℝ] ℝ)
    (M : Matrix (Index N) (Index N) ℝ) :
    matrixFunctional F M = ∑ i, ∑ j, M i j * gram F i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  congr 1
  funext i
  congr 1
  funext j
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j 1 by
    rw [Matrix.smul_single]; simp]
  simp only [map_smul,smul_eq_mul,gram]

lemma linear_pi_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (F : (n → ℝ) →ₗ[ℝ] ℝ) (v : n → ℝ) :
    F v = ∑ i, v i * F (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Pi.single i (v i) = v i • Pi.single i 1 by
    rw [← Pi.single_smul' i (v i) (1:ℝ)]; simp]
  simp only [map_smul,smul_eq_mul]

lemma functional_eq {N : ℕ} (F : E N →L[ℝ] ℝ) (e : E N) :
    F e = (∑ i,∑ j,e.1.val i j * gram F i j) +
      (∑ ij,e.2.1 ij * offWeight F ij) +
      (∑ i,e.2.2.1 i * rowWeight F i) +
      ∑ i,e.2.2.2 i * colWeight F i := by
  have he : e = matrixInjection N e.1 + offInjection N e.2.1 +
      rowInjection N e.2.2.1 + colInjection N e.2.2.2 := by ext <;> simp [matrixInjection,offInjection,rowInjection,colInjection]
  have hm : F (matrixInjection N e.1) = matrixFunctional F e.1.val := by
    change F (matrixInjection N e.1) = F (matrixInjection N (symmetrize N e.1.val))
    congr 2
    apply Subtype.ext
    exact (matrixSymm_of_symm _ e.1.property).symm
  have ho : F (offInjection N e.2.1) = ∑ ij,e.2.1 ij * offWeight F ij :=
    linear_pi_eq_sum (F.toLinearMap.comp (offInjection N)) e.2.1
  have hr : F (rowInjection N e.2.2.1) = ∑ i,e.2.2.1 i * rowWeight F i :=
    linear_pi_eq_sum (F.toLinearMap.comp (rowInjection N)) e.2.2.1
  have hc : F (colInjection N e.2.2.2) = ∑ i,e.2.2.2 i * colWeight F i :=
    linear_pi_eq_sum (F.toLinearMap.comp (colInjection N)) e.2.2.2
  calc F e = F (matrixInjection N e.1) + F (offInjection N e.2.1) +
        F (rowInjection N e.2.2.1) + F (colInjection N e.2.2.2) := by
          simpa only [map_add] using congrArg F he
    _ = _ := by rw [hm,matrixFunctional_eq,ho,hr,hc]

lemma gram_symm {N : ℕ} (F : E N →L[ℝ] ℝ) : (gram F).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change matrixFunctional F (Matrix.single j i 1) = matrixFunctional F (Matrix.single i j 1)
  change F (matrixInjection N (symmetrize N (Matrix.single j i 1))) =
    F (matrixInjection N (symmetrize N (Matrix.single i j 1)))
  congr 2
  apply Subtype.ext
  change GJP.matrixSymm (Matrix.single j i 1) = GJP.matrixSymm (Matrix.single i j 1)
  rw [← Matrix.transpose_single, GJP.matrixSymm_transpose]

lemma gram_psd {N : ℕ} (F : E N →L[ℝ] ℝ)
    (hF : ∀ e ∈ cone N,0 ≤ F e) : (gram F).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using (gram_symm F).eq
  intro x
  have hp : (Matrix.vecMulVec x x).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star x
  have hi : matrixInjection N (symmetrize N (Matrix.vecMulVec x x)) ∈ cone N := by
    refine ⟨?_,by simp [matrixInjection],by simp [matrixInjection],by simp [matrixInjection]⟩
    change (GJP.matrixSymm (Matrix.vecMulVec x x)).PosSemidef
    rw [matrixSymm_of_symm _ (by ext i j; simp [Matrix.vecMulVec,mul_comm])]
    exact hp
  have h := hF _ hi
  change 0 ≤ matrixFunctional F (Matrix.vecMulVec x x) at h
  rw [matrixFunctional_eq] at h
  simpa only [Matrix.vecMulVec_apply,star_trivial,Matrix.mulVec,dotProduct,
    Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using h

lemma rowWeight_nonneg {N : ℕ} (F : E N →L[ℝ] ℝ)
    (hF : ∀ e ∈ cone N,0 ≤ F e) (i : Q N) : 0 ≤ rowWeight F i := by
  apply hF
  refine ⟨Matrix.PosSemidef.zero,by simp [rowInjection],?_,by simp [rowInjection]⟩
  intro j
  change 0 ≤ (Pi.single i (1:ℝ) : Q N → ℝ) j
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

lemma colWeight_nonneg {N : ℕ} (F : E N →L[ℝ] ℝ)
    (hF : ∀ e ∈ cone N,0 ≤ F e) (i : Q N) : 0 ≤ colWeight F i := by
  apply hF
  refine ⟨Matrix.PosSemidef.zero,by simp [colInjection],by simp [colInjection],?_⟩
  intro j
  change 0 ≤ (Pi.single i (1:ℝ) : Q N → ℝ) j
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

lemma offWeight_nonneg {N : ℕ} (F : E N →L[ℝ] ℝ)
    (hF : ∀ e ∈ cone N,0 ≤ F e) (ij : Off N) : 0 ≤ offWeight F ij := by
  apply hF
  refine ⟨Matrix.PosSemidef.zero,?_,by simp [offInjection],by simp [offInjection]⟩
  intro kl
  change 0 ≤ (Pi.single ij (1:ℝ) : Off N → ℝ) kl
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

end GJPDual
