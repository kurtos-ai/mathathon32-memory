module
public import Continuation.GJP.Elimination
public import Mathlib
@[expose] public section
noncomputable section
open Matrix Set
namespace GJPDual

abbrev Q (N : ℕ) := Fin (N+1)
abbrev Index (N : ℕ) := Unit ⊕ Q N

def symmetricSpace (N : ℕ) : Submodule ℝ (Matrix (Index N) (Index N) ℝ) where
  carrier := {M | M.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun ha hb => ha.add hb
  smul_mem' := fun a _ ha => ha.smul a

abbrev SymBlock (N : ℕ) := symmetricSpace N
abbrev Off (N : ℕ) := {ij : Q N × Q N // ij.1 ≠ ij.2}
abbrev E (N : ℕ) := SymBlock N × (Off N → ℝ) × (Q N → ℝ) × (Q N → ℝ)
abbrev Y (N : ℕ) := ℝ × Matrix (Q N) (Q N) ℝ

def linearMatrix {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) (y : Y N) :
    Matrix (Index N) (Index N) ℝ :=
  GJP.borderedMatrix y.1 (fun j => ∑ i, y.2 i j) (GJP.matrixSymm (Wᵀ*y.2))

lemma linearMatrix_symm {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) (y : Y N) :
    (linearMatrix W y).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
    simp [linearMatrix,GJP.borderedMatrix,GJP.matrixSymm,Matrix.fromBlocks,Matrix.diagonal,
      Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,Matrix.mul_apply,Finset.sum_add_distrib] <;>
    simp only [mul_comm] <;> ring

lemma linearMatrix_add {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) (y z : Y N) :
    linearMatrix W (y+z)=linearMatrix W y+linearMatrix W z := by
  ext i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
    simp [linearMatrix,GJP.borderedMatrix,GJP.matrixSymm,Matrix.fromBlocks,Matrix.diagonal,
      Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,Matrix.mul_add,
      Finset.sum_add_distrib,smul_eq_mul] <;> ring

lemma linearMatrix_smul {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) (a : ℝ) (y : Y N) :
    linearMatrix W (a • y)=a • linearMatrix W y := by
  have hs (j : Q N) : (∑ i, a * y.2 i j) = a * ∑ i, y.2 i j := by
    rw [Finset.mul_sum]
  ext i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
    simp [linearMatrix,GJP.borderedMatrix,GJP.matrixSymm,Matrix.fromBlocks,Matrix.diagonal,
      Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,Matrix.mul_smul,
      smul_eq_mul] <;> (try simp only [hs]) <;> ring

def mapLinear {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) : Y N →ₗ[ℝ] E N where
  toFun y := (⟨linearMatrix W y,linearMatrix_symm W y⟩,
    (fun ij => -y.2 ij.val.1 ij.val.2),
    (fun i => ∑ j, y.2 i j),(fun j => ∑ i, y.2 i j))
  map_add' y z := by
    apply Prod.ext
    · apply Subtype.ext; exact linearMatrix_add W y z
    · ext i <;> simp [Finset.sum_add_distrib] <;> ring
  map_smul' a y := by
    apply Prod.ext
    · apply Subtype.ext; exact linearMatrix_smul W a y
    · ext i <;> simp [Finset.mul_sum] <;> ring

/-- The canonical conic map for the compact GJP distance-to-function dual. -/
def conicMap {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) : Y N →L[ℝ] E N :=
  (mapLinear W).toContinuousLinearMap

def cost (N : ℕ) : Y N →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Matrix (Q N) (Q N) ℝ)

def constantMatrix (N : ℕ) : Matrix (Index N) (Index N) ℝ :=
  GJP.borderedMatrix 0 (fun _ => 0)
    ((1/2 : ℝ) • Matrix.vecMulVec (Pi.single (Fin.last N) 1) (Pi.single (Fin.last N) 1))

lemma constantMatrix_symm (N : ℕ) : (constantMatrix N).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
    simp [constantMatrix,GJP.borderedMatrix,Matrix.fromBlocks,Matrix.diagonal,
      Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul] <;> ring

/-- The affine shift: terminal gradient square and terminal row normalization. -/
def constant (N : ℕ) : E N :=
  (⟨constantMatrix N,constantMatrix_symm N⟩,0,Pi.single (Fin.last N) 1,0)

/-- Product-cone membership is stated directly in the symmetric matrix subspace. -/
def ConePred {N : ℕ} (e : E N) : Prop :=
  (e.1.val).PosSemidef ∧ (∀ ij,0 ≤ e.2.1 ij) ∧ (∀ i,0 ≤ e.2.2.1 i) ∧ (∀ i,0 ≤ e.2.2.2 i)

lemma conePred_closed (N : ℕ) : IsClosed {e : E N | ConePred e} := by
  have hm : IsClosed {e : E N | e.1.val.PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_subtype_val.comp continuous_fst)
  have ho : IsClosed {e : E N | ∀ ij, 0 ≤ e.2.1 ij} :=
    by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun ij => isClosed_le continuous_const (by fun_prop)
  have hr : IsClosed {e : E N | ∀ i, 0 ≤ e.2.2.1 i} :=
    by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  have hc : IsClosed {e : E N | ∀ i, 0 ≤ e.2.2.2 i} :=
    by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  exact hm.inter (ho.inter (hr.inter hc))

/-- The closed convex product cone used for conic separation. -/
def cone (N : ℕ) : ProperCone ℝ (E N) where
  carrier := {e | ConePred e}
  zero_mem' := ⟨Matrix.PosSemidef.zero, by simp, by simp, by simp⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨ha.1.add hb.1, fun i => add_nonneg (ha.2.1 i) (hb.2.1 i),
      fun i => add_nonneg (ha.2.2.1 i) (hb.2.2.1 i),
      fun i => add_nonneg (ha.2.2.2 i) (hb.2.2.2 i)⟩
  smul_mem' := by
    intro a b hb
    exact ⟨hb.1.smul a.property, fun i => mul_nonneg a.property (hb.2.1 i),
      fun i => mul_nonneg a.property (hb.2.2.1 i),
      fun i => mul_nonneg a.property (hb.2.2.2 i)⟩
  isClosed' := conePred_closed N

@[simp] lemma mem_cone {N : ℕ} (e : E N) : e ∈ cone N ↔ ConePred e := Iff.rfl

end GJPDual
