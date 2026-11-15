module
public import Continuation.GJP.DualCone
public import Continuation.GJP.DualUniqueness
public import Continuation.GJP.PositiveKernel
@[expose] public section
noncomputable section
open Matrix
namespace GJPDual

lemma slack_matrix {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) (y : Y N) :
    (conicMap W y - constant N).1.val = GJP.compactDualMatrix (Fin.last N) W y.2 y.1 := by
  ext i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
    simp [conicMap,mapLinear,linearMatrix,constant,constantMatrix,GJP.compactDualMatrix,
      GJP.borderedMatrix,Matrix.fromBlocks,Matrix.diagonal,Matrix.sub_apply]

lemma bordered_rate_pos {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (v : n → ℝ) (D : Matrix n n ℝ)
    (hM : (GJP.borderedMatrix r v D).PosSemidef) (hv : 0 < ∑ i,v i) : 0 < r := by
  have hr : 0 ≤ r := by
    have h := hM.diag_nonneg (i := Sum.inl ())
    change 0 ≤ r/2 at h
    linarith
  by_contra! hle
  have hr0 : r = 0 := le_antisymm hle hr
  have hd : GJP.borderedMatrix r v D (Sum.inl ()) (Sum.inl ()) = 0 := by
    simp [GJP.borderedMatrix,Matrix.fromBlocks,hr0]
  have hz := psd_column_zero hM (Sum.inl ()) hd
  have hvi (i : n) : v i = 0 := by
    have h := hz (Sum.inr i)
    change -v i/2 = 0 at h
    linarith
  simp [hvi] at hv

/-- Cone feasibility implies the positive-rate compact certificate used by GJP. -/
theorem compact_of_cone {N : ℕ} (W : Matrix (Q N) (Q N) ℝ) (y : Y N)
    (hy : conicMap W y - constant N ∈ cone N) :
    GJP.CompactDualFeasible (Fin.last N) W y.2 y.1 := by
  rcases hy with ⟨hM,hoff,hrow,hcol⟩
  rw [slack_matrix] at hM
  have hr (i : Q N) : (Pi.single (Fin.last N) 1 : Q N → ℝ) i ≤ ∑ j,y.2 i j := by
    have h := hrow i
    change 0 ≤ (∑ j,y.2 i j) - (Pi.single (Fin.last N) 1 : Q N → ℝ) i at h
    linarith
  have hc (j : Q N) : 0 ≤ ∑ i,y.2 i j := by
    simpa [conicMap,mapLinear,constant] using hcol j
  have ho (i j : Q N) (hij : i ≠ j) : y.2 i j ≤ 0 := by
    have h := hoff ⟨(i,j),hij⟩
    change 0 ≤ -y.2 i j - 0 at h
    linarith
  have hsum : 1 ≤ ∑ j,∑ i,y.2 i j := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hr i)
    calc
      1 ≤ ∑ i,∑ j,y.2 i j := by simpa using h
      _ = ∑ j,∑ i,y.2 i j := Finset.sum_comm
  have hp : 0 < y.1 := bordered_rate_pos y.1 _ _ hM (by linarith)
  refine ⟨hp,ho,?_,?_,hM⟩
  · intro i
    simpa [Matrix.mulVec,dotProduct] using hr i
  · intro j
    simpa [Matrix.mulVec,dotProduct] using hc j

end GJPDual
