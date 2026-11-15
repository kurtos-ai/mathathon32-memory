module
public import Continuation.GJP.Elimination
public import Continuation.OracleTrajectory
public import RealizationCore.Coordinates

@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The source paper uses a unit lower matrix with a minus sign and an explicit `1/L`.
The repository stores the strictly lower additive history coefficients. -/
def sourceMatrix (L : ℝ) (W : Matrix n n ℝ) : Matrix n n ℝ := 1 - L • W

lemma sourceMatrix_entry_lt [LinearOrder n] (L : ℝ) (W : Matrix n n ℝ) (i j : n) (hji : j < i) :
    sourceMatrix L W i j = -L * W i j := by
  simp [sourceMatrix, Matrix.one_apply, ne_of_gt hji]

lemma sourceMatrix_injective (L : ℝ) (hL : L ≠ 0) : Function.Injective (sourceMatrix (n := n) L) := by
  intro W V h
  funext i j
  have heq := congrArg (fun A : Matrix n n ℝ => A i j) h
  simp only [sourceMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at heq
  exact mul_left_cancel₀ hL (by linarith)

variable {N : ℕ}

lemma sourceMatrix_unitLower (L : ℝ) (W : RealizationCore.StrictHistory N) :
    UnitLower (sourceMatrix L W.val) := by
  constructor
  · intro i j hij
    have hij' : i < j := hij
    have hval : i.val ≤ j.val := le_of_lt hij'
    simp [sourceMatrix, W.property i j hval, Matrix.one_apply, ne_of_lt hij']
  · intro i
    simp [sourceMatrix, W.property i i le_rfl]

/-- Exact causal trajectory identity in the source paper's coefficient convention. -/
theorem run_sourceMatrix {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ) (hL : L ≠ 0) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : V → V) (x0 : V) (i : Fin (N+1)) :
    OracleTrajectory.run W G x0 i = x0 - (1/L) •
      ∑ j : Fin i.val, sourceMatrix L W i ⟨j.val, by omega⟩ •
        G (OracleTrajectory.run W G x0 ⟨j.val, by omega⟩) := by
  rw [OracleTrajectory.run_eq]
  rw [Finset.smul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, sourceMatrix_entry_lt L W i ⟨j.val, by omega⟩ (by exact j.isLt)]
  rw [← neg_smul]
  congr 1
  field_simp

/-- Equality in the source coefficient convention gives equality of actual schedules. -/
theorem sourceMatrix_coordinates_injective (L : ℝ) (hL : L ≠ 0)
    (d₁ d₂ : Fin N → ℝ) (T₁ T₂ : RealizationCore.StrictIncrement N)
    (h : sourceMatrix L (RealizationCore.W_of N d₁ T₁.val) =
      sourceMatrix L (RealizationCore.W_of N d₂ T₂.val)) : d₁ = d₂ ∧ T₁ = T₂ := by
  have hW := sourceMatrix_injective L hL h
  have hd := congrArg (RealizationCore.d_of N) hW
  have hT := congrArg (RealizationCore.T_of N) hW
  constructor
  · simpa only [RealizationCore.d_of_W_of] using hd
  · apply Subtype.ext
    simpa only [RealizationCore.T_of_W_of N d₁ T₁.val T₁.property,
      RealizationCore.T_of_W_of N d₂ T₂.val T₂.property] using hT

end GJP
