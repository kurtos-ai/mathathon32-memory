module
public import Continuation.Smooth.GramReconstruction
public import Continuation.Smooth.Sufficient
@[expose] public section

open Matrix
namespace SmoothGramModel
variable {N n : ℕ} {L R : ℝ}

/-- Every feasible finite data set is realized by an actual instance in dimension N+2. -/
theorem realize_feasible (hL : 0 < L) (hR : 0 ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Matrix (Index N) (Index N) ℝ) (φ : Fin (N+1) → ℝ)
    (hF : Feasible W L R M φ) :
    ∃ I : SmoothAttain.Instance (N+2) L R, terminalLoss I W = φ (Fin.last N) := by
  obtain ⟨B,hB⟩ := exists_gram_in_dimension N M hF.1
  obtain ⟨F,G,hGrad,hConv,hLip,hData⟩ := SmoothInterpolation.sufficient hL
    (fun i => Fintype.linearCombination ℝ B (v W i))
    (fun i => Fintype.linearCombination ℝ B (w i)) (value φ)
    (model_data_inequalities W M φ hF B hB)
  have hK : Real.toNNReal L = (⟨L,hL.le⟩ : NNReal) := by
    apply NNReal.coe_injective
    exact Real.coe_toNNReal _ hL.le
  rw [hK] at hLip
  exact realize_of_interpolant hL hR W M φ hF B hB F G hGrad hConv hLip
    (fun i => (hData i).1) (fun i => (hData i).2)

theorem modelLossSet_subset_actualLossSet (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) :
    modelLossSet N W L R ⊆ actualLossSet N W L R := by
  rintro z ⟨M,φ,hF,rfl⟩
  obtain ⟨I,hI⟩ := realize_feasible hL hR W M φ hF
  exact ⟨N+1,I,hI.symm⟩

/-- Exactness over every positive finite dimension, including the causal query constraints. -/
theorem actualLossSet_eq_modelLossSet (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) :
    actualLossSet N W L R = modelLossSet N W L R :=
  Set.Subset.antisymm (actualLossSet_subset_modelLossSet N W L R hL)
    (modelLossSet_subset_actualLossSet N W L R hL hR)

theorem dimension_reduction (I : SmoothAttain.Instance n L R) (hL : 0 < L)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    ∃ J : SmoothAttain.Instance (N+2) L R, terminalLoss J W = terminalLoss I W := by
  have hR : 0 ≤ R := (norm_nonneg _).trans I.near
  obtain ⟨J,hJ⟩ := realize_feasible hL hR W (gram (physical I W)) (values I W)
    (actual_feasible I hL W)
  exact ⟨J,hJ⟩

theorem uniform_bound_iff (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R γ : ℝ) (hL : 0 < L) (hR : 0 ≤ R) :
    (∀ z ∈ actualLossSet N W L R, z ≤ γ) ↔
    (∀ M φ, Feasible W L R M φ → φ (Fin.last N) ≤ γ) := by
  rw [actualLossSet_eq_modelLossSet N W L R hL hR]
  constructor
  · intro h M φ hF
    exact h _ ⟨M,φ,hF,rfl⟩
  · rintro h z ⟨M,φ,hF,rfl⟩
    exact h M φ hF

end SmoothGramModel
