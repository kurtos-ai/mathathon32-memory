module
public import Continuation.GJP.ConicSeparation
public import Continuation.GJP.DualAnnihilator
public import Continuation.GJP.DualRealization
public import Continuation.GJP.DualFeasibility
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GJPDual

/-- Every actual uniform bound admits arbitrarily close compact dual certificates. -/
theorem actual_bound_approximate_certificate {N : ℕ}
    (W : Matrix (Q N) (Q N) ℝ) (hW : GJP.UnitLower W) (v γ : ℝ) (hγ : v < γ)
    (hv : ∀ t ∈ SmoothGramModel.actualLossSet N (GJP.additiveHistory W) 1 (Real.sqrt 2), t ≤ v) :
    ∃ A r, GJP.CompactDualFeasible (Fin.last N) W A r ∧ r ≤ γ := by
  obtain ⟨y,hy,hcost⟩ := ConicDuality.approximate_dual (cone N) (conicMap W) (cost N)
    (constant N) (positive_annihilator_zero W hW) v γ hγ
    (positive_functional_bound W hW v hv)
  exact ⟨y.2,y.1,compact_of_cone W y hy,hcost⟩

/-- Actual sharp normalized risk produces the approaching certificates required
by the independently proved limiting-factor theorem. -/
theorem normalized_approaching_certificates {N : ℕ} (V : RealizationCore.StrictHistory N)
    (hv : ∀ t ∈ SmoothGramModel.actualLossSet N V.val 1 (Real.sqrt 2), t ≤ GJP.rOGM N) :
    ∃ (As : ℕ → Matrix (Q N) (Q N) ℝ) (rs : ℕ → ℝ),
      (∀ k, GJP.CompactDualFeasible (Fin.last N) (GJP.sourceMatrix 1 V.val) (As k) (rs k)) ∧
      Tendsto rs atTop (𝓝 (GJP.rOGM N)) := by
  let W := GJP.sourceMatrix 1 V.val
  have hW : GJP.UnitLower W := GJP.sourceMatrix_unitLower 1 V
  have hbound : ∀ t ∈ SmoothGramModel.actualLossSet N (GJP.additiveHistory W) 1 (Real.sqrt 2),
      t ≤ GJP.rOGM N := by simpa [W,GJP.additiveHistory_sourceMatrix] using hv
  have hex (k : ℕ) : ∃ A r, GJP.CompactDualFeasible (Fin.last N) W A r ∧
      r ≤ GJP.rOGM N + 1 / ((k:ℝ)+1) := by
    apply actual_bound_approximate_certificate W hW _ _ _ hbound
    have hk : 0 < 1 / ((k:ℝ)+1) := by positivity
    linarith
  choose As rs hs using hex
  refine ⟨As,rs,fun k => (hs k).1,?_⟩
  have hu : Tendsto (fun k : ℕ => GJP.rOGM N + 1 / ((k:ℝ)+1)) atTop (𝓝 (GJP.rOGM N)) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun k => GJP.compactDual_rate_lower hW (hs k).1) (fun k => (hs k).2)

end GJPDual
