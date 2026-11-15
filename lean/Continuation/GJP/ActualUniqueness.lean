module
public import Continuation.GJP.ActualDuality
public import Continuation.GJP.SmoothScaling
public import Continuation.Smooth.DroriOperational

@[expose] public section
noncomputable section
open Matrix Filter Topology
namespace GJP
variable {N : ℕ}

/-- Two actual methods attaining the sharp smooth-convex bound have identical coefficients. -/
theorem sharp_methods_equal (W V : RealizationCore.StrictHistory N) (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hW : ∀ z ∈ SmoothGramModel.actualLossSet N W.val L R,
      z ≤ L*R^2/(2*SmoothBenchmark.theta N N^2))
    (hV : ∀ z ∈ SmoothGramModel.actualLossSet N V.val L R,
      z ≤ L*R^2/(2*SmoothBenchmark.theta N N^2)) : W.val = V.val := by
  let W' : RealizationCore.StrictHistory N := ⟨L • W.val,by
    intro i j hij
    simp [W.property i j hij]⟩
  let V' : RealizationCore.StrictHistory N := ⟨L • V.val,by
    intro i j hij
    simp [V.property i j hij]⟩
  obtain ⟨AW,rW,hAW,hrW⟩ := GJPDual.normalized_approaching_certificates W' (uniform_bound_normalized W.val L R hL hR hW)
  obtain ⟨AV,rV,hAV,hrV⟩ := GJPDual.normalized_approaching_certificates V' (uniform_bound_normalized V.val L R hL hR hV)
  have heq := compactDual_approaching_method_unique (sourceMatrix 1 W'.val)
    (sourceMatrix 1 V'.val) AW AV rW rV (sourceMatrix_unitLower 1 W')
    (sourceMatrix_unitLower 1 V') hAW hAV hrW hrV
  have heq' : sourceMatrix L W.val = sourceMatrix L V.val := by
    simpa only [W',V',sourceMatrix_normalized] using heq
  exact sourceMatrix_injective L (ne_of_gt hL) heq'

/-- GJP Theorem 1.1: every actual sharp method is the implemented optimized gradient method. -/
theorem actual_method_unique (W : RealizationCore.StrictHistory N) (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hW : ∀ z ∈ SmoothGramModel.actualLossSet N W.val L R,
      z ≤ L*R^2/(2*SmoothBenchmark.theta N N^2)) : W.val = SmoothOGM.ogmW N L := by
  exact sharp_methods_equal W ⟨SmoothOGM.ogmW N L,SmoothOGM.ogmW_strict N L⟩
    L R hL hR hW (OGMVerified.lossSet_upper N L R hL)

/-- Sharp actual operational risk uniquely determines the full history matrix. -/
theorem operational_method_unique (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N)
    (hbound : MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N) d T ≤
      ((L*R^2/(2*SmoothBenchmark.theta N N^2) : ℝ) : EReal)) :
    RealizationCore.W_of N d T.val = SmoothOGM.ogmW N L := by
  apply actual_method_unique
    ⟨RealizationCore.W_of N d T.val,RealizationCore.W_of_strict N d T.val⟩ L R hL hR
  exact (MemoryDecision.risk_le_iff _ _ _ _ _).mp hbound

/-- The unique optimal history has exactly the OGM diagonal and strict-increment coordinates. -/
theorem operational_coordinates_unique (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N)
    (hbound : MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N) d T ≤
      ((L*R^2/(2*SmoothBenchmark.theta N N^2) : ℝ) : EReal)) :
    d = (OGMVerified.coordinates N L).1 ∧ T = (OGMVerified.coordinates N L).2 := by
  apply sourceMatrix_coordinates_injective L (ne_of_gt hL)
  apply congrArg (sourceMatrix L)
  rw [OGMVerified.coordinates_recover]
  exact operational_method_unique L R hL hR d T hbound

/-- The actual sharp-risk optimizers are exactly the OGM coefficient coordinates. -/
theorem operational_optimal_iff (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) :
    MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N) d T =
      ((L*R^2/(2*SmoothBenchmark.theta N N^2) : ℝ) : EReal) ↔
    d = (OGMVerified.coordinates N L).1 ∧ T = (OGMVerified.coordinates N L).2 := by
  constructor
  · intro h
    exact operational_coordinates_unique L R hL hR d T h.le
  · rintro ⟨rfl,rfl⟩
    exact SmoothDrori.operational_ogm_risk_eq N L R hN hL hR


end GJP
