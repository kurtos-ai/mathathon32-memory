module
public import Submission2026.NearQuadratic.SmoothTransfer
public import Continuation.Smooth.Necessary
@[expose] public section
noncomputable section
namespace NearQuadratic
open scoped InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Actual differentiability and a Lipschitz gradient imply the upper-envelope
hypothesis used by the smooth transfer lemmas. -/
theorem actual_smooth_lower_data {f : V → ℝ} {G : V → V} {L : NNReal}
    (hf : ∀ x, HasGradientAt f (G x) x) (hLip : LipschitzWith L G)
    (xStar : V) (hmin : ∀ x, f xStar ≤ f x) :
    SmoothLowerData V f G (f xStar) (L : ℝ) := by
  refine ⟨L.coe_nonneg,hmin,?_⟩
  intro x y
  simpa only [add_sub_cancel] using SmoothNecessary.descent hf hLip x (y-x)

/-- The gradient-gap estimate for actual globally smooth functions with a minimizer. -/
theorem actual_gradient_norm_sq_le {f : V → ℝ} {G : V → V} {L : NNReal}
    (hf : ∀ x, HasGradientAt f (G x) x) (hLip : LipschitzWith L G)
    (xStar : V) (hmin : ∀ x, f xStar ≤ f x) (x : V) :
    ‖G x‖^2 ≤ 2*(L : ℝ)*(f x-f xStar) := by
  have h := actual_smooth_lower_data hf hLip xStar hmin
  exact gradient_norm_sq_le h.hLf_nonneg h.hfStar_le h.hSmooth x

/-- Appendix transport's objective comparison for actual smooth objectives.
No supplied upper-envelope or gradient-gap conclusion is required. -/
theorem actual_smooth_objective_transfer {f : V → ℝ} {G : V → V} {L : NNReal}
    (hf : ∀ x, HasGradientAt f (G x) x) (hLip : LipschitzWith L G)
    (xStar : V) (hmin : ∀ x, f xStar ≤ f x)
    (xA xB : V) (D : ℝ) (hD : 0 ≤ D) (hdist : ‖xB-xA‖ ≤ D) :
    f xB-f xStar ≤
      (Real.sqrt (f xA-f xStar)+Real.sqrt ((L : ℝ)/2)*D)^2 := by
  have h := actual_smooth_lower_data hf hLip xStar hmin
  exact smooth_objective_transfer h.hLf_nonneg hD h.hfStar_le h.hSmooth xA xB hdist

end NearQuadratic
