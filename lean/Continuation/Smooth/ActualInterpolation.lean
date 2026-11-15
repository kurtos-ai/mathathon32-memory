module
public import Continuation.Smooth.Necessary
public import Continuation.Smooth.Attain.Instances
@[expose] public section

open scoped InnerProductSpace

namespace SmoothAttain

theorem Instance.interpolation_necessary {n : ℕ} {L R : ℝ}
    (I : Instance n L R) (hL : 0 < L) (x y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ I.f x - I.f y - ⟪I.G y, x-y⟫_ℝ - 1/(2*L) * ‖I.G x-I.G y‖^2 := by
  have h := SmoothNecessary.interpolation_necessary I.hasGrad I.convex
    (show 0 < (I.lip:ℝ) by rw [I.lip_eq]; exact hL) I.lipschitz x y
  simpa only [I.lip_eq] using h

theorem Instance.gradient_at_minimizer {n : ℕ} {L R : ℝ} (I : Instance n L R) :
    I.G I.xStar = 0 := by
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
  rw [map_zero]
  exact (I.isMin.isLocalMin (by simp)).hasFDerivAt_eq_zero (I.hasGrad I.xStar).hasFDerivAt

end SmoothAttain
