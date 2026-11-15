module
/-
Pointwise near-quadratic terminal transport.  The response displacement and
spectral response-norm bounds are explicit independent inputs; importing this
module does not claim either one.  They are the remaining bridge to the
polynomial response API, not hypotheses of the objective-gap inequality itself.
-/
public import Submission2026.NearQuadratic.ObjectiveResidual
public import Submission2026.NearQuadratic.ObjectiveTransfer
public import Submission2026.NearQuadratic.TrajectoryNeumann

@[expose] public section

namespace NearQuadratic

open RealInnerProductSpace
open Trajectory

variable {N : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The actual residual-driven trajectory has the source's `O(ε)` objective-gap
transfer as soon as its two response estimates are supplied. -/
theorem terminal_gap_of_actual_trajectory
    (A : Fin (N+1) → Fin (N+1) → ℝ) (hStrict : IsStrictLowerTri' A)
    (Q : V →L[ℝ] V) (f : V → ℝ) (r : V → V) (xStar x0 : V) (L0 ε ε0 R πA βA : ℝ)
    (hData : PerturbedQuadraticData V Q xStar f r L0 ε)
    (hSymm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (hε_le : ε ≤ ε0) (hε0 : 0 ≤ ε0) (hR : 0 ≤ R) (hπ : 0 ≤ πA)
    (hR0 : ‖x0 - xStar‖ ≤ R)
    (z : V)
    (hresponse : ‖error A Q r xStar x0 N - z‖ ≤ ε * R * βA)
    (hz : ‖z‖ ≤ R * πA) :
    |f (xStar + error A Q r xStar x0 N) - f xStar - quadForm Q z| ≤
      ε * R ^ 2 * kappa_const (hA_of A (L0+ε0) ⟨N, by omega⟩) πA βA L0 ε0 := by
  let w := error A Q r xStar x0 N
  let hQ : QData V Q L0 :=
    { hL₀_nonneg := hData.hL0_nonneg
      hQ_nonneg := hData.hQ_nonneg
      hQ_bound := hData.hQ_bound
      hQ_symm := hSymm }
  apply terminal_gap_transfer hQ hData.hε_nonneg hε0 hε_le hR hπ
    (w := w) (z := z) (f_at_w := f (xStar + w)) (fStar := f xStar)
  · have hres := residual_objective_estimate hData (xStar + w)
    simpa only [qForm, quadForm, add_sub_cancel_left] using hres
  · exact terminal_error_norm_le_hA_of A hStrict Q r xStar x0 L0 ε ε0 R
      hData.hε_nonneg hε_le (by linarith [hData.hL0_nonneg]) hR hData.hQ_bound
      hData.hr_zero hData.hr_lip hR0
  · exact hresponse
  · exact hz

end NearQuadratic
