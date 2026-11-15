module
public import Submission2026.NearQuadratic.NearTerminal
public import Submission2026.NearQuadratic.ResponseTrajectory

@[expose] public section

namespace NearQuadratic
namespace ResponseBridge

open RealInnerProductSpace
open Trajectory

variable {N : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Actual perturbed-gradient trajectory to `O(ε)` quadratic-response loss,
with only the two response operator estimates left as inputs. -/
theorem terminal_gap_of_response_estimates
    (A : Fin (N+1) → Fin (N+1) → ℝ) (hStrict : IsStrictLowerTri' A)
    (Q : V →L[ℝ] V) (f : V → ℝ) (r : V → V) (xStar x0 : V)
    (L0 ε ε0 R πA : ℝ) (rho : ℕ → ℝ)
    (hData : PerturbedQuadraticData V Q xStar f r L0 ε)
    (hSymm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (hε_le : ε ≤ ε0) (hε0 : 0 ≤ ε0) (hR : 0 ≤ R) (hπ : 0 ≤ πA)
    (hR0 : ‖x0-xStar‖ ≤ R) (hrho : ∀ j, 0 ≤ rho j)
    (hROp : ∀ j, j < N → ‖ROp (extend A) Q N j‖ ≤ rho j)
    (hz : ‖pOp (extend A) Q N (x0-xStar)‖ ≤ R * πA) :
    |f (xStar + error A Q r xStar x0 N) - f xStar -
        quadForm Q (pOp (extend A) Q N (x0-xStar))| ≤
      ε * R ^ 2 * kappa_const (hA_of A (L0+ε0) ⟨N, by omega⟩) πA
        (betaCoeff N rho (hSeq A (L0+ε0))) L0 ε0 := by
  have hdisp := actual_response_displacement_bound A hStrict Q r xStar x0
    L0 ε ε0 R rho hData.hε_nonneg hε_le (by linarith [hData.hL0_nonneg]) hR
    hData.hQ_bound hData.hr_zero hData.hr_lip hR0 hrho hROp
  exact terminal_gap_of_actual_trajectory A hStrict Q f r xStar x0
    L0 ε ε0 R πA (betaCoeff N rho (hSeq A (L0+ε0))) hData hSymm hε_le hε0 hR hπ
    hR0 (pOp (extend A) Q N (x0-xStar)) hdisp hz

end ResponseBridge
end NearQuadratic
