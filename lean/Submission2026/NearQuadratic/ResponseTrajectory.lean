module
public import Submission2026.NearQuadratic.Response
public import Submission2026.NearQuadratic.TrajectoryNeumann

@[expose] public section

namespace NearQuadratic
namespace ResponseBridge

open Finset BigOperators
open Trajectory

variable {N : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Total natural-index extension of a finite schedule. -/
def extend (A : Fin (N+1) → Fin (N+1) → ℝ) (n j : ℕ) : ℝ :=
  if hn : n < N+1 then if hj : j < N+1 then A ⟨n, hn⟩ ⟨j, hj⟩ else 0 else 0

/-- Residual samples at the actual query trajectory. -/
noncomputable def residualSeq (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V)
    (r : V → V) (xStar x0 : V) : ℕ → V :=
  fun n => r (xStar + error A Q r xStar x0 n)

/-- The generic forced linear recursion and the actual finite-horizon perturbed
trajectory coincide at every state through `N`. -/
theorem response_eq_error (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V)
    (r : V → V) (xStar x0 : V) :
    ∀ n, n < N+1 →
      traj (extend A) Q (residualSeq A Q r xStar x0) (x0-xStar) n =
        error A Q r xStar x0 n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    cases n with
    | zero => simp [traj_zero, error_zero]
    | succ n =>
      have hlt : n < N := by omega
      rw [traj_succ (A:=extend A) (Q:=Q) (r:=residualSeq A Q r xStar x0)
          (e0:=x0-xStar) n,
        error_step A Q r xStar x0 hlt]
      apply congrArg (HAdd.hAdd (x0-xStar))
      apply Finset.sum_congr rfl
      intro k _
      have hk : k.val < n+1 := k.isLt
      rw [ih k.val hk (by omega)]
      have hkN : k.val ≤ N := by omega
      simp [extend, hn, residualSeq, hkN]

/-- The `h` sequence used by the response bound is exactly `hA_of` through the
finite horizon. -/
noncomputable def hSeq (A : Fin (N+1) → Fin (N+1) → ℝ) (L : ℝ) : ℕ → ℝ :=
  fun j => if hj : j < N+1 then hA_of A L ⟨j, hj⟩ else 0

/-- Terminal response displacement for the actual perturbed-gradient trajectory.
The only response-side input is the operator-norm majorant `rho`. -/
theorem actual_response_displacement_bound
    (A : Fin (N+1) → Fin (N+1) → ℝ) (hStrict : IsStrictLowerTri' A)
    (Q : V →L[ℝ] V) (r : V → V) (xStar x0 : V)
    (L0 ε ε0 R : ℝ) (rho : ℕ → ℝ)
    (hε : 0 ≤ ε) (hε_le : ε ≤ ε0) (hL : 0 ≤ L0+ε0) (hR : 0 ≤ R)
    (hQ : ∀ v, ‖Q v‖ ≤ L0 * ‖v‖)
    (hr0 : r xStar = 0) (hLip : ∀ x y, ‖r x-r y‖ ≤ ε * ‖x-y‖)
    (hR0 : ‖x0-xStar‖ ≤ R) (hrho : ∀ j, 0 ≤ rho j)
    (hROp : ∀ j, j < N → ‖ROp (extend A) Q N j‖ ≤ rho j) :
    ‖error A Q r xStar x0 N - pOp (extend A) Q N (x0-xStar)‖ ≤
      ε * R * betaCoeff N rho (hSeq A (L0+ε0)) := by
  let rseq := residualSeq A Q r xStar x0
  have hres : ∀ j, j < N → ‖rseq j‖ ≤ ε * ‖traj (extend A) Q rseq (x0-xStar) j‖ := by
    intro j hj
    rw [response_eq_error A Q r xStar x0 j (by omega)]
    exact residual_norm_le r xStar _ ε hr0 hLip
  have hcausal : ∀ j, j < N →
      ‖traj (extend A) Q rseq (x0-xStar) j‖ ≤ R * hSeq A (L0+ε0) j := by
    intro j hj
    rw [response_eq_error A Q r xStar x0 j (by omega)]
    have he := error_norm_le_hA_of A hStrict Q r xStar x0 L0 ε ε0 R
      hε hε_le hL hR hQ hr0 hLip hR0 j (by omega)
    simp only [hSeq, dif_pos (show j < N+1 by omega)]
    exact he
  rw [← response_eq_error A Q r xStar x0 N (by omega)]
  exact terminal_response_bound
    (traj_eq_pOp_plus_ROp (A:=extend A) (Q:=Q) rseq (x0-xStar) N)
    hres hcausal hROp hε hR hrho
    (fun j => by
      simp only [hSeq]
      split_ifs with hj
      · exact hA_of_nonneg hL ⟨j, hj⟩
      · exact le_rfl)

end ResponseBridge
end NearQuadratic
