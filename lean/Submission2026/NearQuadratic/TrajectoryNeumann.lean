module
public import Submission2026.NearQuadratic.Trajectory
public import Submission2026.NearQuadratic.Neumann

@[expose] public section

namespace NearQuadratic
namespace Trajectory

open Finset BigOperators

variable {N : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The recursively defined trajectory majorant is exactly the finite Neumann
constant `h_A` used in Appendix K. -/
theorem scalarH_eq_hA_of (A : Fin (N+1) → Fin (N+1) → ℝ) (L : ℝ)
    (hA : IsStrictLowerTri' A) :
    ∀ n, ∀ hn : n < N+1,
      scalarH (N:=N) (fun i j => L * |A i j|) (fun _ => 1) n =
        hA_of A L ⟨n, by omega⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    cases n with
    | zero =>
      rw [scalarH_zero, hA_of_eq_causal_recurrence A L hA ⟨0, by omega⟩]
      simp
    | succ n =>
      have hlt : n < N := by omega
      rw [scalarH_step _ _ hlt,
        hA_of_eq_causal_recurrence A L hA ⟨n+1, by omega⟩]
      apply congrArg (HAdd.hAdd 1)
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j.val (by omega) (by omega)]

/-- Every actual error state, including the terminal state, is bounded by the
source's finite Neumann constant. -/
theorem error_norm_le_hA_of
    (A : Fin (N+1) → Fin (N+1) → ℝ) (hStrict : IsStrictLowerTri' A)
    (Q : V →L[ℝ] V) (r : V → V) (xStar x0 : V) (L0 ε ε0 R : ℝ)
    (hε : 0 ≤ ε) (hε_le : ε ≤ ε0) (hL : 0 ≤ L0 + ε0) (hR : 0 ≤ R)
    (hQ : ∀ v, ‖Q v‖ ≤ L0 * ‖v‖)
    (hr0 : r xStar = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ ε * ‖x - y‖)
    (hR0 : ‖x0 - xStar‖ ≤ R) (n : ℕ) (hn : n < N+1) :
    ‖error A Q r xStar x0 n‖ ≤ R * hA_of A (L0+ε0) ⟨n, by omega⟩ := by
  rw [← scalarH_eq_hA_of A (L0+ε0) hStrict n hn]
  exact error_norm_le_scalarH A Q r xStar x0 L0 ε ε0 R
    hε hε_le hL hR hQ hr0 hLip hR0 n hn

/-- Source-terminal specialization at `x_N`. -/
theorem terminal_error_norm_le_hA_of
    (A : Fin (N+1) → Fin (N+1) → ℝ) (hStrict : IsStrictLowerTri' A)
    (Q : V →L[ℝ] V) (r : V → V) (xStar x0 : V) (L0 ε ε0 R : ℝ)
    (hε : 0 ≤ ε) (hε_le : ε ≤ ε0) (hL : 0 ≤ L0 + ε0) (hR : 0 ≤ R)
    (hQ : ∀ v, ‖Q v‖ ≤ L0 * ‖v‖)
    (hr0 : r xStar = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ ε * ‖x - y‖)
    (hR0 : ‖x0 - xStar‖ ≤ R) :
    ‖error A Q r xStar x0 N‖ ≤ R * hA_of A (L0+ε0) ⟨N, by omega⟩ :=
  error_norm_le_hA_of A hStrict Q r xStar x0 L0 ε ε0 R
    hε hε_le hL hR hQ hr0 hLip hR0 N (by omega)

end Trajectory
end NearQuadratic

namespace NearQuadratic
namespace Trajectory

/-- Generic form of `scalarH_eq_hA_of`, independent of the absolute-matrix
majorant used for near-quadratic trajectories. -/
theorem scalarH_eq_neumannSum' {J : Fin (N+1) → Fin (N+1) → ℝ}
    (hJ : IsStrictLowerTri' J) (b : Fin (N+1) → ℝ) :
    ∀ n, ∀ hn : n < N+1,
      scalarH J b n = neumannSum' J b ⟨n, by omega⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    cases n with
    | zero =>
      rw [scalarH_zero, neumannSum'_eq_causal_recurrence hJ b ⟨0, by omega⟩]
      simp
    | succ n =>
      have hlt : n < N := by omega
      rw [scalarH_step _ _ hlt,
        neumannSum'_eq_causal_recurrence hJ b ⟨n+1, by omega⟩]
      apply congrArg (HAdd.hAdd (b ⟨n+1, by omega⟩))
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j.val (by omega) (by omega)]

/-- A causal scalar comparison bound against the explicit recursive majorant. -/
theorem le_scalarH_of_causal {J : Fin (N+1) → Fin (N+1) → ℝ} {d b : Fin (N+1) → ℝ}
    (hJ : ∀ i j, 0 ≤ J i j)
    (hd : ∀ i : Fin (N+1), d i ≤ b i + ∑ j : Fin i.val,
      J i ⟨j.val, by omega⟩ * d ⟨j.val, by omega⟩) :
    ∀ n, ∀ hn : n < N+1,
      d ⟨n, by omega⟩ ≤ scalarH J b n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    cases n with
    | zero =>
      rw [scalarH_zero]
      simpa using hd ⟨0, by omega⟩
    | succ n =>
      have hlt : n < N := by omega
      rw [scalarH_step _ _ hlt]
      apply (hd ⟨n+1, by omega⟩).trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (ih j.val j.isLt (by omega)) (hJ _ _ )

/-- Causal scalar comparison against the actual finite Neumann sum. -/
theorem le_neumannSum'_of_causal {J : Fin (N+1) → Fin (N+1) → ℝ} {d b : Fin (N+1) → ℝ}
    (hStrict : IsStrictLowerTri' J) (hJ : ∀ i j, 0 ≤ J i j)
    (hd : ∀ i : Fin (N+1), d i ≤ b i + ∑ j : Fin i.val,
      J i ⟨j.val, by omega⟩ * d ⟨j.val, by omega⟩)
    (n : ℕ) (hn : n < N+1) :
    d ⟨n, by omega⟩ ≤ neumannSum' J b ⟨n, by omega⟩ := by
  rw [← scalarH_eq_neumannSum' hStrict b n hn]
  exact le_scalarH_of_causal hJ hd n hn

end Trajectory
end NearQuadratic
