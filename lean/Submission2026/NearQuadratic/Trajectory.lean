module
/-
Actual perturbed-gradient trajectories for ext:thm:near.  The finite recursion
uses residual evaluations at the trajectory's own query points.  The proof is
by structural strong induction; no zero-residual shortcut is used.
-/
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

namespace NearQuadratic
namespace Trajectory

open Finset BigOperators

variable {N : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Error at states `0,...,N`, frozen after the horizon. -/
noncomputable def error (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V)
    (r : V → V) (xStar x0 : V) : ℕ → V
  | 0 => x0 - xStar
  | n+1 =>
    if h : n < N then
      x0 - xStar + ∑ j : Fin (n+1),
        A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ •
          (Q (error A Q r xStar x0 j.val) +
            r (xStar + error A Q r xStar x0 j.val))
    else error A Q r xStar x0 n

lemma error_zero (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V)
    (r : V → V) (xStar x0 : V) :
    error A Q r xStar x0 0 = x0 - xStar := by simp [error]

lemma error_step (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V)
    (r : V → V) (xStar x0 : V) {n : ℕ} (hn : n < N) :
    error A Q r xStar x0 (n+1) =
      x0 - xStar + ∑ j : Fin (n+1),
        A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ •
          (Q (error A Q r xStar x0 j.val) +
            r (xStar + error A Q r xStar x0 j.val)) := by
  simp [error, hn]

/-- The actual query point corresponding to an error state. -/
noncomputable def point (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V)
    (r : V → V) (xStar x0 : V) (n : ℕ) : V :=
  xStar + error A Q r xStar x0 n

lemma residual_at_point (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V)
    (r : V → V) (xStar x0 : V) (n : ℕ) :
    r (point A Q r xStar x0 n) = r (xStar + error A Q r xStar x0 n) := rfl

/-- Arbitrary finite causal scalar majorant. -/
noncomputable def scalarH (J : Fin (N+1) → Fin (N+1) → ℝ) (b : Fin (N+1) → ℝ) : ℕ → ℝ
  | 0 => b ⟨0, Nat.zero_lt_succ _⟩
  | n+1 =>
    if h : n < N then
      b ⟨n+1, by omega⟩ + ∑ j : Fin (n+1),
        J ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ * scalarH J b j.val
    else scalarH J b n

lemma scalarH_zero (J : Fin (N+1) → Fin (N+1) → ℝ) (b : Fin (N+1) → ℝ) :
    scalarH J b 0 = b ⟨0, Nat.zero_lt_succ _⟩ := by simp [scalarH]

lemma scalarH_step (J : Fin (N+1) → Fin (N+1) → ℝ) (b : Fin (N+1) → ℝ)
    {n : ℕ} (hn : n < N) :
    scalarH J b (n+1) = b ⟨n+1, by omega⟩ + ∑ j : Fin (n+1),
      J ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ * scalarH J b j.val := by
  simp [scalarH, hn]

lemma scalarH_nonneg (J : Fin (N+1) → Fin (N+1) → ℝ) (b : Fin (N+1) → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hb : ∀ i, 0 ≤ b i) :
    ∀ n, n < N+1 → 0 ≤ scalarH J b n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    cases n with
    | zero => rw [scalarH_zero]; exact hb _
    | succ n =>
      have hlt : n < N := by omega
      rw [scalarH_step J b hlt]
      apply add_nonneg (hb _)
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (hJ _ _) (ih j.val (by omega) (by omega))

lemma residual_norm_le (r : V → V) (xStar e : V) (ε : ℝ)
    (hr0 : r xStar = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ ε * ‖x - y‖) :
    ‖r (xStar + e)‖ ≤ ε * ‖e‖ := by
  have h := hLip (xStar + e) xStar
  rw [hr0, sub_zero] at h
  convert h using 1 <;> abel

lemma perturbed_gradient_norm_le (Q : V →L[ℝ] V) (r : V → V)
    (xStar e : V) (L0 ε : ℝ) (hQ : ∀ v, ‖Q v‖ ≤ L0 * ‖v‖)
    (hr0 : r xStar = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ ε * ‖x - y‖) :
    ‖Q e + r (xStar + e)‖ ≤ (L0 + ε) * ‖e‖ := by
  calc
    ‖Q e + r (xStar + e)‖ ≤ ‖Q e‖ + ‖r (xStar + e)‖ := norm_add_le _ _
    _ ≤ L0 * ‖e‖ + ε * ‖e‖ := add_le_add (hQ e) (residual_norm_le r xStar e ε hr0 hLip)
    _ = (L0 + ε) * ‖e‖ := by ring

/-- Uniform causal bound for the actual perturbed-gradient error trajectory.
`hA` is the recursive solution `h=1+(L0+ε0)|A|h` from Appendix K. -/
theorem error_norm_le_scalarH
    (A : Fin (N+1) → Fin (N+1) → ℝ) (Q : V →L[ℝ] V) (r : V → V)
    (xStar x0 : V) (L0 ε ε0 R : ℝ)
    (hε : 0 ≤ ε) (hε_le : ε ≤ ε0) (hL : 0 ≤ L0 + ε0) (hR : 0 ≤ R)
    (hQ : ∀ v, ‖Q v‖ ≤ L0 * ‖v‖)
    (hr0 : r xStar = 0) (hLip : ∀ x y, ‖r x - r y‖ ≤ ε * ‖x - y‖)
    (hR0 : ‖x0 - xStar‖ ≤ R) :
    let H := scalarH (N:=N) (fun i j => (L0+ε0) * |A i j|) (fun _ => 1)
    ∀ n, n < N+1 → ‖error A Q r xStar x0 n‖ ≤ R * H n := by
  dsimp only
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    cases n with
    | zero =>
      rw [error_zero, scalarH_zero]
      have hone : (0:ℝ) ≤ 1 := zero_le_one
      nlinarith
    | succ n =>
      have hlt : n < N := by omega
      let E : ℕ → V := error A Q r xStar x0
      let H : ℕ → ℝ := scalarH (N:=N) (fun i j => (L0+ε0) * |A i j|) (fun _ => 1)
      have hgrad : ∀ j : Fin (n+1),
          ‖Q (E j.val) + r (xStar + E j.val)‖ ≤ (L0+ε0) * ‖E j.val‖ := by
        intro j
        exact (perturbed_gradient_norm_le Q r xStar (E j.val) L0 ε hQ hr0 hLip).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      have hsum : (∑ j : Fin (n+1),
            ‖A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ • (Q (E j.val) + r (xStar + E j.val))‖) ≤
          ∑ j : Fin (n+1), ((L0+ε0) * |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩|) * (R * H j.val) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_eq_abs]
        have hprev : ‖E j.val‖ ≤ R * H j.val := ih j.val (by omega) (by omega)
        calc
          |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩| * ‖Q (E j.val) + r (xStar + E j.val)‖
              ≤ |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩| * ((L0+ε0) * ‖E j.val‖) :=
                mul_le_mul_of_nonneg_left (hgrad j) (abs_nonneg _)
          _ ≤ |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩| * ((L0+ε0) * (R * H j.val)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprev hL)
                  (abs_nonneg _)
          _ = ((L0+ε0) * |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩|) * (R * H j.val) := by ring
      rw [error_step A Q r xStar x0 hlt, scalarH_step _ _ hlt]
      calc
        ‖x0 - xStar + ∑ j : Fin (n+1),
            A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ • (Q (E j.val) + r (xStar + E j.val))‖
            ≤ ‖x0 - xStar‖ + ∑ j : Fin (n+1),
              ‖A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ • (Q (E j.val) + r (xStar + E j.val))‖ := by
                exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
        _ ≤ R + ∑ j : Fin (n+1),
              ((L0+ε0) * |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩|) * (R * H j.val) :=
                add_le_add hR0 hsum
        _ = R + ∑ j : Fin (n+1), R *
              ((L0+ε0) * |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩| * H j.val) := by
                congr 1
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = R * (1 + ∑ j : Fin (n+1),
              (L0+ε0) * |A ⟨n+1, by omega⟩ ⟨j.val, by omega⟩| * H j.val) := by
                rw [mul_add, Finset.mul_sum]
                ring

end Trajectory
end NearQuadratic
