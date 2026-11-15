module
public import Continuation.Projected.Recurrence
@[expose] public section
namespace Continuation.Projected
open Continuation.ProjectedSupport
theorem direct_singleton_a {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F] {a : F} (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : F) (hx0 : x0 = a) (g : Fin N → F) (n : ℕ) :
    directStateAux (K := ({a} : Set F)) (by simp [convex_singleton]) isClosed_singleton ⟨a, rfl⟩ W x0 g n = a := by
  induction n with
  | zero => simp [directStateAux, hx0]
  | succ n ih =>
    simp [directStateAux, ih, piK_singleton]

theorem proj_singleton_a {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F] {a : F} (N s : ℕ) (M : ProjectedMachine ({a} : Set F) N s) (x0 : F) (hx0 : x0 = a) (g : Fin N → F) (n : ℕ) (hn : n ≤ N) :
    projQuery (K := ({a} : Set F)) (by simp [convex_singleton]) isClosed_singleton ⟨a, rfl⟩ M x0 g ⟨n, by omega⟩ = a := by
  induction n with
  | zero =>
    have h0 : projQuery (K := ({a} : Set F)) (by simp [convex_singleton]) isClosed_singleton ⟨a, rfl⟩ M x0 g ⟨0, by omega⟩ = x0 := projQuery_zero _ _ _ M x0 g
    rw [h0, hx0]
  | succ n ih =>
    have hk : n < N := by omega
    have hsucc := projQuery_succ_eq_piK (K := ({a} : Set F)) (by simp [convex_singleton]) isClosed_singleton ⟨a, rfl⟩ M x0 g ⟨n, hk⟩
    have hEq : (⟨n+1, by omega⟩ : Fin (N+1)) = ⟨(⟨n, hk⟩ : Fin N).val + 1, by omega⟩ := by ext; simp
    rw [hEq, hsucc, piK_singleton]

end Continuation.Projected
