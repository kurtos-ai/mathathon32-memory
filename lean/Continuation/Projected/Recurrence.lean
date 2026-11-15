module
public import Continuation.Support.ProjectedCore
/-! The corrected register readouts stay in K. This does not yet prove equality
with the history-based projected recurrence for general K. -/
@[expose] public section
open InnerProductSpace
namespace Continuation.Projected
open Continuation.ProjectedSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
theorem projStateAux_succ {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (g : Fin N → E) (n : ℕ) (hn : n < N) :
    projStateAux hKconv hKclosed hKne M x0 g (n+1) =
      fun r => (∑ j : Fin s, M.F ⟨n, hn⟩ r j • projStateAux hKconv hKclosed hKne M x0 g n j) + M.b ⟨n, hn⟩ r • g ⟨n, hn⟩
        + M.p ⟨n, hn⟩ r • (piK hKconv hKclosed hKne (weightedSum (M.c ⟨n+1, by omega⟩) (fun r => (∑ j : Fin s, M.F ⟨n, hn⟩ r j • projStateAux hKconv hKclosed hKne M x0 g n j) + M.b ⟨n, hn⟩ r • g ⟨n, hn⟩)) - weightedSum (M.c ⟨n+1, by omega⟩) (fun r => (∑ j : Fin s, M.F ⟨n, hn⟩ r j • projStateAux hKconv hKclosed hKne M x0 g n j) + M.b ⟨n, hn⟩ r • g ⟨n, hn⟩)) := by
  simp [projStateAux, hn]
theorem projQuery_zero {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (g : Fin N → E) :
    projQuery hKconv hKclosed hKne M x0 g ⟨0, by omega⟩ = x0 := by
  unfold projQuery; have : projStateAux hKconv hKclosed hKne M x0 g 0 = initState s x0 := by simp [projStateAux]
  rw [this]; exact weightedSum_initState (M.c ⟨0, by omega⟩) M.c0_e1
theorem projQuery_succ_eq_piK {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (g : Fin N → E) (k : Fin N) :
    projQuery hKconv hKclosed hKne M x0 g ⟨k.val+1, by omega⟩ = piK hKconv hKclosed hKne (weightedSum (M.c ⟨k.val+1, by omega⟩) (fun r => (∑ j : Fin s, M.F k r j • projStateAux hKconv hKclosed hKne M x0 g k.val j) + M.b k r • g k)) := by
  have h1 := projStateAux_succ hKconv hKclosed hKne M x0 g k.val k.isLt
  have h2 : projStateAux hKconv hKclosed hKne M x0 g (k.val+1) = fun r => (∑ j : Fin s, M.F k r j • projStateAux hKconv hKclosed hKne M x0 g k.val j) + M.b k r • g k + M.p k r • (piK hKconv hKclosed hKne (weightedSum (M.c ⟨k.val+1, by omega⟩) (fun r => (∑ j : Fin s, M.F k r j • projStateAux hKconv hKclosed hKne M x0 g k.val j) + M.b k r • g k)) - weightedSum (M.c ⟨k.val+1, by omega⟩) (fun r => (∑ j : Fin s, M.F k r j • projStateAux hKconv hKclosed hKne M x0 g k.val j) + M.b k r • g k)) := h1
  have hcalc : weightedSum (M.c ⟨k.val+1, by omega⟩) (projStateAux hKconv hKclosed hKne M x0 g (k.val+1)) = piK hKconv hKclosed hKne (weightedSum (M.c ⟨k.val+1, by omega⟩) (fun r => (∑ j : Fin s, M.F k r j • projStateAux hKconv hKclosed hKne M x0 g k.val j) + M.b k r • g k)) := by
    rw [h2]; exact correction_algebra hKconv hKclosed hKne M k _
  unfold projQuery; exact hcalc
theorem projQuery_mem_K {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (hx0 : x0 ∈ K) (g : Fin N → E) (n : ℕ) (hn : n ≤ N) :
    projQuery hKconv hKclosed hKne M x0 g ⟨n, by omega⟩ ∈ K := by
  induction n with
  | zero => rw [projQuery_zero hKconv hKclosed hKne M x0 g]; exact hx0
  | succ n ih =>
    have h : n < N := Nat.lt_of_succ_le hn
    have hk := projQuery_succ_eq_piK hKconv hKclosed hKne M x0 g ⟨n, h⟩
    have hEq : (⟨n+1, by omega⟩ : Fin (N+1)) = ⟨(⟨n, h⟩ : Fin N).val + 1, by omega⟩ := by ext; simp
    rw [hEq, hk]; exact piK_mem hKconv hKclosed hKne _

end Continuation.Projected
