module

-- Public cut-rank helpers (partial formalization).
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

namespace MemoryRank.CutRank

def H_k (N k : ℕ) (_hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N - k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun (i : Fin (N - k + 1)) (j : Fin (k + 1)) =>
    if j.val = 0 then (1 : ℝ)
    else
      let row : Fin (N+1) := ⟨k + i.val, by omega⟩
      let col : Fin (N+1) := ⟨j.val - 1, by omega⟩
      W row col

noncomputable def memRank (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : ℕ :=
  Finset.sup (Finset.univ : Finset (Fin (N+1))) fun k =>
    (H_k N k.val (by omega) W).rank

theorem H_k_rank_le_height (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    (H_k N k hk W).rank ≤ N - k + 1 := by
  have h := Matrix.rank_le_height (R := ℝ) (A := H_k N k hk W)
  simpa using h

theorem H_k_rank_le_width (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    (H_k N k hk W).rank ≤ k + 1 := by
  have h := Matrix.rank_le_width (R := ℝ) (A := H_k N k hk W)
  simpa using h

theorem min_dim_le_half (N k : ℕ) (hk : k ≤ N) :
    min (N - k + 1) (k + 1) ≤ 1 + N / 2 := by
  omega

/-- Dimension bound for the maximum cut rank. No register-realization
semantics or equality with the report's s(W) is asserted here. -/
theorem memRank_le (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    memRank N W ≤ 1 + N / 2 := by
  unfold memRank
  apply Finset.sup_le
  intro k _
  have hk : k.val ≤ N := by omega
  have h1 := H_k_rank_le_height N k.val hk W
  have h2 := H_k_rank_le_width N k.val hk W
  have h3 := min_dim_le_half N k.val hk
  omega
#print axioms memRank_le

end MemoryRank.CutRank
