module

-- Public increment-rank helpers (partial formalization).
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

namespace MemoryRank.Incremental

def S_k (N k : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (N - k)) (Fin k) ℝ :=
  Matrix.of fun (i : Fin (N - k)) (j : Fin k) =>
    if hk : k ≤ N then
      let row : Fin N := ⟨k + i.val, by omega⟩
      let col : Fin N := ⟨j.val, by omega⟩
      T row col
    else 0

def Q (N m : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < N → (S_k N k T).rank ≤ m

def IsZeroMatrix (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, T i j = 0

theorem S_k_rank_le_height (N k : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    (S_k N k T).rank ≤ N - k := by
  have h := Matrix.rank_le_height (R := ℝ) (A := S_k N k T)
  simpa using h

theorem S_k_rank_le_width (N k : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    (S_k N k T).rank ≤ k := by
  have h := Matrix.rank_le_width (R := ℝ) (A := S_k N k T)
  simpa using h

theorem Q_monotone (N m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) (T : Matrix (Fin N) (Fin N) ℝ) :
    Q N m₁ T → Q N m₂ T := by
  intro hQ k hk1 hk2
  have h := hQ k hk1 hk2
  omega

theorem zero_mem_Q (N m : ℕ) : Q N m (0 : Matrix (Fin N) (Fin N) ℝ) := by
  intro k hk1 hk2
  have : S_k N k (0 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
    ext i j; simp [S_k]
  rw [this]
  simp

theorem S_k_rank_le_min (N k : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    (S_k N k T).rank ≤ min (N - k) k := by
  have h1 := S_k_rank_le_height N k T
  have h2 := S_k_rank_le_width N k T
  omega

theorem Q_zero_rank_zero (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hQ : Q N 0 T) :
    ∀ k : ℕ, 1 ≤ k → k < N → (S_k N k T).rank = 0 := by
  intro k hk1 hk2
  have h := hQ k hk1 hk2
  omega

#print axioms S_k_rank_le_height
#print axioms Q_monotone
#print axioms zero_mem_Q
#print axioms S_k_rank_le_min

end MemoryRank.Incremental
