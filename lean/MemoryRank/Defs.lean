module

-- Public structural definitions (partial formalization).
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace MemoryRank

/-
Paper §2: Cut matrix H_k(W) ∈ ℝ^{(N-k+1)×(k+1)} (eq:cut) and
incremental block S_k(T) ∈ ℝ^{(N-k)×k} with memory loci Q_m.
These definitions describe coefficient blocks. The maximum cut rank defined
below is not a definition of operational register memory. The realization
equivalence needs a separate proof with machine semantics.
-/

def H_k (N k : ℕ) (_hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N - k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun (i : Fin (N - k + 1)) (j : Fin (k + 1)) =>
    if j.val = 0 then (1 : ℝ)
    else
      let row : Fin (N+1) := ⟨k + i.val, by omega⟩
      let col : Fin (N+1) := ⟨j.val - 1, by omega⟩
      W row col

def S_k (N k : ℕ) (hk : k ≤ N) (_hk2 : k < N ∨ k = N) (T : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (N - k)) (Fin k) ℝ :=
  Matrix.of fun (i : Fin (N - k)) (j : Fin k) =>
    let row : Fin N := ⟨k + i.val, by omega⟩
    let col : Fin N := ⟨j.val, by omega⟩
    T row col

-- Simplified version for Q definition (handles k=0,N via if)
def S_k' (N k : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (N - k)) (Fin k) ℝ :=
  Matrix.of fun (i : Fin (N - k)) (j : Fin k) =>
    if hk : k ≤ N then
      let row : Fin N := ⟨k + i.val, by omega⟩
      let col : Fin N := ⟨j.val, by omega⟩
      T row col
    else 0

def Q (N m : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < N → (S_k' N k T).rank ≤ m

def IsZeroMatrix (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, T i j = 0

noncomputable def memRank (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : ℕ :=
  Finset.sup (Finset.univ : Finset (Fin (N+1))) fun k =>
    (H_k N k.val (by omega) W).rank

end MemoryRank
