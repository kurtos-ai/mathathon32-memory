module
public import Mathlib
public import RealizationCore.BlockRank
@[expose] public section
noncomputable section
namespace RealizationCore

open Matrix

-- Helper lemmas for Fin bounds
theorem k_add_i_lt_N {k N i : ℕ} (hk : k ≤ N) (hi : i < N - k) : k + i < N := by
  have h1 : k + (N - k) = N := Nat.add_sub_cancel' hk
  have h2 : k + i < k + (N - k) := Nat.add_lt_add_left hi k
  exact h2.trans_eq h1

theorem k_add_i_lt_Succ {k N i : ℕ} (hk : k ≤ N) (hi : i < N - k + 1) : k + i < N + 1 := by omega

def H_k (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N - k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun (i : Fin (N - k + 1)) (j : Fin (k + 1)) =>
    if j.val = 0 then (1 : ℝ)
    else
      W ⟨k + i.val, k_add_i_lt_Succ hk i.isLt⟩
        ⟨j.val - 1, by have hj := j.isLt; omega⟩

def T_of (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun (i : Fin N) (j : Fin N) =>
    if h : j.val < i.val then
      W ⟨i.val + 1, by have hi := i.isLt; omega⟩ ⟨j.val, by have hj := j.isLt; omega⟩
        - W ⟨i.val, by have hi := i.isLt; omega⟩ ⟨j.val, by have hj := j.isLt; omega⟩
    else 0

def S_k_of (N k : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N - k)) (Fin k) ℝ :=
  Matrix.of fun (i : Fin (N - k)) (j : Fin k) =>
    if hk : k ≤ N then
      (T_of N W) ⟨k + i.val, k_add_i_lt_N hk i.isLt⟩ ⟨j.val, by have hj := j.isLt; omega⟩
    else 0

def M_k (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N - k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun (i : Fin (N - k + 1)) (j : Fin (k + 1)) =>
    if h0 : i.val = 0 then
      H_k N k hk W ⟨0, Nat.zero_lt_succ (N - k)⟩ j
    else
      H_k N k hk W i j - H_k N k hk W ⟨i.val - 1, by have hi := i.isLt; omega⟩ j

-- Already proved: row operation preserves rank
theorem M_row_mem_span_H (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (i : Fin (N - k + 1)) :
    (M_k N k hk W).row i ∈ Submodule.span ℝ (Set.range (H_k N k hk W).row) := by
  by_cases hi : i.val = 0
  · have hi0 : i = ⟨0, Nat.zero_lt_succ (N - k)⟩ := Fin.ext hi
    rw [hi0]
    have h : (M_k N k hk W).row ⟨0, Nat.zero_lt_succ (N - k)⟩ = (H_k N k hk W).row ⟨0, Nat.zero_lt_succ (N - k)⟩ := by ext j; simp [M_k, Matrix.of_apply, hi]
    rw [h]; exact Submodule.subset_span ⟨⟨0, Nat.zero_lt_succ (N - k)⟩, rfl⟩
  · have hM : (M_k N k hk W).row i = (H_k N k hk W).row i - (H_k N k hk W).row ⟨i.val - 1, by have hi := i.isLt; omega⟩ := by ext j; simp only [Matrix.row_apply, Pi.sub_apply, M_k, Matrix.of_apply, hi, dite_false]
    rw [hM]; exact Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨⟨i.val - 1, by have hi := i.isLt; omega⟩, rfl⟩)

theorem H_row_mem_span_M_aux (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (n : ℕ) (hn : n < N - k + 1) :
    (H_k N k hk W).row ⟨n, hn⟩ ∈ Submodule.span ℝ (Set.range (M_k N k hk W).row) := by
  induction n with
  | zero =>
    have h : (H_k N k hk W).row ⟨0, hn⟩ = (M_k N k hk W).row ⟨0, Nat.zero_lt_succ (N - k)⟩ := by ext j; simp [M_k, Matrix.of_apply]
    rw [h]
    exact Submodule.subset_span ⟨⟨0, Nat.zero_lt_succ (N - k)⟩, rfl⟩
  | succ m ih =>
    have hm : m < N - k + 1 := by omega
    have ih' := ih hm
    have hM : (M_k N k hk W).row ⟨m + 1, hn⟩ = (H_k N k hk W).row ⟨m + 1, hn⟩ - (H_k N k hk W).row ⟨m, hm⟩ := by ext j; simp only [Matrix.row_apply, Pi.sub_apply, M_k, Matrix.of_apply, show (m + 1 : ℕ) ≠ 0 by omega, dite_false]; have heq : (⟨m + 1 - 1, by omega⟩ : Fin (N - k + 1)) = ⟨m, hm⟩ := Fin.ext (by simp); rw [heq]
    have hH : (H_k N k hk W).row ⟨m + 1, hn⟩ = (M_k N k hk W).row ⟨m + 1, hn⟩ + (H_k N k hk W).row ⟨m, hm⟩ := by rw [hM]; abel
    rw [hH]; exact Submodule.add_mem _ (Submodule.subset_span ⟨⟨m + 1, hn⟩, rfl⟩) ih'

theorem H_row_mem_span_M (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Fin (N - k + 1)) : (H_k N k hk W).row i ∈ Submodule.span ℝ (Set.range (M_k N k hk W).row) := H_row_mem_span_M_aux N k hk W i.val i.isLt

theorem rank_H_eq_rank_M (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : (H_k N k hk W).rank = (M_k N k hk W).rank := by
  have h : Submodule.span ℝ (Set.range (H_k N k hk W).row) = Submodule.span ℝ (Set.range (M_k N k hk W).row) := le_antisymm (Submodule.span_le.mpr fun x hx => by obtain ⟨i, rfl⟩ := hx; exact H_row_mem_span_M N k hk W i) (Submodule.span_le.mpr fun x hx => by obtain ⟨i, rfl⟩ := hx; exact M_row_mem_span_H N k hk W i)
  rw [rank_eq_finrank_span_row, rank_eq_finrank_span_row, h]


 theorem M_eq_upperBlock (N k : ℕ) (hk : k ≤ N)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    M_k N k hk W = MemoryBlock.upperBlock (S_k_of N k W)
      (fun j => W ⟨k, by omega⟩ ⟨j.val, by omega⟩) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · simp [M_k, H_k, MemoryBlock.upperBlock]
  · simp [M_k, H_k, MemoryBlock.upperBlock]
  · simp [M_k, H_k, MemoryBlock.upperBlock]
  · rename_i i j
    have hj : j.val < k + i.val := by omega
    simp [M_k, H_k, MemoryBlock.upperBlock, S_k_of, T_of, hk, hj,
      Nat.add_assoc]

 theorem rank_H_eq_one_add_rank_S (N k : ℕ) (hk : k ≤ N)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    (H_k N k hk W).rank = 1 + (S_k_of N k W).rank := by
  rw [rank_H_eq_rank_M, M_eq_upperBlock, MemoryBlock.upperBlock_rank]

#print axioms rank_H_eq_one_add_rank_S
end RealizationCore
