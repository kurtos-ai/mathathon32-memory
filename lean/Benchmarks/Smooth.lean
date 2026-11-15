module

/-
Smooth convex helpers (partial formalization).

This module proves the scalar theta recurrence/positivity and a generic rank
bound for a strictly lower-triangular outer-product matrix. It does not define
an OGM coefficient map, prove that the OGM map has the factored form, or prove
any plateau/separation/minimax theorem.
-/
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace SmoothBenchmark

-- ------------------------------------------------------------------
-- 1. Theta recurrence  (paper eq:theta)
-- ------------------------------------------------------------------

/-- Theta sequence from paper eq:theta for fixed N:
θ₀=1, θ_k=(1+√(1+4θ²_{k-1}))/2 for 1≤k<N,
θ_N=(1+√(1+8θ²_{N-1}))/2.
We define it as a recursive function on Fin (N+1). -/
def theta : ℕ → ℕ → ℝ
  | _, 0 => 1
  | N, (k+1) =>
    if k + 1 < N then (1 + Real.sqrt (1 + 4 * theta N k ^ 2)) / 2
    else if k + 1 = N then (1 + Real.sqrt (1 + 8 * theta N k ^ 2)) / 2
    else 0  -- unreachable for k+1 ≤ N

theorem theta_zero (N : ℕ) : theta N 0 = 1 := by simp [theta]

theorem theta_pos (N k : ℕ) (hk : k ≤ N) : 0 < theta N k := by
  induction k with
  | zero => simp [theta]
  | succ k ih =>
    have hk' : k ≤ N := by omega
    have ih_pos := ih hk'
    simp only [theta]
    split
    · positivity
    · split
      · positivity
      · omega

theorem theta_ge_one (N k : ℕ) (hk : k ≤ N) : 1 ≤ theta N k := by
  induction k with
  | zero => simp [theta]
  | succ k ih =>
    have hk' : k ≤ N := by omega
    have ih1 := ih hk'
    have _hpos := theta_pos N k hk'
    simp only [theta]
    split
    · -- standard step: θ_{k+1} = (1 + √(1+4θ_k²))/2 ≥ (1+1)/2 =1
      have h1 : 1 ≤ Real.sqrt (1 + 4 * theta N k ^ 2) := by
        have : 1 ≤ 1 + 4 * theta N k ^ 2 := by nlinarith
        calc 1 = Real.sqrt 1 := by simp
          _ ≤ Real.sqrt (1 + 4 * theta N k ^ 2) := Real.sqrt_le_sqrt this
      linarith
    · split
      · -- final step: θ_N = (1+√(1+8θ²_{N-1}))/2 ≥ 1
        have h1 : 1 ≤ Real.sqrt (1 + 8 * theta N k ^ 2) := by
          have : 1 ≤ 1 + 8 * theta N k ^ 2 := by nlinarith
          calc 1 = Real.sqrt 1 := by simp
            _ ≤ Real.sqrt (1 + 8 * theta N k ^ 2) := Real.sqrt_le_sqrt this
        linarith
      · omega

-- The recurrence relations themselves (characterizing equations)
theorem theta_recurrence_standard (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    theta N k = (1 + Real.sqrt (1 + 4 * theta N (k - 1) ^ 2)) / 2 := by
  have hk_eq : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk_eq]
  simp only [theta, show k - 1 + 1 < N from by omega, ↓reduceIte,
             show ¬ (k - 1 + 1 = N) from by omega]

theorem theta_recurrence_final (N : ℕ) (hN : 1 ≤ N) :
    theta N N = (1 + Real.sqrt (1 + 8 * theta N (N - 1) ^ 2)) / 2 := by
  have : N = (N - 1) + 1 := by omega
  conv_lhs => rw [this]
  simp only [theta]
  have h1 : ¬ (N - 1 + 1 < N) := by omega
  have h2 : N - 1 + 1 = N := by omega
  simp [h1, h2]

-- ------------------------------------------------------------------
-- 2. Smooth minimax value  (paper eq:smooth-value)
-- ------------------------------------------------------------------

/-- Minimax value for smooth convex class (paper eq:smooth-value):
c_N = L R² / 2 θ_N², where θ_N is the final theta value.
This is the unrestricted optimum V_lin = V_m for m ≥ 1 (plateau). -/
def smoothMinimaxValue (N : ℕ) (L R : ℝ) : ℝ :=
  L * R ^ 2 / (2 * theta N N ^ 2)

theorem smoothMinimaxValue_pos {N : ℕ} {L R : ℝ}
    (hL : 0 < L) (hR : 0 < R) :
    0 < smoothMinimaxValue N L R := by
  unfold smoothMinimaxValue
  have hθ : 0 < theta N N := theta_pos N N le_rfl
  positivity

theorem smoothMinimaxValue_eq (N : ℕ) (L R : ℝ) :
    smoothMinimaxValue N L R = L * R ^ 2 / (2 * theta N N ^ 2) := by simp [smoothMinimaxValue]

-- ------------------------------------------------------------------
-- 3. OGM construction and memory  (paper eq:OGM-state, Prop prop:OGM-memory)
-- ------------------------------------------------------------------

/-- OGM increment matrix structure: for the OGM method defined by
recurrence eq:OGM-state, each S_k(T_OGM) has rank ≤ 1.
We prove this abstractly: T_OGM = u vᵀ with a cut-off for j ≥ i
(OGM's T is rank-1 factored restricted to strictly lower triangular);
its bottom-left blocks S_k inherit rank ≤ 1.

The explicit coefficient verification (d_O, T_O values, eq:OGM-increment
with T_{10} = -(1-1/θ_1)/Lθ_2 ≠ 0 for N≥2) is checked computationally
in computations/ogm_checks.py; here we state the rank property. -/

-- Helper: factored rank-1 strictly lower triangular matrix
def factoredT (N : ℕ) (u v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => if j.val < i.val then u i * v j else 0

theorem factoredT_rank_one_block (N : ℕ) (u v : Fin N → ℝ) (k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    ∃ w : Fin (N - k) → ℝ, ∃ z : Fin k → ℝ,
      (Matrix.of fun (i : Fin (N - k)) (j : Fin k) =>
        factoredT N u v ⟨k + i.val, by omega⟩ ⟨j.val, by omega⟩) =
      Matrix.of fun i j => w i * z j := by
  refine ⟨fun i => u ⟨k + i.val, by omega⟩, fun j => v ⟨j.val, by omega⟩, ?_⟩
  ext i j
  simp only [factoredT, Matrix.of_apply]
  have hj_lt : j.val < k := j.isLt
  have hi_lt : (k + i.val : ℕ) < N := by omega
  -- j.val < k ≤ k + i.val = (factored row index), so j < i condition holds in factoredT
  have : j.val < k + i.val := by omega
  simp [this]

/-- Every cut block of a generic strictly lower-triangular outer-product
matrix has rank at most one. No identification with the actual OGM increment
matrix is asserted by this theorem. -/
theorem factoredT_rank_le_one (N : ℕ) (hN : 1 ≤ N)
    (u v : Fin N → ℝ) (k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    (Matrix.of fun (i : Fin (N - k)) (j : Fin k) =>
      factoredT N u v ⟨k + i.val, by omega⟩ ⟨j.val, by omega⟩).rank ≤ 1 := by
  obtain ⟨w, z, hwz⟩ := factoredT_rank_one_block N u v k hk hkN
  rw [hwz]
  -- Rank of outer product w zᵀ is ≤ 1
  have : (Matrix.of fun i j => w i * z j) = Matrix.vecMulVec w z := by
    ext i j; simp [Matrix.vecMulVec_apply]
  rw [this]
  -- vecMulVec has rank at most 1 by Matrix.rank_vecMulVec_le_one
  have h := Matrix.rank_vecMulVec_le (R := ℝ) w z
  omega

/-
Remaining report results (not formalized): the OGM recurrence and coefficient
map, its rank calculation and nonzero increment entry, the exact finite loss
model, plateau theorem, GJP-based separation, and least sufficient budget.

-/

end SmoothBenchmark
