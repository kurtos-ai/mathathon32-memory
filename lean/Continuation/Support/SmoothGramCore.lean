module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.Basic
/-!
# Checked Gram support lemmas

Coverage: finite-dimensional Gram identities and the PSD factorization
`G = BᵀB`. This is supporting algebra for the smooth-convex exact loss model;
the interpolation theorem and Section 6 minimax results are not claimed here.
-/
@[expose] public section
open Matrix
open scoped MatrixOrder
namespace Continuation.SmoothSupport

noncomputable def nu (N : ℕ) : ℕ := N + 2

-- Gram identity: <Bu, Bv> = uᵀ G v where G = Bᵀ B
theorem gram_identity {n N : ℕ} (B : Matrix (Fin n) (Fin (nu N)) ℝ) (u v : Fin (nu N) → ℝ) :
    let G := Bᵀ * B
    (B *ᵥ u) ⬝ᵥ (B *ᵥ v) = u ⬝ᵥ (G *ᵥ v) := by
  intro G
  have h1 : u ⬝ᵥ ((Bᵀ * B) *ᵥ v) = u ⬝ᵥ (Bᵀ *ᵥ (B *ᵥ v)) := by rw [← mulVec_mulVec]
  have h2 : u ⬝ᵥ (Bᵀ *ᵥ (B *ᵥ v)) = (B *ᵥ v) ⬝ᵥ (B *ᵥ u) := by rw [dotProduct_transpose_mulVec]
  have h3 : (B *ᵥ v) ⬝ᵥ (B *ᵥ u) = (B *ᵥ u) ⬝ᵥ (B *ᵥ v) := by rw [dotProduct_comm]
  calc (B *ᵥ u) ⬝ᵥ (B *ᵥ v) = (B *ᵥ v) ⬝ᵥ (B *ᵥ u) := by rw [dotProduct_comm]
    _ = u ⬝ᵥ (Bᵀ *ᵥ (B *ᵥ v)) := by rw [← h2]
    _ = u ⬝ᵥ ((Bᵀ * B) *ᵥ v) := by rw [h1]
    _ = u ⬝ᵥ (G *ᵥ v) := rfl

theorem gram_norm {n N : ℕ} (B : Matrix (Fin n) (Fin (nu N)) ℝ) (u : Fin (nu N) → ℝ) :
    let G := Bᵀ * B
    (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = u ⬝ᵥ (G *ᵥ u) := by
  intro G
  exact gram_identity B u u

-- PSD factorization: every PSD G has B with G = Bᵀ * B, dim ν
theorem psd_factorization {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℝ) (hG : G.PosSemidef) :
    ∃ B : Matrix n n ℝ, G = Bᵀ * B := by
  let B := CFC.sqrt G
  use B
  have hnn : (0 : Matrix n n ℝ) ≤ G := hG.nonneg
  have hsq : B * B = G := CFC.sqrt_mul_sqrt_self G hnn
  have hB_le : (0 : Matrix n n ℝ) ≤ B := CFC.sqrt_nonneg G
  have hB_psd : B.PosSemidef := by
    rw [Matrix.le_iff] at hB_le
    simpa [sub_zero] using hB_le
  have hH : B.IsHermitian := hB_psd.isHermitian
  have hT : Bᵀ = B := by
    have hconj : Bᴴ = B := hH
    ext i j
    have hj := congrFun (congrFun hconj i) j
    simp only [conjTranspose_apply, star_trivial] at hj
    simp only [transpose_apply]
    exact hj
  rw [hT]
  exact hsq.symm

-- Forward direction: every actual instance gives PSD G
theorem forward_psd {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) : (Bᵀ * B).PosSemidef := by
  have h : Bᴴ = Bᵀ := by ext i j; simp [conjTranspose_apply, transpose_apply, star_trivial]
  rw [← h]
  exact posSemidef_conjTranspose_mul_self B


end Continuation.SmoothSupport
