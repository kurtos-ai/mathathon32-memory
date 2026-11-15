module

/-
Mathathon 32 — Quadratic benchmark (WP3)
Paper §5: class eq:quadratic-class, polynomials eq:polynomials,
risk eq:quad-risk, Chebyshev optimum eq:Cheb, Thm thm:quadratic.
Lean v4.35.0 / mathlib v4.35.0.

Formalizes product-polynomial evaluation and normalization, and positivity
of the expression named quadMinimaxValue. It does not prove this expression
is the minimax value, nor prove the Chebyshev schedule or its optimality.
-/
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic

@[expose] public section

open Polynomial
noncomputable section
namespace QuadraticBenchmark

/-- Product polynomial at T=0 (paper eq:product): p_N(λ)=∏(1 + d_i λ).
Degree ≤ N, constant term 1, rank-one memory locus Q_0. -/
def productPoly {N : ℕ} (d : Fin N → ℝ) : ℝ[X] :=
  Finset.prod Finset.univ fun i => (C (1 : ℝ) + C (d i) * X)

theorem productPoly_eval_zero {N : ℕ} (d : Fin N → ℝ) :
    (productPoly d).eval 0 = 1 := by
  unfold productPoly
  -- eval of product is product of evals
  have h1 : ∀ i : Fin N, (C (1 : ℝ) + C (d i) * (X : ℝ[X])).eval (0 : ℝ) = 1 := by
    intro i
    simp [eval_add, eval_mul, eval_C, eval_X]
  simp [eval_prod, h1]

theorem productPoly_eval {N : ℕ} (d : Fin N → ℝ) (lam : ℝ) :
    (productPoly (N := N) d).eval lam =
    Finset.prod Finset.univ (fun i : Fin N => 1 + d i * lam) := by
  unfold productPoly
  simp [eval_prod, eval_add, eval_mul, eval_C, eval_X]

/-- Exact quadratic minimax value (paper eq:quad-values, thm:quadratic):
V = L R² / 2(2N+1)² for every N ≥ 1 and every m ≥ 0.
Upper bound via Chebyshev polynomial C_{2N+1} giving p⋆ with
max_{[0,L]} λ p⋆(λ)² = L/(2N+1)².
Lower bound via Chebyshev alternation (cited literature). -/
def quadMinimaxValue (N : ℕ) (L R : ℝ) : ℝ :=
  L * R ^ 2 / (2 * ((2 * (N : ℝ) + 1) ^ 2))

theorem quadMinimaxValue_pos {N : ℕ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    0 < quadMinimaxValue N L R := by
  unfold quadMinimaxValue
  positivity

/- The spectral risk formula, Chebyshev construction, alternation bound,
and minimax threshold intersections remain written proofs in the report. -/

end QuadraticBenchmark
