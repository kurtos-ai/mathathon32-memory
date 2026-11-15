module
public import Continuation.Quadratic.MatrixResidual
public import Mathlib.Algebra.Polynomial.Roots
@[expose] public section
noncomputable section
namespace ResidualRigidity
open Polynomial Matrix

/-- The root-diagonal part of pointwise rigidity: a normalized residual of degree at most N
is determined by its values at N distinct nonzero roots of a competing residual. -/
theorem eq_of_normalized_root_values (N : ℕ) (p q : ℝ[X])
    (hp : p.eval 0 = 1) (hq : q.eval 0 = 1)
    (hdp : p.natDegree ≤ N) (hdq : q.natDegree ≤ N)
    (r : Fin N → ℝ) (hr : Function.Injective r) (hr0 : ∀ i, r i ≠ 0)
    (hpr : ∀ i, p.eval (r i) = 0) (hqr : ∀ i, q.eval (r i) = 0) : p = q := by
  let nodes : Option (Fin N) → ℝ := fun i => match i with
    | none => 0
    | some j => r j
  have hinj : Function.Injective nodes := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim ((hr0 j) hij.symm)
    | some i =>
      cases j with
      | none => exact False.elim ((hr0 i) hij)
      | some j => exact congrArg some (hr hij)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q hinj
  · intro i
    cases i with
    | none => exact hp.trans hq.symm
    | some i => exact (hpr i).trans (hqr i).symm
  · simp only [Fintype.card_option,Fintype.card_fin]
    omega

/-- Scalar positive-curvature quadratic loss domination at the distinct roots forces
terminal-polynomial equality. This does not assert equality of the intermediate query maps. -/
theorem eq_of_positive_roots_of_energy_domination (N : ℕ) (p q : ℝ[X])
    (hp : p.eval 0 = 1) (hq : q.eval 0 = 1)
    (hdp : p.natDegree ≤ N) (hdq : q.natDegree ≤ N)
    (r : Fin N → ℝ) (hr : Function.Injective r) (hrpos : ∀ i, 0 < r i)
    (hpr : ∀ i, p.eval (r i) = 0)
    (hdom : ∀ i, r i * (q.eval (r i))^2 ≤ r i * (p.eval (r i))^2) : p = q := by
  apply eq_of_normalized_root_values N p q hp hq hdp hdq r hr
    (fun i => ne_of_gt (hrpos i)) hpr
  intro i
  have he : r i * (q.eval (r i))^2 ≤ 0 := by simpa only [hpr i,zero_pow (by norm_num : 2 ≠ 0),mul_zero] using hdom i
  have hs : (q.eval (r i))^2 ≤ 0 := by
    apply le_of_not_gt
    intro h
    exact (not_lt_of_ge he) (mul_pos (hrpos i) h)
  nlinarith [sq_nonneg (q.eval (r i))]

/-- Two predetermined schedules satisfying the scalar quadratic domination test have
identical terminal residual polynomials, even if the second uses fewer calls. -/
theorem residual_eq_of_scalar_quadratic_domination (N M : ℕ) (hMN : M ≤ N)
    (dA : Fin N → ℝ) (TA : Matrix (Fin N) (Fin N) ℝ)
    (dB : Fin M → ℝ) (TB : Matrix (Fin M) (Fin M) ℝ)
    (r : Fin N → ℝ) (hr : Function.Injective r) (hrpos : ∀ i, 0 < r i)
    (hroot : ∀ i, (QuadraticFoundations.pIter N dA TA N).eval (r i) = 0)
    (hdom : ∀ i, r i * ((QuadraticFoundations.pIter M dB TB M).eval (r i))^2 ≤
      r i * ((QuadraticFoundations.pIter N dA TA N).eval (r i))^2) :
    QuadraticFoundations.pIter N dA TA N = QuadraticFoundations.pIter M dB TB M := by
  apply eq_of_positive_roots_of_energy_domination N _ _
    (QuadraticFoundations.pIter_eval_zero N dA TA N le_rfl)
    (QuadraticFoundations.pIter_eval_zero M dB TB M le_rfl)
    (QuadraticFoundations.pIter_natDegree_le N dA TA N le_rfl)
    ((QuadraticFoundations.pIter_natDegree_le M dB TB M le_rfl).trans hMN)
    r hr hrpos hroot hdom

/-- Consequently the two schedules agree on terminal points of all matrix quadratics.
Full smooth-function rigidity still requires identification of intermediate query rows. -/
theorem terminal_eq_of_scalar_quadratic_domination (N M : ℕ) (hMN : M ≤ N)
    (dA : Fin N → ℝ) (TA : Matrix (Fin N) (Fin N) ℝ)
    (dB : Fin M → ℝ) (TB : Matrix (Fin M) (Fin M) ℝ)
    (r : Fin N → ℝ) (hr : Function.Injective r) (hrpos : ∀ i, 0 < r i)
    (hroot : ∀ i, (QuadraticFoundations.pIter N dA TA N).eval (r i) = 0)
    (hdom : ∀ i, r i * ((QuadraticFoundations.pIter M dB TB M).eval (r i))^2 ≤
      r i * ((QuadraticFoundations.pIter N dA TA N).eval (r i))^2)
    {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) :
    QuadraticResidual.errorIter N dA TA Q e N = QuadraticResidual.errorIter M dB TB Q e M := by
  rw [QuadraticResidual.errorIter_eq_polynomial N dA TA Q e N le_rfl,
    QuadraticResidual.errorIter_eq_polynomial M dB TB Q e M le_rfl,
    residual_eq_of_scalar_quadratic_domination N M hMN dA TA dB TB r hr hrpos hroot hdom]

end ResidualRigidity
