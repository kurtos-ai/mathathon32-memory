module
public import Submission2026.NearQuadratic.NearResponse
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section
noncomputable section
namespace NearQuadratic.PolynomialResponse
open Polynomial
open scoped BigOperators

/-- The history-gain polynomial uses the same plus convention as `pOp`. -/
def pPoly (A : ℕ → ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n+1 => 1 + ∑ k : Fin (n+1), C (A (n+1) k.val) * X * pPoly A k.val
termination_by n => n

/-- The polynomial response to a residual injected at query `j`. -/
def rPoly (A : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ[X]
  | 0, _ => 0
  | n+1, j => if j < n+1 then
      C (A (n+1) j) + ∑ k : Fin (n+1), if j < k.val then
        C (A (n+1) k.val) * X * rPoly A k.val j else 0
    else 0
termination_by n _ => n

section Operators
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact operator evaluation of the actual unforced response. -/
theorem pOp_eq_aeval (A : ℕ → ℕ → ℝ) (Q : V →L[ℝ] V) (n : ℕ) :
    pOp A Q n = aeval Q (pPoly A n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => simp [pOp_zero_eq, pPoly, ContinuousLinearMap.one_def]
    | succ n =>
      rw [pOp_succ_eq, pPoly]
      simp only [map_add, map_one, map_sum, map_mul, aeval_C, aeval_X,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        ContinuousLinearMap.one_def, ContinuousLinearMap.mul_def]
      apply congrArg (HAdd.hAdd (ContinuousLinearMap.id ℝ V))
      apply Finset.sum_congr rfl
      intro k _
      rw [ih k.val k.isLt]
      simp only [ContinuousLinearMap.id_comp]

/-- Exact operator evaluation of every causal residual response. -/
theorem ROp_eq_aeval (A : ℕ → ℕ → ℝ) (Q : V →L[ℝ] V)
    (n j : ℕ) (hj : j < n) :
    ROp A Q n j = aeval Q (rPoly A n j) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [ROp_succ_lt A Q n j hj, rPoly, ite_eq_left hj]
      simp only [map_add, map_sum, aeval_C, Algebra.algebraMap_eq_smul_one,
        ContinuousLinearMap.one_def]
      apply congrArg (HAdd.hAdd (A (n+1) j • ContinuousLinearMap.id ℝ V))
      apply Finset.sum_congr rfl
      intro k _
      split_ifs with hkj
      · simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul, ContinuousLinearMap.mul_def]
        rw [ih k.val k.isLt hkj]
      · simp


end Operators

section Spectral
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Polynomial evaluation acts diagonally in an orthonormal eigenbasis. -/
theorem repr_aeval {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (Q : V →L[ℝ] V) (lam : ι → ℝ)
    (hdiag : ∀ v i, b.repr (Q v) i = lam i * b.repr v i)
    (p : ℝ[X]) (v : V) (i : ι) :
    b.repr ((aeval Q p) v) i = p.eval (lam i) * b.repr v i := by
  have hp (n : ℕ) (w : V) : b.repr ((Q ^ n) w) i = lam i ^ n * b.repr w i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, hdiag, ih, pow_succ']
      ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      smul_apply, map_smul, PiLp.smul_apply, smul_eq_mul,
      hp, Polynomial.eval_monomial, mul_assoc]

/-- A scalar bound on all eigenvalues controls the full, unweighted operator norm. -/
theorem norm_aeval_le_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (Q : V →L[ℝ] V) (lam : ι → ℝ)
    (hdiag : ∀ v i, b.repr (Q v) i = lam i * b.repr v i)
    (p : ℝ[X]) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i, |p.eval (lam i)| ≤ B) :
    ‖aeval Q p‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg v))).mp
  rw [← b.repr.norm_map ((aeval Q p) v), EuclideanSpace.real_norm_sq_eq]
  have hv : ‖v‖ ^ 2 = ∑ i, b.repr v i ^ 2 := by
    rw [← b.repr.norm_map v, EuclideanSpace.real_norm_sq_eq]
  rw [mul_pow, hv, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [repr_aeval b Q lam hdiag, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb i)

variable [FiniteDimensional ℝ V]

/-- Positivity and the operator bound put each real eigenvalue in the paper's interval. -/
theorem eigenvalues_mem_Icc (Q : V →L[ℝ] V)
    (hSym : Q.toLinearMap.IsSymmetric) (L : ℝ)
    (hpos : ∀ v, 0 ≤ @inner ℝ V _ (Q v) v)
    (hbound : ∀ v, ‖Q v‖ ≤ L * ‖v‖)
    (i : Fin (Module.finrank ℝ V)) :
    hSym.eigenvalues rfl i ∈ Set.Icc 0 L := by
  let b := hSym.eigenvectorBasis rfl
  have heig : Q (b i) = hSym.eigenvalues rfl i • b i :=
    hSym.apply_eigenvectorBasis rfl i
  have hnorm : ‖b i‖ = 1 := b.norm_eq_one i
  constructor
  · have h := hpos (b i)
    rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm] at h
    simpa using h
  · have h := hbound (b i)
    rw [heig, norm_smul, hnorm, mul_one, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h

/-- The interval maximum gives the unweighted polynomial operator norm bound. -/
theorem norm_aeval_le_pi (Q : V →L[ℝ] V)
    (hSym : Q.toLinearMap.IsSymmetric) (L : ℝ) (hL : 0 ≤ L)
    (hpos : ∀ v, 0 ≤ @inner ℝ V _ (Q v) v)
    (hbound : ∀ v, ‖Q v‖ ≤ L * ‖v‖) (p : ℝ[X]) :
    ‖aeval Q p‖ ≤ pi_of_poly p L := by
  apply norm_aeval_le_of_eigenbasis (hSym.eigenvectorBasis rfl) Q
    (hSym.eigenvalues rfl) (hSym.eigenvectorBasis_apply_self_apply rfl) p
    (pi_of_poly p L) (pi_of_poly_nonneg p L hL)
  intro i
  exact pi_of_poly_is_ub p L hL _ (eigenvalues_mem_Icc Q hSym L hpos hbound i)

/-- Both response estimates needed for the actual nonlinear trajectory are derived. -/
theorem response_estimates (A : ℕ → ℕ → ℝ) (Q : V →L[ℝ] V)
    (hSym : Q.toLinearMap.IsSymmetric) (L : ℝ) (hL : 0 ≤ L)
    (hpos : ∀ v, 0 ≤ @inner ℝ V _ (Q v) v)
    (hbound : ∀ v, ‖Q v‖ ≤ L * ‖v‖) (N : ℕ) (v : V)
    (R : ℝ) (hv : ‖v‖ ≤ R) :
    (∀ j, j < N → ‖ROp A Q N j‖ ≤ pi_of_poly (rPoly A N j) L) ∧
    ‖pOp A Q N v‖ ≤ R * pi_of_poly (pPoly A N) L := by
  constructor
  · intro j hj
    rw [ROp_eq_aeval A Q N j hj]
    exact norm_aeval_le_pi Q hSym L hL hpos hbound _
  · rw [pOp_eq_aeval]
    calc
      ‖(aeval Q (pPoly A N)) v‖ ≤ ‖aeval Q (pPoly A N)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ pi_of_poly (pPoly A N) L * R :=
        mul_le_mul (norm_aeval_le_pi Q hSym L hL hpos hbound _) hv
          (norm_nonneg _) (pi_of_poly_nonneg _ L hL)
      _ = R * pi_of_poly (pPoly A N) L := mul_comm _ _

variable [CompleteSpace V]

/-- The actual finite-dimensional perturbed-gradient trajectory satisfies the explicit
near-quadratic error bound. All spectral response estimates are discharged from
symmetry, positivity and the operator bound in the data. -/
theorem terminal_gap {N : ℕ}
    (A : Fin (N+1) → Fin (N+1) → ℝ) (hStrict : IsStrictLowerTri' A)
    (Q : V →L[ℝ] V) (f : V → ℝ) (r : V → V) (xStar x0 : V)
    (L0 ε ε0 R : ℝ)
    (hData : PerturbedQuadraticData V Q xStar f r L0 ε)
    (hSymm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (hε_le : ε ≤ ε0) (hε0 : 0 ≤ ε0) (hR : 0 ≤ R)
    (hR0 : ‖x0-xStar‖ ≤ R) :
    let πA := pi_of_poly (pPoly (ResponseBridge.extend A) N) L0
    let rho := fun j => pi_of_poly (rPoly (ResponseBridge.extend A) N j) L0
    |f (xStar + Trajectory.error A Q r xStar x0 N) - f xStar -
        quadForm Q (pOp (ResponseBridge.extend A) Q N (x0-xStar))| ≤
      ε * R ^ 2 * kappa_const (hA_of A (L0+ε0) ⟨N, by omega⟩) πA
        (betaCoeff N rho (ResponseBridge.hSeq A (L0+ε0))) L0 ε0 := by
  have hSym : Q.toLinearMap.IsSymmetric := hSymm
  have hs := response_estimates (ResponseBridge.extend A) Q hSym L0 hData.hL0_nonneg
    hData.hQ_nonneg hData.hQ_bound N (x0-xStar) R hR0
  exact ResponseBridge.terminal_gap_of_response_estimates A hStrict Q f r xStar x0
    L0 ε ε0 R (pi_of_poly (pPoly (ResponseBridge.extend A) N) L0)
    (fun j => pi_of_poly (rPoly (ResponseBridge.extend A) N j) L0)
    hData hSymm hε_le hε0 hR (pi_of_poly_nonneg _ _ hData.hL0_nonneg) hR0
    (fun _ => pi_of_poly_nonneg _ _ hData.hL0_nonneg) hs.1 hs.2

end Spectral
end NearQuadratic.PolynomialResponse
