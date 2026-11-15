module
public import Submission2026.QuadraticReplacement.PolynomialDomination
public import Continuation.Quadratic.SpectralRisk
@[expose] public section
noncomputable section
namespace QuadraticReplacement
open Matrix Polynomial
open scoped MatrixOrder

lemma polynomial_energy_identity {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsHermitian) (p : ℝ[X]) (e : Fin n → ℝ) :
    (aeval Q p *ᵥ e) ⬝ᵥ (Q *ᵥ (aeval Q p *ᵥ e)) =
      e ⬝ᵥ (aeval Q (p*X*p) *ᵥ e) := by
  have hpSelf : IsSelfAdjoint (aeval Q p) := by
    rw [← cfc_polynomial p Q (show IsSelfAdjoint Q from hQ)]
    exact cfc_predicate p.eval Q
  have hp : (aeval Q p).IsHermitian := hpSelf
  simp only [map_mul,aeval_X,← mulVec_mulVec]
  have h := hp.star_dotProduct_mulVec_comm e (Q *ᵥ (aeval Q p *ᵥ e))
  simpa only [star_trivial,dotProduct_comm] using h.symm

/-- Scalar residual domination transfers to every actual positive semidefinite quadratic,
with the same initial vector and matrix, rather than just to worst-case suprema. -/
theorem polynomial_energy_mono {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosSemidef) (p q : ℝ[X])
    (hdom : ∀ x : ℝ,|q.eval x| ≤ |p.eval x|) (e : Fin n → ℝ) :
    (aeval Q q *ᵥ e) ⬝ᵥ (Q *ᵥ (aeval Q q *ᵥ e)) ≤
      (aeval Q p *ᵥ e) ⬝ᵥ (Q *ᵥ (aeval Q p *ᵥ e)) := by
  have hself : IsSelfAdjoint Q := hQ.isHermitian
  have hspec : ∀ x ∈ spectrum ℝ Q,0 ≤ x :=
    (posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hQ).2
  have hle : cfc (q*X*q).eval Q ≤ cfc (p*X*p).eval Q := by
    apply cfc_mono (hf:=by fun_prop) (hg:=by fun_prop)
    intro x hx
    have hs : (q.eval x)^2 ≤ (p.eval x)^2 := (sq_le_sq).mpr (hdom x)
    have h := mul_le_mul_of_nonneg_left hs (hspec x hx)
    simpa only [eval_mul,eval_X,pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  rw [cfc_polynomial (q*X*q) Q hself,cfc_polynomial (p*X*p) Q hself] at hle
  have hpsd := Matrix.le_iff.mp hle
  have h := hpsd.dotProduct_mulVec_nonneg e
  rw [polynomial_energy_identity Q hQ.isHermitian q e,
    polynomial_energy_identity Q hQ.isHermitian p e]
  simpa only [sub_mulVec,star_trivial,dotProduct_sub,sub_nonneg] using h

/-- Every predetermined history method has an actual one-register replacement whose
terminal objective error is no larger on each convex quadratic instance. -/
theorem exists_one_register_pointwise_replacement (N : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) :
    ∃ d' : Fin N → ℝ,
      RegisterMachine.HasVectorRealization N (RealizationCore.W_of N d' 0) 1 ∧
      ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ),Q.PosSemidef → ∀ e : Fin n → ℝ,
        (QuadraticResidual.errorIter N d' 0 Q e N) ⬝ᵥ
          (Q *ᵥ QuadraticResidual.errorIter N d' 0 Q e N) / 2 ≤
        (QuadraticResidual.errorIter N d T.val Q e N) ⬝ᵥ
          (Q *ᵥ QuadraticResidual.errorIter N d T.val Q e N) / 2 := by
  let p := QuadraticFoundations.pIter N d T.val N
  obtain ⟨d',hdom⟩ := exists_productPoly_dominated N p
    (QuadraticFoundations.pIter_eval_zero N d T.val N le_rfl)
    (QuadraticFoundations.pIter_natDegree_le N d T.val N le_rfl)
  refine ⟨d',?_,?_⟩
  · apply (RegisterMachine.hasVectorRealization_iff_scalar N _ 1).mpr
    exact (RealizationCore.realization_iff_coordinates N 0 d' ⟨0,by intros; rfl⟩).mpr
      (MemoryRank.Incremental.zero_mem_Q N 0)
  · intro n Q hQ e
    rw [QuadraticResidual.errorIter_eq_polynomial N d' 0 Q e N le_rfl,
      QuadraticResidual.errorIter_eq_polynomial N d T.val Q e N le_rfl,
      QuadraticFoundations.pIter_T_zero_eq_product N d' N le_rfl]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact polynomial_energy_mono Q hQ p (QuadraticFoundations.productPoly d') hdom e

/-- The paper's two-call block implements an arbitrary normalized quadratic factor. -/
theorem quadratic_two_call_identity {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (b c : ℝ) :
    let g := Q *ᵥ x
    let y := x+g
    y+(b-c-1) • g+c • (Q *ᵥ y) =
      x+b • (Q *ᵥ x)+c • (Q *ᵥ (Q *ᵥ x)) := by
  dsimp
  rw [mulVec_add,smul_add]
  module

end QuadraticReplacement
