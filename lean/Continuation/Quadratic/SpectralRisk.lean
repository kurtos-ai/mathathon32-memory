module
public import Continuation.Quadratic.MatrixResidual
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
@[expose] public section
noncomputable section
namespace QuadraticSpectral
open Matrix Polynomial
open scoped MatrixOrder

/-- A scalar bound for λ p(λ)^2 bounds every admissible matrix quadratic loss. -/
theorem polynomial_energy_bound {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosSemidef) (L B : ℝ)
    (hL : (L • (1 : Matrix (Fin n) (Fin n) ℝ) - Q).PosSemidef)
    (p : ℝ[X]) (hb : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 ≤ B)
    (e : Fin n → ℝ) :
    let v := (aeval Q p) *ᵥ e
    v ⬝ᵥ (Q *ᵥ v) ≤ B * (e ⬝ᵥ e) := by
  let r : ℝ[X] := p * X * p
  have hself : IsSelfAdjoint Q := hQ.isHermitian
  have hlo : ∀ x ∈ spectrum ℝ Q, 0 ≤ x := by
    exact (posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hQ).2
  have hhi : ∀ x ∈ spectrum ℝ Q, x ≤ L := by
    apply (le_algebraMap_iff_spectrum_le hself).mp
    simpa only [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] using hL
  have hr : cfc r.eval Q ≤ algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) B := by
    apply (cfc_le_algebraMap_iff r.eval B Q (by fun_prop) hself).mpr
    intro x hx
    have h := hb x ⟨hlo x hx,hhi x hx⟩
    simpa only [r, eval_mul, eval_X, pow_two, mul_assoc, mul_comm, mul_left_comm] using h
  rw [cfc_polynomial r Q hself] at hr
  have hpsd := Matrix.le_iff.mp hr
  have hval := hpsd.dotProduct_mulVec_nonneg e
  have hpSelf : IsSelfAdjoint (aeval Q p) := by
    rw [← cfc_polynomial p Q hself]
    exact cfc_predicate p.eval Q
  have hp : (aeval Q p).IsHermitian := hpSelf
  have hid : (aeval Q p *ᵥ e) ⬝ᵥ (Q *ᵥ (aeval Q p *ᵥ e)) =
      e ⬝ᵥ ((aeval Q r) *ᵥ e) := by
    simp only [r, map_mul, aeval_X, ← mulVec_mulVec]
    have h := hp.star_dotProduct_mulVec_comm e (Q *ᵥ (aeval Q p *ᵥ e))
    simpa only [star_trivial, dotProduct_comm] using h.symm
  dsimp
  rw [hid]
  simpa only [Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec,
    one_mulVec, star_trivial, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, sub_nonneg] using hval

/-- Attainable losses over all positive finite dimensions, for a fixed residual
polynomial. The squared Euclidean radius is written as a dot product. -/
def lossSet (L R : ℝ) (p : ℝ[X]) : Set ℝ :=
  {a | ∃ (n : ℕ) (_ : 1 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n → ℝ), Q.PosSemidef ∧
    (L • (1 : Matrix (Fin n) (Fin n) ℝ) - Q).PosSemidef ∧
    e ⬝ᵥ e ≤ R ^ 2 ∧
    a = ((aeval Q p) *ᵥ e) ⬝ᵥ (Q *ᵥ ((aeval Q p) *ᵥ e)) / 2}

theorem scalar_loss_mem (L R : ℝ) (p : ℝ[X]) (μ : ℝ)
    (hμ : μ ∈ Set.Icc 0 L) :
    R ^ 2 / 2 * (μ * p.eval μ ^ 2) ∈ lossSet L R p := by
  let Q : Matrix (Fin 1) (Fin 1) ℝ := μ • 1
  refine ⟨1, le_refl _, Q, (fun _ => R), ?_, ?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.one.smul hμ.1
  · change (L • (1 : Matrix (Fin 1) (Fin 1) ℝ) - μ • 1).PosSemidef
    rw [← sub_smul]
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hμ.2)
  · simp [dotProduct, pow_two]
  · have ha : aeval Q p = p.eval μ • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      simpa only [Q, Algebra.algebraMap_eq_smul_one] using
        (aeval_algebraMap_apply_eq_algebraMap_eval
          (A := Matrix (Fin 1) (Fin 1) ℝ) μ p)
    rw [ha]
    simp [Q, smul_mulVec, dotProduct]
    ring

theorem isGreatest_lossSet (L R : ℝ) (p : ℝ[X])
    (μ : ℝ) (hμ : μ ∈ Set.Icc 0 L)
    (hmax : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 ≤ μ * p.eval μ ^ 2) :
    IsGreatest (lossSet L R p) (R ^ 2 / 2 * (μ * p.eval μ ^ 2)) := by
  refine ⟨scalar_loss_mem L R p μ hμ, ?_⟩
  rintro a ⟨n, hn, Q, e, hQ, hQL, he, rfl⟩
  have hb : 0 ≤ μ * p.eval μ ^ 2 := mul_nonneg hμ.1 (sq_nonneg _)
  have h := polynomial_energy_bound Q hQ L (μ * p.eval μ ^ 2) hQL p hmax e
  have h2 := mul_le_mul_of_nonneg_left he hb
  dsimp at h
  nlinarith

/-- The spectral risk formula is attained in dimension one. In particular,
the supremum over all finite dimensions equals the scalar interval maximum. -/
theorem spectral_risk_attained (L R : ℝ) (hL : 0 ≤ L) (p : ℝ[X]) :
    ∃ μ ∈ Set.Icc 0 L,
      IsGreatest ((fun x : ℝ => x * p.eval x ^ 2) '' Set.Icc 0 L)
        (μ * p.eval μ ^ 2) ∧
      IsGreatest (lossSet L R p) (R ^ 2 / 2 * (μ * p.eval μ ^ 2)) := by
  obtain ⟨μ, hμ, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hL)
    (show ContinuousOn (fun x : ℝ => x * p.eval x ^ 2) (Set.Icc 0 L) by fun_prop)
  refine ⟨μ, hμ, ?_, isGreatest_lossSet L R p μ hμ hmax⟩
  exact ⟨⟨μ,hμ,rfl⟩, by rintro a ⟨x,hx,rfl⟩; exact hmax hx⟩

/-- Losses of the actual increment trajectory driven by the exact oracle Qe. -/
def historyLossSet (N : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (L R : ℝ) : Set ℝ :=
  {a | ∃ (n : ℕ) (_ : 1 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n → ℝ), Q.PosSemidef ∧
    (L • (1 : Matrix (Fin n) (Fin n) ℝ) - Q).PosSemidef ∧
    e ⬝ᵥ e ≤ R ^ 2 ∧
    a = (QuadraticResidual.errorIter N d T.val Q e N) ⬝ᵥ
      (Q *ᵥ (QuadraticResidual.errorIter N d T.val Q e N)) / 2}

theorem historyLossSet_eq (N : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (L R : ℝ) :
    historyLossSet N d T L R =
      lossSet L R (QuadraticFoundations.pIter N d T.val N) := by
  ext a
  simp only [historyLossSet, lossSet, Set.mem_ofPred_eq,
    QuadraticResidual.errorIter_eq_polynomial N d T.val _ _ N (le_refl N)]

theorem history_risk_eq_scalar_max (N : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (L R : ℝ) (hL : 0 ≤ L) :
    ∃ μ ∈ Set.Icc 0 L,
      let p := QuadraticFoundations.pIter N d T.val N
      (∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 ≤ μ * p.eval μ ^ 2) ∧
      sSup (historyLossSet N d T L R) = R ^ 2 / 2 * (μ * p.eval μ ^ 2) := by
  obtain ⟨μ,hμ,hmax,hloss⟩ := spectral_risk_attained L R hL
    (QuadraticFoundations.pIter N d T.val N)
  refine ⟨μ,hμ,?_,?_⟩
  · intro x hx
    exact hmax.2 ⟨x,hx,rfl⟩
  · rw [historyLossSet_eq]
    exact hloss.isLUB.csSup_eq ⟨_,hloss.1⟩

end QuadraticSpectral
