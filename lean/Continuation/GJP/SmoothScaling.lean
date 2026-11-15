module
public import Continuation.GJP.HistoryNormalization
public import Continuation.Smooth.GramExact
public import Continuation.GJP.Simplex

@[expose] public section
noncomputable section
open Matrix
open scoped InnerProductSpace
namespace GJP
variable {n N : ℕ} {R₀ : ℝ}

lemma scaled_hasGradient (I : SmoothAttain.Instance n 1 R₀) (L a : ℝ) (ha : a ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (fun x => (L*a^2)*I.f (a⁻¹ • x)) ((L*a) • I.G (a⁻¹ • x)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    a⁻¹ • ContinuousLinearMap.id ℝ _
  have h := ((I.hasGrad (a⁻¹ • x)).hasFDerivAt.comp x A.hasFDerivAt).const_mul (L*a^2)
  have hderiv : InnerProductSpace.toDual ℝ _ ((L*a) • I.G (a⁻¹ • x)) =
      ((L*a^2) • InnerProductSpace.toDual ℝ _ (I.G (a⁻¹ • x))).comp A := by
    apply ContinuousLinearMap.ext
    intro v
    change ⟪(L*a) • I.G (a⁻¹ • x), v⟫_ℝ =
      (L*a^2)*⟪I.G (a⁻¹ • x), a⁻¹ • v⟫_ℝ
    simp only [real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [hderiv]
  exact h

/-- Rescale an actual normalized smooth-convex instance to smoothness `L` and radius `R`. -/
def rescaleInstance (I : SmoothAttain.Instance n 1 R₀) (L a R : ℝ)
    (hL : 0 < L) (ha : 0 < a) (hR : a*R₀ ≤ R) : SmoothAttain.Instance n L R where
  f := fun x => (L*a^2)*I.f (a⁻¹ • x)
  G := fun x => (L*a) • I.G (a⁻¹ • x)
  hasGrad := scaled_hasGradient I L a (ne_of_gt ha)
  convex := by
    have hc := I.convex.comp_linearMap (a⁻¹ • LinearMap.id :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    have hc' := hc.smul (show 0 ≤ L*a^2 by positivity)
    simpa using hc'
  lip := ⟨L,hL.le⟩
  lip_eq := rfl
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hl := I.lipschitz.dist_le_mul (a⁻¹ • x) (a⁻¹ • y)
    rw [I.lip_eq, one_mul] at hl
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hL ha)]
    simp only [dist_eq_norm] at hl
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)] at hl
    have hmul := mul_le_mul_of_nonneg_left hl (le_of_lt (mul_pos hL ha))
    convert hmul using 1
    simp only [dist_eq_norm]
    field_simp
    change L * ‖x - y‖ = ‖x - y‖ * L
    ring
  x0 := a • I.x0
  xStar := a • I.xStar
  isMin := by
    intro x _
    change (L*a^2)*I.f (a⁻¹ • (a • I.xStar)) ≤ (L*a^2)*I.f (a⁻¹ • x)
    have h := I.isMin (show a⁻¹ • x ∈ Set.univ from Set.mem_univ _)
    have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ L*a^2 by positivity)
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul] using hm
  near := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left I.near ha.le).trans hR

/-- Smoothness rescaling multiplies the additive method coefficients by `L`. -/
theorem rescale_trajectory (I : SmoothAttain.Instance n 1 R₀) (L a R : ℝ)
    (hL : 0 < L) (ha : 0 < a) (hR : a*R₀ ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    OracleTrajectory.run W (rescaleInstance I L a R hL ha hR).G (rescaleInstance I L a R hL ha hR).x0 =
      fun i => a • OracleTrajectory.run (L • W) I.G I.x0 i := by
  symm
  apply OracleTrajectory.unique
  intro i
  rw [OracleTrajectory.run_eq, smul_add, Finset.smul_sum]
  change a • I.x0 + _ = a • I.x0 + _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [rescaleInstance, Matrix.smul_apply, smul_eq_mul, smul_smul,
    inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  congr 1
  ring

/-- Actual terminal losses scale by exactly `L*a²`. -/
theorem rescale_terminalLoss (I : SmoothAttain.Instance n 1 R₀) (L a R : ℝ)
    (hL : 0 < L) (ha : 0 < a) (hR : a*R₀ ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    SmoothGramModel.terminalLoss (rescaleInstance I L a R hL ha hR) W =
      (L*a^2)*SmoothGramModel.terminalLoss I (L • W) := by
  unfold SmoothGramModel.terminalLoss
  rw [rescale_trajectory I L a R hL ha hR W]
  simp only [rescaleInstance, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  ring

/-- An actual uniform bound transfers to normalized smoothness and radius. -/
theorem uniform_bound_rescale (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (L a R γ : ℝ) (hL : 0 < L) (ha : 0 < a) (hR : a*R₀ ≤ R)
    (hbound : ∀ z ∈ SmoothGramModel.actualLossSet N W L R, z ≤ (L*a^2)*γ) :
    ∀ z ∈ SmoothGramModel.actualLossSet N (L • W) 1 R₀, z ≤ γ := by
  rintro z ⟨m,I,rfl⟩
  have h := hbound (SmoothGramModel.terminalLoss (rescaleInstance I L a R hL ha hR) W)
    ⟨m,rescaleInstance I L a R hL ha hR,rfl⟩
  rw [rescale_terminalLoss] at h
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < L*a^2)).mp h

/-- The scale matching the source paper's radius is exact. -/
lemma normalized_radius (R : ℝ) : (R / Real.sqrt 2) * Real.sqrt 2 = R := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  exact div_mul_cancel₀ R hs

lemma normalized_benchmark (N : ℕ) (L R : ℝ) :
    (L * (R / Real.sqrt 2)^2) * rOGM N =
      L*R^2/(2*SmoothBenchmark.theta N N^2) := by
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  simp only [rOGM, div_pow, hs]
  ring

/-- Every actual sharp bound yields the source paper's normalized sharp bound. -/
theorem uniform_bound_normalized (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hbound : ∀ z ∈ SmoothGramModel.actualLossSet N W L R,
      z ≤ L*R^2/(2*SmoothBenchmark.theta N N^2)) :
    ∀ z ∈ SmoothGramModel.actualLossSet N (L • W) 1 (Real.sqrt 2), z ≤ rOGM N := by
  apply uniform_bound_rescale W L (R / Real.sqrt 2) R (rOGM N) hL
    (div_pos hR (Real.sqrt_pos.2 (by norm_num)))
    (le_of_eq (normalized_radius R))
  simpa only [normalized_benchmark] using hbound

lemma sourceMatrix_normalized (L : ℝ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    sourceMatrix 1 (L • W) = sourceMatrix L W := by
  simp only [sourceMatrix, one_smul]

end GJP
