module
-- ObjectiveResidual.lean
-- Perturbed convex quadratic gradient decomposition and objective residual
-- Source-faithful to ext:thm:near + Appendix K description:
--   grad f(x) = Q (x - x*) + r(x), 0 ≤ Q ≤ L0 I, r(x*)=0, Lip(r) ≤ ε,
--   q(x) = 1/2 (x-x*)ᵀ Q (x-x*),
--   goals: |f(x)-f* - q(x)| ≤ ε/2 ‖x-x*‖² and ‖grad f(x)‖ ≤ (L0+ε0)‖x-x*‖ when ε ≤ ε0.
-- Uses genuine C¹ gradient hypothesis (HasGradientAt) and segment integration (FTC-2),
-- no C² shortcut. All constants are finite and explicit.

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory intervalIntegral

namespace NearQuadratic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

noncomputable def qForm (Q : V →L[ℝ] V) (xStar : V) (x : V) : ℝ :=
  (1/2 : ℝ) * @inner ℝ V _ (Q (x - xStar)) (x - xStar)

structure PerturbedQuadraticData (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (Q : V →L[ℝ] V) (xStar : V) (f : V → ℝ) (r : V → V) (L0 ε : ℝ) : Prop where
  hQ_bound : ∀ v : V, ‖Q v‖ ≤ L0 * ‖v‖
  hQ_nonneg : ∀ v : V, 0 ≤ @inner ℝ V _ (Q v) v
  hL0_nonneg : 0 ≤ L0
  hε_nonneg : 0 ≤ ε
  hr_zero : r xStar = 0
  hr_lip : ∀ x y : V, ‖r x - r y‖ ≤ ε * ‖x - y‖
  hGrad : ∀ x : V, HasGradientAt f (Q (x - xStar) + r x) x

lemma r_norm_le_of_lip {Q : V →L[ℝ] V} {xStar : V} {f : V → ℝ} {r : V → V} {L0 ε : ℝ}
    (h : PerturbedQuadraticData V Q xStar f r L0 ε) (x : V) :
    ‖r x‖ ≤ ε * ‖x - xStar‖ := by
  have h1 := h.hr_lip x xStar
  rw [h.hr_zero] at h1
  simpa [sub_zero] using h1

lemma grad_norm_le {Q : V →L[ℝ] V} {xStar : V} {f : V → ℝ} {r : V → V} {L0 ε ε0 : ℝ}
    (h : PerturbedQuadraticData V Q xStar f r L0 ε) (hε_le : ε ≤ ε0) (_hε0_nonneg : 0 ≤ ε0)
    (x : V) :
    ‖Q (x - xStar) + r x‖ ≤ (L0 + ε0) * ‖x - xStar‖ := by
  have hQ := h.hQ_bound (x - xStar)
  have hr := r_norm_le_of_lip h x
  have hε : ε * ‖x - xStar‖ ≤ ε0 * ‖x - xStar‖ :=
    mul_le_mul_of_nonneg_right hε_le (norm_nonneg _)
  calc ‖Q (x - xStar) + r x‖ ≤ ‖Q (x - xStar)‖ + ‖r x‖ := norm_add_le _ _
    _ ≤ L0 * ‖x - xStar‖ + ε * ‖x - xStar‖ := add_le_add hQ hr
    _ = (L0 + ε) * ‖x - xStar‖ := by ring
    _ ≤ (L0 + ε0) * ‖x - xStar‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        linarith

private lemma hasDerivAt_curve (xStar v : V) (t : ℝ) :
    HasDerivAt (fun t : ℝ => xStar + ((t : ℝ) • (v : V))) v t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℝ) • (v : V)) v t := by
    have h := (hasDerivAt_id (x:=t)).smul_const v
    simpa [one_smul] using h
  exact h1.const_add xStar

lemma qForm_eq_half_inner (Q : V →L[ℝ] V) (xStar x : V) :
    qForm Q xStar x = (1/2 : ℝ) * @inner ℝ V _ (Q (x - xStar)) (x - xStar) := rfl

theorem residual_objective_estimate
    {Q : V →L[ℝ] V} {xStar : V} {f : V → ℝ} {r : V → V} {L0 ε : ℝ}
    (h : PerturbedQuadraticData V Q xStar f r L0 ε)
    (x : V) :
    |f x - f xStar - qForm Q xStar x| ≤ ε / 2 * ‖x - xStar‖ ^ 2 := by
  let v : V := x - xStar
  have hv : x = xStar + v := by simp only [v]; abel
  have hv0 : xStar + (0 : ℝ) • v = xStar := by simp [zero_smul]
  have hv1 : xStar + (1 : ℝ) • v = x := by simp [hv, one_smul]
  let g : ℝ → ℝ := fun t : ℝ => f (xStar + ((t : ℝ) • (v : V)))
  let g' : ℝ → ℝ := fun t => @inner ℝ V _ (Q ((xStar + ((t : ℝ) • (v : V))) - xStar) + r (xStar + ((t : ℝ) • (v : V)))) v
  have hg_hasDeriv : ∀ t : ℝ, HasDerivAt g (g' t) t := by
    intro t
    have hcurve : HasDerivAt (fun s : ℝ => xStar + ((s : ℝ) • (v : V))) v t := hasDerivAt_curve xStar v t
    have hGrad := h.hGrad (xStar + ((t : ℝ) • (v : V)))
    have hF : HasFDerivAt f (InnerProductSpace.toDual ℝ V (Q ((xStar + ((t : ℝ) • (v : V))) - xStar) + r (xStar + ((t : ℝ) • (v : V))))) (xStar + ((t : ℝ) • (v : V))) :=
      hGrad.hasFDerivAt
    have hcomp := hF.comp_hasDerivAt (f := fun s : ℝ => xStar + ((s : ℝ) • (v : V))) t hcurve
    have h_eq : (InnerProductSpace.toDual ℝ V (Q ((xStar + ((t : ℝ) • (v : V))) - xStar) + r (xStar + ((t : ℝ) • (v : V))))) v = g' t := by
      simp only [g', InnerProductSpace.toDual_apply_apply]
    rw [h_eq] at hcomp
    have hg_eq : g = f ∘ (fun s : ℝ => xStar + ((s : ℝ) • (v : V))) := rfl
    rw [← hg_eq] at hcomp
    exact hcomp
  have hLipschitz_r : LipschitzWith ⟨ε, h.hε_nonneg⟩ r := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    exact h.hr_lip a b
  have hCont_r : Continuous r := hLipschitz_r.continuous
  have hCont_curve : Continuous (fun t : ℝ => xStar + ((t : ℝ) • (v : V))) := by fun_prop
  have hg'_continuous : Continuous g' := by
    unfold g'
    have hQ_cont : Continuous (fun t : ℝ => @inner ℝ V _ (Q ((xStar + ((t : ℝ) • (v : V))) - xStar)) v) := by
      have h1 : Continuous (fun t : ℝ => Q ((xStar + ((t : ℝ) • (v : V))) - xStar)) := by
        have hsub : Continuous (fun t : ℝ => (xStar + ((t : ℝ) • (v : V))) - xStar) :=
          hCont_curve.sub continuous_const
        exact Q.continuous.comp hsub
      exact continuous_inner.comp (h1.prodMk continuous_const)
    have hr_cont : Continuous (fun t : ℝ => @inner ℝ V _ (r (xStar + ((t : ℝ) • (v : V)))) v) := by
      have hcomp : Continuous (fun t : ℝ => r (xStar + ((t : ℝ) • (v : V)))) := hCont_r.comp hCont_curve
      exact continuous_inner.comp (hcomp.prodMk continuous_const)
    have h_eq : (fun t => @inner ℝ V _ (Q ((xStar + ((t : ℝ) • (v : V))) - xStar) + r (xStar + ((t : ℝ) • (v : V)))) v) =
        fun t => @inner ℝ V _ (Q ((xStar + ((t : ℝ) • (v : V))) - xStar)) v + @inner ℝ V _ (r (xStar + ((t : ℝ) • (v : V)))) v := by
      funext t; rw [inner_add_left]
    rw [h_eq]
    exact hQ_cont.add hr_cont
  have hg'_integrable : IntervalIntegrable g' volume 0 1 :=
    hg'_continuous.intervalIntegrable 0 1
  have hFTC : ∫ t in (0:ℝ)..1, g' t = g 1 - g 0 := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt g (g' t) t := by
      intro t _; exact hg_hasDeriv t
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hg'_integrable
  have hg1 : g 1 = f x := by
    show f (xStar + (1:ℝ) • v) = f x
    rw [hv1]
  have hg0 : g 0 = f xStar := by
    show f (xStar + (0:ℝ) • v) = f xStar
    rw [hv0]
  have hFT_eq : ∫ t in (0:ℝ)..1, g' t = f x - f xStar := by
    rw [hFTC, hg1, hg0]
  let gQ : ℝ → ℝ := fun t => @inner ℝ V _ (Q ((xStar + ((t : ℝ) • (v : V))) - xStar)) v
  let gR : ℝ → ℝ := fun t => @inner ℝ V _ (r (xStar + ((t : ℝ) • (v : V)))) v
  have hg'_eq : ∀ t, g' t = gQ t + gR t := by
    intro t; simp [g', gQ, gR, inner_add_left]
  have hgQ_cont : Continuous gQ := by
    unfold gQ
    have h1 : Continuous (fun t : ℝ => Q ((xStar + ((t : ℝ) • (v : V))) - xStar)) := by
      have hsub : Continuous (fun t : ℝ => (xStar + ((t : ℝ) • (v : V))) - xStar) :=
        hCont_curve.sub continuous_const
      exact Q.continuous.comp hsub
    exact continuous_inner.comp (h1.prodMk continuous_const)
  have hgR_cont : Continuous gR := by
    unfold gR
    have hcomp : Continuous (fun t : ℝ => r (xStar + ((t : ℝ) • (v : V)))) := hCont_r.comp hCont_curve
    exact continuous_inner.comp (hcomp.prodMk continuous_const)
  have hgQ_integrable : IntervalIntegrable gQ volume 0 1 :=
    hgQ_cont.intervalIntegrable 0 1
  have hgR_integrable : IntervalIntegrable gR volume 0 1 :=
    hgR_cont.intervalIntegrable 0 1
  have hQ_simp : ∀ t : ℝ, Q ((xStar + ((t : ℝ) • (v : V))) - xStar) = t • Q v := by
    intro t
    have h1 : (xStar + ((t : ℝ) • (v : V))) - xStar = t • v := by abel
    rw [h1, Q.map_smul]
  have hgQ_simp : ∀ t : ℝ, gQ t = t * @inner ℝ V _ (Q v) v := by
    intro t
    simp only [gQ, hQ_simp t, real_inner_smul_left]
  have hIntQ : ∫ t in (0:ℝ)..1, gQ t = qForm Q xStar x := by
    have h1 : ∫ t in (0:ℝ)..1, gQ t = ∫ t in (0:ℝ)..1, (t * @inner ℝ V _ (Q v) v) := by
      apply intervalIntegral.integral_congr
      intro t _; rw [hgQ_simp t]
    rw [h1]
    have h2 : (fun t : ℝ => t * @inner ℝ V _ (Q v) v) = fun t => (@inner ℝ V _ (Q v) v) * t := by
      funext t; ring
    rw [h2, intervalIntegral.integral_const_mul, integral_id]
    simp [qForm, v]
    ring
  have hDecomp : ∫ t in (0:ℝ)..1, g' t = (∫ t in (0:ℝ)..1, gQ t) + (∫ t in (0:ℝ)..1, gR t) := by
    have h_eq : (fun t => g' t) = (fun t => gQ t + gR t) := by funext t; exact hg'_eq t
    rw [h_eq]
    exact intervalIntegral.integral_add hgQ_integrable hgR_integrable
  have hFT_decomp : f x - f xStar = (∫ t in (0:ℝ)..1, gQ t) + (∫ t in (0:ℝ)..1, gR t) := by
    rw [← hFT_eq, hDecomp]
  have hResEq : f x - f xStar - qForm Q xStar x = ∫ t in (0:ℝ)..1, gR t := by
    rw [hFT_decomp, hIntQ]; ring
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  have hAbsLeInter : |∫ t in (0:ℝ)..1, gR t| ≤ ∫ t in (0:ℝ)..1, |gR t| :=
    intervalIntegral.abs_integral_le_integral_abs h01
  have hBound : ∀ t ∈ Set.Icc (0:ℝ) 1, |gR t| ≤ ε * t * ‖v‖ ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hInner : |gR t| ≤ ‖r (xStar + ((t : ℝ) • (v : V)))‖ * ‖v‖ := by
      simp only [gR]
      exact abs_real_inner_le_norm _ _
    have hr_norm : ‖r (xStar + ((t : ℝ) • (v : V)))‖ ≤ ε * t * ‖v‖ := by
      have h1 := r_norm_le_of_lip h (xStar + ((t : ℝ) • (v : V)))
      have h2 : ‖xStar + ((t : ℝ) • (v : V)) - xStar‖ = ‖t • v‖ := by
        have : xStar + ((t : ℝ) • (v : V)) - xStar = t • v := by abel
        rw [this]
      rw [h2] at h1
      have hnorm_smul : ‖t • v‖ = |t| * ‖v‖ := norm_smul t v
      rw [hnorm_smul] at h1
      have ht_abs : |t| = t := abs_of_nonneg ht0
      rw [ht_abs] at h1
      have : ε * (t * ‖v‖) = ε * t * ‖v‖ := by ring
      rw [this] at h1
      exact h1
    calc |gR t| ≤ ‖r (xStar + ((t : ℝ) • (v : V)))‖ * ‖v‖ := hInner
      _ ≤ (ε * t * ‖v‖) * ‖v‖ := by
          apply mul_le_mul_of_nonneg_right hr_norm (norm_nonneg _)
      _ = ε * t * ‖v‖ ^ 2 := by ring
  have hgR_abs_cont : Continuous (fun t : ℝ => |gR t|) := hgR_cont.abs
  have hgR_abs_integrable : IntervalIntegrable (fun t => |gR t|) volume 0 1 :=
    hgR_abs_cont.intervalIntegrable 0 1
  have hWeight_cont : Continuous (fun t : ℝ => ε * t * ‖v‖ ^ 2) := by fun_prop
  have hWeight_integrable : IntervalIntegrable (fun t => ε * t * ‖v‖ ^ 2) volume 0 1 :=
    hWeight_cont.intervalIntegrable 0 1
  have hMono : ∫ t in (0:ℝ)..1, |gR t| ≤ ∫ t in (0:ℝ)..1, ε * t * ‖v‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on h01 hgR_abs_integrable hWeight_integrable
    intro t ht
    exact hBound t ht
  have hWeight_eq : ∫ t in (0:ℝ)..1, ε * t * ‖v‖ ^ 2 = ε / 2 * ‖v‖ ^ 2 := by
    have h1 : (fun t : ℝ => ε * t * ‖v‖ ^ 2) = fun t => (ε * ‖v‖ ^ 2) * t := by funext t; ring
    rw [h1, intervalIntegral.integral_const_mul, integral_id]
    ring
  have hFinal : |∫ t in (0:ℝ)..1, gR t| ≤ ε / 2 * ‖v‖ ^ 2 := by
    calc |∫ t in (0:ℝ)..1, gR t| ≤ ∫ t in (0:ℝ)..1, |gR t| := hAbsLeInter
      _ ≤ ∫ t in (0:ℝ)..1, ε * t * ‖v‖ ^ 2 := hMono
      _ = ε / 2 * ‖v‖ ^ 2 := hWeight_eq
  have hv_eq : ‖v‖ = ‖x - xStar‖ := rfl
  rw [hResEq]
  rw [hv_eq] at hFinal
  exact hFinal

theorem gradient_norm_bound
    {Q : V →L[ℝ] V} {xStar : V} {f : V → ℝ} {r : V → V} {L0 ε ε0 : ℝ}
    (h : PerturbedQuadraticData V Q xStar f r L0 ε) (hε_le : ε ≤ ε0) (hε0_nonneg : 0 ≤ ε0)
    (x : V) :
    ‖Q (x - xStar) + r x‖ ≤ (L0 + ε0) * ‖x - xStar‖ :=
  grad_norm_le h hε_le hε0_nonneg x

end NearQuadratic
