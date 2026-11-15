module
public import Continuation.Quadratic.SpectralRisk
@[expose] public section
noncomputable section
namespace QuadraticSpectral
open Matrix Polynomial

/-- The two-real-variable loss model of the report, including every smaller loss. -/
def scalarLossSet (L R : ℝ) (p : ℝ[X]) : Set ℝ :=
  {a | ∃ μ ∈ Set.Icc 0 L, ∃ ρ ∈ Set.Icc 0 (R^2), a = ρ/2 * (μ * p.eval μ^2)}

lemma lossSet_nonneg (L R : ℝ) (p : ℝ[X]) {a : ℝ} (ha : a ∈ lossSet L R p) : 0 ≤ a := by
  rcases ha with ⟨n,hn,Q,e,hQ,hQL,he,rfl⟩
  have h := hQ.dotProduct_mulVec_nonneg ((aeval Q p) *ᵥ e)
  simp only [star_trivial] at h
  positivity

lemma lossSet_radius_mono (L R S : ℝ) (p : ℝ[X]) (h : R^2 ≤ S^2) :
    lossSet L R p ⊆ lossSet L S p := by
  rintro a ⟨n,hn,Q,e,hQ,hQL,he,ha⟩
  exact ⟨n,hn,Q,e,hQ,hQL,he.trans h,ha⟩

lemma scalar_loss_of_squared_radius (L R : ℝ) (p : ℝ[X])
    (μ ρ : ℝ) (hμ : μ ∈ Set.Icc 0 L) (hρ : ρ ∈ Set.Icc 0 (R^2)) :
    ρ/2 * (μ * p.eval μ^2) ∈ lossSet L R p := by
  have h := scalar_loss_mem L (Real.sqrt ρ) p μ hμ
  rw [Real.sq_sqrt hρ.1] at h
  exact lossSet_radius_mono L (Real.sqrt ρ) R p (by rw [Real.sq_sqrt hρ.1]; exact hρ.2) h

lemma scalarLossSet_subset (L R : ℝ) (p : ℝ[X]) : scalarLossSet L R p ⊆ lossSet L R p := by
  rintro a ⟨μ,hμ,ρ,hρ,rfl⟩
  exact scalar_loss_of_squared_radius L R p μ ρ hμ hρ

/-- Exactness of the scalar model concerns all losses, not merely their supremum. -/
theorem lossSet_eq_scalarLossSet (L R : ℝ) (hL : 0 ≤ L) (p : ℝ[X]) :
    lossSet L R p = scalarLossSet L R p := by
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨μ,hμ,hmax,hgreat⟩ := spectral_risk_attained L R hL p
    let c := μ * p.eval μ^2
    have hc : 0 ≤ c := mul_nonneg hμ.1 (sq_nonneg _)
    have ha0 := lossSet_nonneg L R p ha
    have hau : a ≤ R^2/2 * c := hgreat.2 ha
    by_cases hc0 : c=0
    · have haeq : a=0 := by rw [hc0,mul_zero] at hau; exact le_antisymm hau ha0
      exact ⟨μ,hμ,0,⟨le_rfl,sq_nonneg R⟩,by rw [haeq]; ring⟩
    · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      refine ⟨μ,hμ,2*a/c,⟨by positivity,?_⟩,?_⟩
      · apply (div_le_iff₀ hcp).mpr
        nlinarith
      · change a = (2*a/c)/2*c
        field_simp
  · exact scalarLossSet_subset L R p

/-- The actual multidimensional quadratic history has exactly the stated finite model. -/
theorem historyLossSet_eq_scalarLossSet (N : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (L R : ℝ) (hL : 0 ≤ L) :
    historyLossSet N d T L R = scalarLossSet L R (QuadraticFoundations.pIter N d T.val N) := by
  rw [historyLossSet_eq,lossSet_eq_scalarLossSet L R hL]

/-- Eliminating the radius variable leaves precisely the report's uniform spectral bound. -/
theorem scalarLossSet_uniform_bound (L R : ℝ) (p : ℝ[X]) (b : ℝ) :
    (∀ a ∈ scalarLossSet L R p,a ≤ b) ↔
      ∀ μ ∈ Set.Icc 0 L,R^2/2*(μ*p.eval μ^2) ≤ b := by
  constructor
  · intro h μ hμ
    exact h _ ⟨μ,hμ,R^2,⟨sq_nonneg R,le_rfl⟩,rfl⟩
  · rintro h a ⟨μ,hμ,ρ,hρ,rfl⟩
    have hcoef : 0 ≤ μ*p.eval μ^2 := mul_nonneg hμ.1 (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_right (by linarith [hρ.2] : ρ/2 ≤ R^2/2) hcoef).trans (h μ hμ)

end QuadraticSpectral
