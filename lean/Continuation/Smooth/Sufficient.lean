module
public import Continuation.SmoothDualCore
public import Continuation.Smooth.ConjugateRegularity
public import Continuation.Smooth.Necessary
public import Mathlib.Topology.Order.Lattice
@[expose] public section

open Set
open scoped InnerProductSpace
noncomputable section

namespace SmoothDual
variable {d n : ℕ} [NeZero n] {L : ℝ}
variable (x g : Fin n → E d) (f : Fin n → ℝ)

theorem Hi_continuous (i : Fin n) : Continuous (Hi x g f L i) := by
  unfold Hi
  fun_prop

theorem H_continuous : Continuous (H x g f L) := by
  unfold H
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => Hi_continuous x g f i)

/-- Sufficient smooth-convex interpolation, with an actual everywhere-defined gradient. -/
theorem interpolation_sufficient (hL : 0 < L)
    (hTHG : ∀ i j, 0 ≤ f i-f j-⟪g j,x i-x j⟫_ℝ-1/(2*L)*‖g i-g j‖^2) :
    ∃ F : E d → ℝ, ∃ G : E d → E d,
      (∀ p, HasGradientAt F (G p) p) ∧ ConvexOn ℝ univ F ∧
      LipschitzWith (Real.toNNReal L) G ∧
      ∀ i, F (x i) = f i ∧ G (x i) = g i := by
  have hμ : 0 < 1/L := one_div_pos.mpr hL
  have hsc := H_strongConvex (x:=x) (g:=g) (f:=f) (L:=L)
  obtain ⟨G,hG,hgrad,hconv,hlip⟩ := ConjugateRegularity.exists_smooth_conjugate
    hμ hsc (H_continuous x g f) (x 0) (g 0)
    (H_subgradient_weak (x:=x) (g:=g) (f:=f) hL hTHG 0)
  refine ⟨ConjugateRegularity.value (H x g f L) G,G,hgrad,hconv,?_,?_⟩
  · simpa only [one_div, inv_inv] using hlip
  · intro i
    have hGi : G (x i) = g i := ConjugateRegularity.maximizer_unique hμ hsc
      (x i) (G (x i)) (g i) (hG (x i))
      (H_subgradient_weak (x:=x) (g:=g) (f:=f) hL hTHG i)
    refine ⟨?_,hGi⟩
    simp only [ConjugateRegularity.value, hGi]
    rw [H_contact' (x:=x) (g:=g) (f:=f) hTHG i]
    linarith [real_inner_comm (x i) (g i)]

end SmoothDual

namespace SmoothInterpolation
variable {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ} {L : ℝ}

theorem sufficient (hL : 0 < L) (x g : ι → EuclideanSpace ℝ (Fin d)) (f : ι → ℝ)
    (hTHG : ∀ i j, 0 ≤ f i-f j-⟪g j,x i-x j⟫_ℝ-1/(2*L)*‖g i-g j‖^2) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ,
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ p, HasGradientAt F (G p) p) ∧ ConvexOn ℝ univ F ∧
      LipschitzWith (Real.toNNReal L) G ∧
      ∀ i, F (x i) = f i ∧ G (x i) = g i := by
  classical
  let e := Fintype.equivFin ι
  letI : NeZero (Fintype.card ι) := ⟨Nat.ne_of_gt Fintype.card_pos⟩
  obtain ⟨F,G,hGrad,hConv,hLip,hData⟩ := SmoothDual.interpolation_sufficient
    (x ∘ e.symm) (g ∘ e.symm) (f ∘ e.symm) hL (fun i j => hTHG (e.symm i) (e.symm j))
  refine ⟨F,G,hGrad,hConv,hLip,fun i => ?_⟩
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hData (e i)

theorem iff_interpolable (hL : 0 < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (f : ι → ℝ) :
    (∀ i j, 0 ≤ f i-f j-⟪g j,x i-x j⟫_ℝ-1/(2*L)*‖g i-g j‖^2) ↔
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ,
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ p, HasGradientAt F (G p) p) ∧ ConvexOn ℝ univ F ∧
      LipschitzWith (Real.toNNReal L) G ∧
      ∀ i, F (x i) = f i ∧ G (x i) = g i := by
  constructor
  · exact sufficient hL x g f
  · rintro ⟨F,G,hGrad,hConv,hLip,hData⟩ i j
    have hc : ((Real.toNNReal L : NNReal) : ℝ) = L := Real.coe_toNNReal _ hL.le
    have hp : 0 < ((Real.toNNReal L : NNReal) : ℝ) := by rwa [hc]
    have h := SmoothNecessary.interpolation_necessary hGrad hConv hp hLip (x i) (x j)
    simpa only [hc,(hData i).1,(hData j).1,(hData i).2,(hData j).2] using h

end SmoothInterpolation
