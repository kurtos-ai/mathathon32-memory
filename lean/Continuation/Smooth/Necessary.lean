module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic
@[expose] public section

open Set
open scoped InnerProductSpace

namespace SmoothNecessary
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {f : V → ℝ} {G : V → V}

theorem line_hasDerivAt (hf : ∀ x, HasGradientAt f (G x) x) (x v : V) (t : ℝ) :
    HasDerivAt (fun a : ℝ => f (x + a • v)) ⟪G (x + t • v), v⟫_ℝ t := by
  have hline : HasDerivAt (fun a : ℝ => x + a • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline

theorem convex_line (hc : ConvexOn ℝ univ f) (x v : V) :
    ConvexOn ℝ univ (fun a : ℝ => f (x + a • v)) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ s t hs ht hst
  have hid : x + (s • a + t • b) • v = s • (x + a • v) + t • (x + b • v) := by
    calc
      x + (s • a + t • b) • v = (s+t) • x + (s • a + t • b) • v := by rw [hst, one_smul]
      _ = _ := by simp only [smul_add, add_smul, smul_smul, smul_eq_mul]; abel
  dsimp only
  rw [hid]
  exact hc.2 (mem_univ _) (mem_univ _) hs ht hst

theorem tangent_lower (hf : ∀ x, HasGradientAt f (G x) x)
    (hc : ConvexOn ℝ univ f) (x y : V) :
    f x + ⟪G x, y - x⟫_ℝ ≤ f y := by
  have h := (convex_line hc x (y-x)).le_slope_of_hasDerivAt
    (mem_univ (0:ℝ)) (mem_univ (1:ℝ)) zero_lt_one (line_hasDerivAt hf x (y-x) 0)
  simp only [zero_smul, add_zero, slope, one_smul, add_sub_cancel, sub_zero,
    inv_one, vsub_eq_sub] at h
  linarith

theorem descent (hf : ∀ x, HasGradientAt f (G x) x) {L : NNReal}
    (hLip : LipschitzWith L G) (x v : V) :
    f (x + v) ≤ f x + ⟪G x, v⟫_ℝ + (L:ℝ)/2 * ‖v‖^2 := by
  let F : ℝ → ℝ := fun t => f (x + t • v)
  let B : ℝ → ℝ := fun t => f x + t * ⟪G x, v⟫_ℝ + (L:ℝ)/2 * t^2 * ‖v‖^2
  let B' : ℝ → ℝ := fun t => ⟪G x, v⟫_ℝ + (L:ℝ) * t * ‖v‖^2
  have hF (t : ℝ) : HasDerivAt F ⟪G (x+t•v),v⟫_ℝ t := line_hasDerivAt hf x v t
  have hB (t : ℝ) : HasDerivAt B (B' t) t := by
    convert (((hasDerivAt_id t).mul_const ⟪G x,v⟫_ℝ).const_add (f x)).add
      ((((hasDerivAt_id t).pow 2).const_mul ((L:ℝ)/2)).mul_const (‖v‖^2)) using 1 <;>
      (try funext a) <;> dsimp [B, B'] <;> ring
  have hbound (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) : ⟪G (x+t•v),v⟫_ℝ ≤ B' t := by
    have hn : ‖G (x+t•v)-G x‖ ≤ (L:ℝ)*t*‖v‖ := by
      have h := hLip.dist_le_mul (x+t•v) x
      simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
        mul_assoc] using h
    have hi := real_inner_le_norm (G (x+t•v)-G x) v
    rw [inner_sub_left] at hi
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg v)
    dsimp [B']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F,B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hbound
    (x:=1) (by constructor <;> norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
  simpa [F,B] using h

/-- The necessary smooth-convex interpolation inequality for actual functions. -/
theorem interpolation_necessary (hf : ∀ x, HasGradientAt f (G x) x)
    (hc : ConvexOn ℝ univ f) {L : NNReal} (hL : 0 < (L:ℝ))
    (hLip : LipschitzWith L G) (x y : V) :
    0 ≤ f x - f y - ⟪G y, x-y⟫_ℝ - 1/(2*(L:ℝ)) * ‖G x-G y‖^2 := by
  let w := G x - G y
  let v := -(1/(L:ℝ)) • w
  have hd := descent hf hLip x v
  have ht := tangent_lower hf hc y (x+v)
  have hsplit : x + v - y = (x-y)+v := by abel
  rw [hsplit, inner_add_right] at ht
  have hi : ⟪G x,v⟫_ℝ - ⟪G y,v⟫_ℝ = -(1/(L:ℝ)) * ‖w‖^2 := by
    rw [← inner_sub_left]
    change ⟪w, -(1/(L:ℝ)) • w⟫_ℝ = _
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : ‖v‖^2 = (1/(L:ℝ))^2 * ‖w‖^2 := by
    simp [v, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hcoef : -(1/(L:ℝ)) + (L:ℝ)/2 * (1/(L:ℝ))^2 = -(1/(2*(L:ℝ))) := by
    field_simp
    ring
  have heq : ⟪G x,v⟫_ℝ + (L:ℝ)/2 * ‖v‖^2 - ⟪G y,v⟫_ℝ =
      -(1/(2*(L:ℝ))) * ‖w‖^2 := by
    calc
      _ = (⟪G x,v⟫_ℝ - ⟪G y,v⟫_ℝ) + (L:ℝ)/2 * ‖v‖^2 := by ring
      _ = (-(1/(L:ℝ)) + (L:ℝ)/2 * (1/(L:ℝ))^2) * ‖w‖^2 := by rw [hi,hn]; ring
      _ = _ := by rw [hcoef]
  dsimp [w] at heq
  linarith

end SmoothNecessary
