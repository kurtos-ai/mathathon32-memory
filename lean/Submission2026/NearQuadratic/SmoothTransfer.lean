module
/-
Source fidelity note — SmoothTransfer (NearQuadratic / Appendix K smooth transfer):

Mathematical source: `ext:thm:near` smooth-transfer paragraph and Appendix K
transport discussion.  For a convex `Lf`-smooth `f : V → ℝ` with minimizer
`x⋆` and `f⋆ = f(x⋆) = inf f`, the smoothness upper bound

  f(y) ≤ f(x) + ⟪∇f(x), y−x⟫ + (Lf/2) ‖y−x‖²

together with convexity (used only to identify `f⋆` as global lower bound,
`f⋆ ≤ f(x)` for all `x`, and `∇f(x⋆)=0`) yields the coercive gradient bound

  ‖∇f(x)‖² ≤ 2 Lf (f(x) − f⋆)                                    (∗)

via the standard descent lemma `y = x − (1/Lf)∇f(x)` (and the `Lf=0` constant
case).  From smoothness, Cauchy–Schwarz, and (∗),

  f(xᴮ)−f⋆ ≤ ( √(f(xᴬ)−f⋆) + √(Lf/2) ‖xᴮ−xᴬ‖ )²,

hence if `‖xᴮ−xᴬ‖ ≤ D` then

  f(xᴮ)−f⋆ ≤ ( √(f(xᴬ)−f⋆) + √(Lf/2) D )².                         (†)

Both (∗) and (†) hold with `f(xᴬ)−f⋆ = 0` and `D = 0` (then `‖∇f(xᴬ)‖=0`).
No C², no quadratic factorization, no minimax value is assumed.
The companion `ActualSmoothTransfer` module derives the upper-envelope
hypothesis from actual differentiability and a Lipschitz gradient.
-/
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

open RealInnerProductSpace

namespace NearQuadratic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Smoothness + lower-bound data sufficient for gradient and transfer bounds.
`Lf`-smoothness is taken as the upper quadratic envelope; `fStar_le` is the
global lower bound `f⋆ ≤ f(x)` (for convex `f` with minimizer `x⋆`,
`f⋆ = f(x⋆)`).  `grad` is the gradient field `∇f(x)` in `V` (identified via
`toDual`).  No convexity is needed for the two bounds below beyond `fStar_le`;
convexity is the source-faithful justification for `fStar_le` and `∇f(x⋆)=0`. -/
structure SmoothLowerData (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (grad : V → V) (fStar : ℝ) (Lf : ℝ) : Prop where
  hLf_nonneg : 0 ≤ Lf
  hfStar_le : ∀ x : V, fStar ≤ f x
  hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2

section GradientBound

variable {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}

/-- Auxiliary: smoothness applied to the gradient step `y = x - t • g` yields
`f(y) ≤ f(x) − t‖g‖² + (Lf/2) t²‖g‖²`. -/
lemma smooth_gradient_step (hSm : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (x : V) (t : ℝ) :
    f (x - t • grad x) ≤ f x + (-t * ‖grad x‖ ^ 2 + Lf / 2 * (t ^ 2 * ‖grad x‖ ^ 2)) := by
  have h := hSm x (x - t • grad x)
  have hsub : x - t • grad x - x = -(t • grad x) := by abel
  rw [hsub] at h
  have hinner : @inner ℝ V _ (grad x) (-(t • grad x)) = -(t * ‖grad x‖ ^ 2) := by
    rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have hnorm : ‖-(t • grad x)‖ ^ 2 = t ^ 2 * ‖grad x‖ ^ 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h2 := h
  rw [hinner, hnorm] at h2
  linarith

/-- Coercive gradient bound for `Lf>0`:
`‖∇f(x)‖² ≤ 2 Lf (f(x)−f⋆)` from smoothness and `f⋆ ≤ f(y)` at
`y = x − (1/Lf)∇f(x)`. -/
theorem gradient_norm_sq_le_of_smooth {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}
    (hLf_pos : 0 < Lf)
    (hfStar_le : ∀ x : V, fStar ≤ f x)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (x : V) :
    ‖grad x‖ ^ 2 ≤ 2 * Lf * (f x - fStar) := by
  have hLf_ne : Lf ≠ 0 := ne_of_gt hLf_pos
  -- apply smoothness to the gradient step with t = 1/Lf
  have hstep := smooth_gradient_step (V:=V) (f:=f) (grad:=grad) (Lf:=Lf) hSmooth x (1 / Lf)
  -- lower bound at the stepped point
  have hlow : fStar ≤ f (x - (1 / Lf) • grad x) := hfStar_le _
  -- expand the step bound
  -- f(x - (1/Lf) g) ≤ f(x) - (1/Lf)‖g‖² + (Lf/2)(1/Lf²)‖g‖² = f(x) - (1/(2Lf))‖g‖²
  have hcalc : -(1 / Lf) * ‖grad x‖ ^ 2 + Lf / 2 * ((1 / Lf) ^ 2 * ‖grad x‖ ^ 2)
      = -(1 / (2 * Lf)) * ‖grad x‖ ^ 2 := by
    field_simp
    ring
  have hle : f (x - (1 / Lf) • grad x) ≤ f x - 1 / (2 * Lf) * ‖grad x‖ ^ 2 := by
    have h1 : f (x - (1 / Lf) • grad x) ≤ f x + (-(1 / Lf) * ‖grad x‖ ^ 2 + Lf / 2 * ((1 / Lf) ^ 2 * ‖grad x‖ ^ 2)) := by
      -- rewrite hstep conclusion
      have hs := hstep
      -- hstep already is the expanded form; just rewrite
      convert hs using 1
    have h2 : f x + (-(1 / Lf) * ‖grad x‖ ^ 2 + Lf / 2 * ((1 / Lf) ^ 2 * ‖grad x‖ ^ 2)) = f x - 1 / (2 * Lf) * ‖grad x‖ ^ 2 := by
      rw [hcalc]; ring
    linarith
  -- fStar ≤ f(x) - 1/(2Lf)‖g‖²  →  ‖g‖² ≤ 2Lf(f(x)-fStar)
  have h3 : fStar ≤ f x - 1 / (2 * Lf) * ‖grad x‖ ^ 2 := le_trans hlow hle
  have h4 : 1 / (2 * Lf) * ‖grad x‖ ^ 2 ≤ f x - fStar := by linarith
  have hLf2_pos : 0 < 2 * Lf := by positivity
  have hle2 : ‖grad x‖ ^ 2 ≤ 2 * Lf * (f x - fStar) := by
    have h5 : 2 * Lf * (1 / (2 * Lf) * ‖grad x‖ ^ 2) = ‖grad x‖ ^ 2 := by
      field_simp
    have h6 : 2 * Lf * (1 / (2 * Lf) * ‖grad x‖ ^ 2) ≤ 2 * Lf * (f x - fStar) :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt hLf2_pos)
    rw [h5] at h6
    exact h6
  exact hle2

/-- When `Lf=0`, smoothness forces `⟪g(x),y−x⟫ ≥ f(y)−f(x)`; choosing
`y = x + g(x)` and using `fStar ≤ f(y)` with the lower bound yields `g=0`.
More directly: if `fStar ≤ f` and `Lf=0`-smooth, then `‖g(x)‖=0`; hence the
gradient bound `‖g‖² ≤ 0 = 2*0*(f−fStar)` holds. -/
theorem gradient_norm_sq_le_of_smooth_zero {f : V → ℝ} {grad : V → V} {fStar : ℝ}
    (hfStar_le : ∀ x : V, fStar ≤ f x)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x))
    (x : V) :
    grad x = 0 := by
  by_contra hne
  have hnorm_pos : 0 < ‖grad x‖ := norm_pos_iff.mpr hne
  -- take y = x + grad x, then smoothness gives f(y) ≤ f(x) + ‖g‖²
  have h1 := hSmooth x (x + grad x)
  have hsub : x + grad x - x = grad x := by abel
  rw [hsub] at h1
  have hinner : @inner ℝ V _ (grad x) (grad x) = ‖grad x‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
  rw [hinner] at h1
  -- take y = x + (f(x)-fStar+1)/‖g‖² • g  to amplify inner product arbitrarily?
  -- Actually with Lf=0 we can get a direct contradiction by scaling.
  -- Use y = x + t•g for arbitrary t: f(y) ≤ f(x) + t‖g‖², but also fStar ≤ f(y).
  -- So fStar ≤ f(x) + t‖g‖² for all t. Choose t = -(f(x)-fStar+1)/‖g‖² → contradiction
  -- unless ‖g‖=0.
  have h_forall_t : ∀ t : ℝ, fStar ≤ f x + t * ‖grad x‖ ^ 2 := by
    intro t
    have ht := hSmooth x (x + t • grad x)
    have hsub2 : x + t • grad x - x = t • grad x := by abel
    rw [hsub2] at ht
    have hinner2 : @inner ℝ V _ (grad x) (t • grad x) = t * ‖grad x‖ ^ 2 := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hinner2] at ht
    linarith [hfStar_le (x + t • grad x)]
  -- pick t negative large
  have hgap_nonneg : 0 ≤ f x - fStar := by linarith [hfStar_le x]
  let t0 := -((f x - fStar + 1) / ‖grad x‖ ^ 2)
  have ht0 := h_forall_t t0
  have hsq_pos : 0 < ‖grad x‖ ^ 2 := by positivity
  have ht0_val : t0 * ‖grad x‖ ^ 2 = -(f x - fStar + 1) := by
    simp only [t0]
    field_simp
  rw [ht0_val] at ht0
  linarith

/-- Unified gradient bound for `Lf ≥ 0` (both `Lf>0` and `Lf=0` cases).
This is the coercive bound `‖∇f(x)‖² ≤ 2 Lf (f(x)−f⋆)` used in Appendix K. -/
theorem gradient_norm_sq_le {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}
    (hLf_nonneg : 0 ≤ Lf)
    (hfStar_le : ∀ x : V, fStar ≤ f x)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (x : V) :
    ‖grad x‖ ^ 2 ≤ 2 * Lf * (f x - fStar) := by
  by_cases hLf_zero : Lf = 0
  · -- Lf = 0: smoothness with Lf/2 term is zero, so we are in zero case
    have hSmooth0 : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) := by
      intro x y
      have h := hSmooth x y
      rw [hLf_zero] at h
      simp at h
      exact h
    have hg0 := gradient_norm_sq_le_of_smooth_zero (V:=V) hfStar_le hSmooth0 x
    rw [hg0]
    simp [hLf_zero]
  · have hLf_pos : 0 < Lf := lt_of_le_of_ne hLf_nonneg (Ne.symm hLf_zero)
    exact gradient_norm_sq_le_of_smooth hLf_pos hfStar_le hSmooth x

/-- Nonnegativity of the gap and gradient bound implies `‖∇f(x)‖ ≤ √(2 Lf (f−f⋆))`
when `Lf ≥ 0`. -/
lemma norm_grad_le_sqrt {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}
    (hLf_nonneg : 0 ≤ Lf)
    (hfStar_le : ∀ x : V, fStar ≤ f x)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (x : V) :
    ‖grad x‖ ≤ Real.sqrt (2 * Lf * (f x - fStar)) := by
  have hsq := gradient_norm_sq_le hLf_nonneg hfStar_le hSmooth x
  have hgap : 0 ≤ f x - fStar := by linarith [hfStar_le x]
  have hprod_nonneg : 0 ≤ 2 * Lf * (f x - fStar) := mul_nonneg (mul_nonneg (by linarith) hLf_nonneg) hgap
  have hnorm_nonneg : 0 ≤ ‖grad x‖ := norm_nonneg _
  -- ‖g‖² ≤ 2LfΔ → ‖g‖ ≤ √(2LfΔ)  via Real.le_sqrt_of_sq_le
  exact Real.le_sqrt_of_sq_le hsq

end GradientBound

section Transfer

/-- Smooth upper bound applied from `xA` to `xB`: `f(xB) ≤ f(xA) + ⟪g(xA),xB−xA⟫ + (Lf/2)‖xB−xA‖²`. -/
lemma smooth_upper_from {f : V → ℝ} {grad : V → V} {Lf : ℝ}
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (xA xB : V) :
    f xB ≤ f xA + @inner ℝ V _ (grad xA) (xB - xA) + Lf / 2 * ‖xB - xA‖ ^ 2 :=
  hSmooth xA xB

/-- Cauchy–Schwarz step for transfer: `⟪gA, xB−xA⟫ ≤ ‖gA‖·‖xB−xA‖ ≤ ‖gA‖·D` when `‖xB−xA‖ ≤ D`, `0 ≤ D`. -/
lemma inner_le_norm_mul_D (grad : V → V) (xA xB : V) (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hDist : ‖xB - xA‖ ≤ D) :
    @inner ℝ V _ (grad xA) (xB - xA) ≤ ‖grad xA‖ * D := by
  calc @inner ℝ V _ (grad xA) (xB - xA)
      ≤ ‖grad xA‖ * ‖xB - xA‖ := real_inner_le_norm _ _
    _ ≤ ‖grad xA‖ * D := mul_le_mul_of_nonneg_left hDist (norm_nonneg _)

/-- Core transfer inequality from smoothness + displacement bound:
`f(xB) ≤ f(xA) + ‖gA‖·D + (Lf/2) D²`. -/
lemma smooth_transfer_core {f : V → ℝ} {grad : V → V} {Lf D : ℝ}
    (hLf_nonneg : 0 ≤ Lf) (hD_nonneg : 0 ≤ D)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (xA xB : V) (hDist : ‖xB - xA‖ ≤ D) :
    f xB ≤ f xA + ‖grad xA‖ * D + Lf / 2 * D ^ 2 := by
  have hUpper := hSmooth xA xB
  have hInner : @inner ℝ V _ (grad xA) (xB - xA) ≤ ‖grad xA‖ * D := by
    calc @inner ℝ V _ (grad xA) (xB - xA)
        ≤ ‖grad xA‖ * ‖xB - xA‖ := real_inner_le_norm _ _
      _ ≤ ‖grad xA‖ * D := mul_le_mul_of_nonneg_left hDist (norm_nonneg _)
  -- bound the quadratic term: (Lf/2)‖xB−xA‖² ≤ (Lf/2) D²
  have hQuad : Lf / 2 * ‖xB - xA‖ ^ 2 ≤ Lf / 2 * D ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sq_le_sq' (by linarith [norm_nonneg (xB - xA)]) hDist
  linarith

/-- Algebraic identity: for `a ≥ 0`, `d ≥ 0`, `Lf ≥ 0`,
`a + √(2 Lf a) D + (Lf/2) D² = (√a + √(Lf/2)·D)²`. -/
lemma transfer_algebraic_eq (a D Lf : ℝ) (ha_nonneg : 0 ≤ a) (hD_nonneg : 0 ≤ D) (hLf_nonneg : 0 ≤ Lf) :
    a + Real.sqrt (2 * Lf * a) * D + Lf / 2 * D ^ 2
      = (Real.sqrt a + Real.sqrt (Lf / 2) * D) ^ 2 := by
  have ha_sqrt_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nonneg
  have hLf2_nonneg : 0 ≤ Lf / 2 := by positivity
  have hLf2_sqrt_sq : Real.sqrt (Lf / 2) ^ 2 = Lf / 2 := Real.sq_sqrt hLf2_nonneg
  have h2Lf_a_nonneg : 0 ≤ 2 * Lf * a := by positivity
  -- Need: √(2Lf a) = √(Lf/2)·√a·2  ?  Check: (√(Lf/2)·√a·2)² = 4·(Lf/2)·a =2Lf a
  -- Indeed √(2Lf a)= 2·√(Lf/2)·√a  when Lf,a≥0.
  -- Proof: show √(2Lf a) = 2 * √(Lf/2) * √a  via squaring (both nonneg)
  have h_prod_nonneg : 0 ≤ Lf / 2 * a := by positivity
  have h_cross : Real.sqrt (2 * Lf * a) = 2 * Real.sqrt (Lf / 2) * Real.sqrt a := by
    have h1 : (2 * Real.sqrt (Lf / 2) * Real.sqrt a) ^ 2 = 2 * Lf * a := by
      have h2 : (Real.sqrt (Lf / 2) * Real.sqrt a) ^ 2 = Lf / 2 * a := by
        rw [mul_pow, Real.sq_sqrt hLf2_nonneg, Real.sq_sqrt ha_nonneg]
      calc (2 * Real.sqrt (Lf / 2) * Real.sqrt a) ^ 2
          = 4 * (Real.sqrt (Lf / 2) * Real.sqrt a) ^ 2 := by ring
        _ = 4 * (Lf / 2 * a) := by rw [h2]
        _ = 2 * Lf * a := by ring
    have h_nonneg : 0 ≤ 2 * Real.sqrt (Lf / 2) * Real.sqrt a := by positivity
    rw [← Real.sqrt_sq h_nonneg, h1]
  -- Now expand RHS
  have h_expand : (Real.sqrt a + Real.sqrt (Lf / 2) * D) ^ 2
      = Real.sqrt a ^ 2 + 2 * (Real.sqrt a * (Real.sqrt (Lf / 2) * D)) + (Real.sqrt (Lf / 2) * D) ^ 2 := by ring
  have h_cross2 : (Real.sqrt (Lf / 2) * D) ^ 2 = Lf / 2 * D ^ 2 := by
    rw [mul_pow, hLf2_sqrt_sq]
  calc a + Real.sqrt (2 * Lf * a) * D + Lf / 2 * D ^ 2
      = a + (2 * Real.sqrt (Lf / 2) * Real.sqrt a) * D + Lf / 2 * D ^ 2 := by rw [← h_cross]
    _ = Real.sqrt a ^ 2 + 2 * (Real.sqrt a * (Real.sqrt (Lf / 2) * D)) + (Real.sqrt (Lf / 2) * D) ^ 2 := by
        rw [ha_sqrt_sq, h_cross2]; ring
    _ = (Real.sqrt a + Real.sqrt (Lf / 2) * D) ^ 2 := by rw [← h_expand]

/-- Terminal objective transfer under displacement bound.

Assumes smoothness, global lower bound `fStar ≤ f(x)`, and displacement
`‖xB−xA‖ ≤ D`.  Concludes

  f(xB) − fStar ≤ ( √(f(xA)−fStar) + √(Lf/2) · D )²

allowing `f(xA)−fStar = 0` and `D = 0`.  The proof combines the smooth upper
bound, Cauchy–Schwarz, and the coercive gradient bound
`‖∇f(xA)‖² ≤ 2 Lf (f(xA)−fStar)`. -/
theorem smooth_objective_transfer {f : V → ℝ} {grad : V → V} {fStar Lf D : ℝ}
    (hLf_nonneg : 0 ≤ Lf) (hD_nonneg : 0 ≤ D)
    (hfStar_le : ∀ x : V, fStar ≤ f x)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (xA xB : V) (hDist : ‖xB - xA‖ ≤ D) :
    f xB - fStar ≤ (Real.sqrt (f xA - fStar) + Real.sqrt (Lf / 2) * D) ^ 2 := by
  -- gap nonneg
  have hGapA_nonneg : 0 ≤ f xA - fStar := by linarith [hfStar_le xA]
  -- gradient bound at xA
  have hGrad_sq := gradient_norm_sq_le (V:=V) hLf_nonneg hfStar_le hSmooth xA
  have hGrad_le_sqrt : ‖grad xA‖ ≤ Real.sqrt (2 * Lf * (f xA - fStar)) := by
    exact norm_grad_le_sqrt (V:=V) hLf_nonneg hfStar_le hSmooth xA
  -- core smooth transfer
  have hCore := smooth_transfer_core (V:=V) hLf_nonneg hD_nonneg hSmooth xA xB hDist
  -- combine: f(xB) ≤ f(xA) + ‖gA‖ D + (Lf/2) D² ≤ fStar + [gap + √(2Lf gap) D + (Lf/2) D²]
  have hle1 : f xB ≤ f xA + Real.sqrt (2 * Lf * (f xA - fStar)) * D + Lf / 2 * D ^ 2 := by
    have h1 : ‖grad xA‖ * D ≤ Real.sqrt (2 * Lf * (f xA - fStar)) * D := by
      apply mul_le_mul_of_nonneg_right hGrad_le_sqrt hD_nonneg
    linarith
  have hAlg := transfer_algebraic_eq (f xA - fStar) D Lf hGapA_nonneg hD_nonneg hLf_nonneg
  have hEq : f xA + Real.sqrt (2 * Lf * (f xA - fStar)) * D + Lf / 2 * D ^ 2
      = fStar + (f xA - fStar + Real.sqrt (2 * Lf * (f xA - fStar)) * D + Lf / 2 * D ^ 2) := by ring
  -- relate √(2Lf(fA−fStar)) to √(2Lf·gap) form used in hAlg (they match)
  have hRewrite : f xA - fStar + Real.sqrt (2 * Lf * (f xA - fStar)) * D + Lf / 2 * D ^ 2
      = (Real.sqrt (f xA - fStar) + Real.sqrt (Lf / 2) * D) ^ 2 := by
    have h1 : Real.sqrt (2 * Lf * (f xA - fStar)) = Real.sqrt (2 * Lf * (f xA - fStar)) := rfl
    -- hAlg states: a + √(2Lf a) D + Lf/2 D² = (√a + √(Lf/2) D)²
    have := hAlg
    -- need to match form: our left has √(2Lf a) * D, same as in lemma
    -- lemma's left is exactly a + √(2Lf a)*D + Lf/2 D²
    linarith
  have hFinal : f xB ≤ fStar + (Real.sqrt (f xA - fStar) + Real.sqrt (Lf / 2) * D) ^ 2 := by
    calc f xB ≤ f xA + Real.sqrt (2 * Lf * (f xA - fStar)) * D + Lf / 2 * D ^ 2 := hle1
      _ = fStar + (f xA - fStar + Real.sqrt (2 * Lf * (f xA - fStar)) * D + Lf / 2 * D ^ 2) := by ring
      _ = fStar + (Real.sqrt (f xA - fStar) + Real.sqrt (Lf / 2) * D) ^ 2 := by rw [hRewrite]
  linarith

/-- Variant with `‖xB−xA‖ ≤ D` hypothesis packaged as `D` itself: if the
displacement is at most `‖xB−xA‖`, the same bound holds with `D := ‖xB−xA‖`. -/
theorem smooth_objective_transfer_self {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}
    (hLf_nonneg : 0 ≤ Lf)
    (hfStar_le : ∀ x : V, fStar ≤ f x)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (xA xB : V) :
    f xB - fStar ≤ (Real.sqrt (f xA - fStar) + Real.sqrt (Lf / 2) * ‖xB - xA‖) ^ 2 := by
  have hD_nonneg : 0 ≤ ‖xB - xA‖ := norm_nonneg _
  exact smooth_objective_transfer hLf_nonneg hD_nonneg hfStar_le hSmooth xA xB le_rfl

/-- Monotonicity corollary: the RHS is monotone in `D` for `D ≥ 0`.  Hence any
upper bound `‖xB−xA‖ ≤ D` yields the same RHS bound. This isolates the
“allowing `D=0`” case: at `D=0` the bound is tight, `f(xB)−fStar ≤ f(xA)−fStar`
when `xB=xA`. -/
lemma transfer_RHS_mono (a Lf D₁ D₂ : ℝ) (ha_nonneg : 0 ≤ a) (hLf_nonneg : 0 ≤ Lf)
    (hD1_nonneg : 0 ≤ D₁) (hD2_nonneg : 0 ≤ D₂) (hD_le : D₁ ≤ D₂) :
    (Real.sqrt a + Real.sqrt (Lf / 2) * D₁) ^ 2 ≤ (Real.sqrt a + Real.sqrt (Lf / 2) * D₂) ^ 2 := by
  have hLf2_nonneg : 0 ≤ Lf / 2 := by positivity
  have h_sqrt_nonneg : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h_sqrtLf_nonneg : 0 ≤ Real.sqrt (Lf / 2) := Real.sqrt_nonneg _
  have h1 : Real.sqrt a + Real.sqrt (Lf / 2) * D₁ ≤ Real.sqrt a + Real.sqrt (Lf / 2) * D₂ := by
    apply add_le_add_right (mul_le_mul_of_nonneg_left hD_le h_sqrtLf_nonneg) _
  have h2 : 0 ≤ Real.sqrt a + Real.sqrt (Lf / 2) * D₁ := by positivity
  exact sq_le_sq' (by linarith) h1

/-- Interface lemma: expose `‖∇f(x)‖² ≤ 2 Lf (f(x)−f⋆)` as a standalone
declaration for downstream `NearQuadratic` modules (Transport, kappa bounds)
without importing the whole `SmoothLowerData` structure. -/
theorem convex_smooth_gradient_bound {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}
    (hLf_nonneg : 0 ≤ Lf)
    (hfStar_le : ∀ x : V, fStar ≤ f x)
    (hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2)
    (x : V) :
    ‖grad x‖ ^ 2 ≤ 2 * Lf * (f x - fStar) :=
  gradient_norm_sq_le hLf_nonneg hfStar_le hSmooth x

end Transfer

section SmoothDataStructure

/-- Bundled structure for downstream use: smoothness + lower bound + gradient field.
This is the “genuine” hypothesis package that the transfer theorems consume;
convexity is the source-faithful motivation for `hfStar_le` (global minimizer)
and is not otherwise needed for the inequalities. -/
structure ConvexSmoothData (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (grad : V → V) (fStar Lf : ℝ) : Prop where
  hLf_nonneg : 0 ≤ Lf
  hfStar_le : ∀ x : V, fStar ≤ f x
  hSmooth : ∀ x y : V, f y ≤ f x + @inner ℝ V _ (grad x) (y - x) + Lf / 2 * ‖y - x‖ ^ 2

theorem ConvexSmoothData.gradient_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}
    (h : ConvexSmoothData V f grad fStar Lf) (x : V) :
    ‖grad x‖ ^ 2 ≤ 2 * Lf * (f x - fStar) :=
  gradient_norm_sq_le h.hLf_nonneg h.hfStar_le h.hSmooth x

theorem ConvexSmoothData.objective_transfer {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ℝ} {grad : V → V} {fStar Lf D : ℝ}
    (h : ConvexSmoothData V f grad fStar Lf) (hD_nonneg : 0 ≤ D)
    (xA xB : V) (hDist : ‖xB - xA‖ ≤ D) :
    f xB - fStar ≤ (Real.sqrt (f xA - fStar) + Real.sqrt (Lf / 2) * D) ^ 2 :=
  smooth_objective_transfer h.hLf_nonneg hD_nonneg h.hfStar_le h.hSmooth xA xB hDist

/-- Convenience: the classic `Lf`-smooth descent guarantee at the gradient step
`x⁺ = x − (1/Lf)∇f(x)` for `Lf>0`: `f(x⁺) ≤ f(x) − (1/(2Lf))‖∇f(x)‖²`. -/
theorem ConvexSmoothData.descent_lemma {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ℝ} {grad : V → V} {fStar Lf : ℝ}
    (h : ConvexSmoothData V f grad fStar Lf) (hLf_pos : 0 < Lf) (x : V) :
    f (x - (1 / Lf) • grad x) ≤ f x - 1 / (2 * Lf) * ‖grad x‖ ^ 2 := by
  have hstep := smooth_gradient_step (V:=V) (f:=f) (grad:=grad) (Lf:=Lf) h.hSmooth x (1 / Lf)
  have hcalc : -(1 / Lf) * ‖grad x‖ ^ 2 + Lf / 2 * ((1 / Lf) ^ 2 * ‖grad x‖ ^ 2)
      = -(1 / (2 * Lf)) * ‖grad x‖ ^ 2 := by
    field_simp; ring
  have h1 : f (x - (1 / Lf) • grad x) ≤ f x + (-(1 / Lf) * ‖grad x‖ ^ 2 + Lf / 2 * ((1 / Lf) ^ 2 * ‖grad x‖ ^ 2)) := by
    convert hstep using 1
  have h2 : f x + (-(1 / Lf) * ‖grad x‖ ^ 2 + Lf / 2 * ((1 / Lf) ^ 2 * ‖grad x‖ ^ 2)) = f x - 1 / (2 * Lf) * ‖grad x‖ ^ 2 := by
    rw [hcalc]; ring
  linarith

end SmoothDataStructure

end NearQuadratic
