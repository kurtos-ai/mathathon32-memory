module
/-
Source fidelity note — ObjectiveTransfer (NearQuadratic / ext:thm:near terminal gap).

Mathematical source: ext:thm:near + Appendix K "Residual integration".
  0 <= Q <= L0 I on Hilbert space V, q(w)=1/2<W,Qw>, fStar=f(xStar).
  Residual estimate |f(x)-fStar-q(x-xStar)| <= eps/2 ||x-xStar||^2
  w=xN-xStar, z=p_A(Q)(x0-xStar), ||w-z||<=eps R beta, ||z||<=R pi, ||w||<=R hN.
  Theorem: |f(xN)-fStar-1/2<z,Qz>| <= eps R^2 kappa,
  kappa=1/2 hN^2 + L0 pi beta + 1/2 L0 eps0 beta^2, eps<=eps0.
  Inputs are independent estimates, not the target disguised.
  Q symmetric (self-adjoint) for sharp kappa; nonsymmetric variant also proved.
-/

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
set_option linter.unusedVariables false

open RealInnerProductSpace

namespace NearQuadratic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure QData (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : V →L[ℝ] V) (L₀ : ℝ) : Prop where
  hL₀_nonneg : 0 ≤ L₀
  hQ_nonneg : ∀ v : V, 0 ≤ @inner ℝ V _ (Q v) v
  hQ_bound : ∀ v : V, ‖Q v‖ ≤ L₀ * ‖v‖
  hQ_symm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v)

noncomputable def quadForm (Q : V →L[ℝ] V) (w : V) : ℝ :=
  (1/2 : ℝ) * @inner ℝ V _ (Q w) w

noncomputable def kappa_const (hN πA βA L₀ ε₀ : ℝ) : ℝ :=
  1/2 * hN ^ 2 + L₀ * πA * βA + 1/2 * L₀ * ε₀ * βA ^ 2

lemma kappa_const_nonneg {hN πA βA L₀ ε₀ : ℝ}
    (hL₀ : 0 ≤ L₀) (hε₀ : 0 ≤ ε₀)
    (hπ : 0 ≤ πA) (hβ : 0 ≤ βA) :
    0 ≤ kappa_const hN πA βA L₀ ε₀ := by
  unfold kappa_const; positivity

lemma inner_Q_le {Q : V →L[ℝ] V} {L₀ : ℝ}
    (hQ_bound : ∀ v : V, ‖Q v‖ ≤ L₀ * ‖v‖)
    (u v : V) : |@inner ℝ V _ (Q v) u| ≤ L₀ * ‖u‖ * ‖v‖ := by
  calc |@inner ℝ V _ (Q v) u| ≤ ‖Q v‖ * ‖u‖ := abs_real_inner_le_norm _ _
    _ ≤ L₀ * ‖v‖ * ‖u‖ := mul_le_mul_of_nonneg_right (hQ_bound v) (norm_nonneg _)
    _ = L₀ * ‖u‖ * ‖v‖ := by ring

-- Symmetric decomposition: W=Z+D, <W,QW>-<Z,QZ>=2<Z,QD>+<D,QD> when Q symmetric
lemma quad_diff_eq {Q : V →L[ℝ] V}
    (hQ_symm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (w z : V) :
    @inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z
    = 2 * @inner ℝ V _ (Q z) (w - z) + @inner ℝ V _ (Q (w - z)) (w - z) := by
  set d := w - z
  have hw : w = z + d := by simp [d]
  -- Expand Q(z+d) = Qz+Qd, then inner products
  have hQd : Q (z + d) = Q z + Q d := map_add Q z d
  have expand : @inner ℝ V _ (Q (z + d)) (z + d)
      = @inner ℝ V _ (Q z) z + @inner ℝ V _ (Q z) d
        + @inner ℝ V _ (Q d) z + @inner ℝ V _ (Q d) d := by
    rw [hQd]
    simp only [inner_add_left, inner_add_right]
    ring
  have symm_eq : @inner ℝ V _ (Q d) z = @inner ℝ V _ (Q z) d := by
    calc @inner ℝ V _ (Q d) z = @inner ℝ V _ d (Q z) := hQ_symm d z
      _ = @inner ℝ V _ (Q z) d := (real_inner_comm _ _).symm
  have h1 : @inner ℝ V _ (Q w) w = @inner ℝ V _ (Q (z + d)) (z + d) := by rw [← hw]
  rw [h1, expand, symm_eq]; ring

lemma quadForm_diff_le {Q : V →L[ℝ] V} {L₀ : ℝ}
    (hQ_bound : ∀ v : V, ‖Q v‖ ≤ L₀ * ‖v‖)
    (hQ_symm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (_hL₀ : 0 ≤ L₀)
    (w z : V) :
    |quadForm Q w - quadForm Q z| ≤ L₀ * ‖z‖ * ‖w - z‖ + 1/2 * L₀ * ‖w - z‖ ^ 2 := by
  unfold quadForm
  have h_eq : (1/2 : ℝ) * @inner ℝ V _ (Q w) w - 1/2 * @inner ℝ V _ (Q z) z
      = 1/2 * (@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z) := by ring
  rw [h_eq, quad_diff_eq hQ_symm w z]
  have h1 : (1/2 : ℝ) * (2 * @inner ℝ V _ (Q z) (w - z) + @inner ℝ V _ (Q (w - z)) (w - z))
      = @inner ℝ V _ (Q z) (w - z) + 1/2 * @inner ℝ V _ (Q (w - z)) (w - z) := by ring
  rw [h1]
  have bnd1 : |@inner ℝ V _ (Q z) (w - z)| ≤ L₀ * ‖w - z‖ * ‖z‖ :=
    inner_Q_le hQ_bound (w - z) z
  have bnd2 : |@inner ℝ V _ (Q (w - z)) (w - z)| ≤ L₀ * ‖w - z‖ ^ 2 := by
    calc |@inner ℝ V _ (Q (w - z)) (w - z)| ≤ ‖Q (w - z)‖ * ‖w - z‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ L₀ * ‖w - z‖ * ‖w - z‖ :=
          mul_le_mul_of_nonneg_right (hQ_bound (w - z)) (norm_nonneg _)
      _ = L₀ * ‖w - z‖ ^ 2 := by ring
  have h_half_pos : (0:ℝ) ≤ 1/2 := by norm_num
  have triangle : |@inner ℝ V _ (Q z) (w - z) + 1/2 * @inner ℝ V _ (Q (w - z)) (w - z)|
      ≤ |@inner ℝ V _ (Q z) (w - z)| + 1/2 * |@inner ℝ V _ (Q (w - z)) (w - z)| := by
    calc |@inner ℝ V _ (Q z) (w - z) + 1/2 * @inner ℝ V _ (Q (w - z)) (w - z)|
        ≤ |@inner ℝ V _ (Q z) (w - z)| + |1/2 * @inner ℝ V _ (Q (w - z)) (w - z)| :=
          abs_add_le _ _
      _ = |@inner ℝ V _ (Q z) (w - z)| + 1/2 * |@inner ℝ V _ (Q (w - z)) (w - z)| := by
          rw [abs_mul, abs_of_nonneg h_half_pos]
  have h_step2 : |@inner ℝ V _ (Q z) (w - z)| + 1/2 * |@inner ℝ V _ (Q (w - z)) (w - z)|
      ≤ L₀ * ‖w - z‖ * ‖z‖ + 1/2 * (L₀ * ‖w - z‖ ^ 2) := by
    apply add_le_add bnd1
    exact mul_le_mul_of_nonneg_left bnd2 h_half_pos
  calc |@inner ℝ V _ (Q z) (w - z) + 1/2 * @inner ℝ V _ (Q (w - z)) (w - z)|
      ≤ |@inner ℝ V _ (Q z) (w - z)| + 1/2 * |@inner ℝ V _ (Q (w - z)) (w - z)| := triangle
    _ ≤ L₀ * ‖w - z‖ * ‖z‖ + 1/2 * (L₀ * ‖w - z‖ ^ 2) := h_step2
    _ = L₀ * ‖z‖ * ‖w - z‖ + 1/2 * L₀ * ‖w - z‖ ^ 2 := by ring

lemma quadForm_transfer_aux {Q : V →L[ℝ] V} {L₀ ε R πA βA : ℝ}
    (hQ_bound : ∀ v : V, ‖Q v‖ ≤ L₀ * ‖v‖)
    (hQ_symm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (hL₀ : 0 ≤ L₀) (hR : 0 ≤ R) (hπ : 0 ≤ πA)
    {w z : V} (hwz : ‖w - z‖ ≤ ε * R * βA) (hz : ‖z‖ ≤ R * πA) :
    |quadForm Q w - quadForm Q z| ≤ ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2 := by
  have h_main := quadForm_diff_le hQ_bound hQ_symm hL₀ w z
  have h1 : L₀ * ‖z‖ * ‖w - z‖ ≤ L₀ * (R * πA) * (ε * R * βA) := by
    have h_nn : 0 ≤ L₀ * (R * πA) := mul_nonneg hL₀ (mul_nonneg hR hπ)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hz hL₀) hwz (norm_nonneg _) h_nn
  have h2 : 1/2 * L₀ * ‖w - z‖ ^ 2 ≤ 1/2 * L₀ * (ε * R * βA) ^ 2 := by
    have h_pow : ‖w - z‖ ^ 2 ≤ (ε * R * βA) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hwz 2
    have h_nn : (0:ℝ) ≤ 1/2 * L₀ := mul_nonneg (by norm_num) hL₀
    exact mul_le_mul_of_nonneg_left h_pow h_nn
  have h_combine : L₀ * ‖z‖ * ‖w - z‖ + 1/2 * L₀ * ‖w - z‖ ^ 2
      ≤ L₀ * (R * πA) * (ε * R * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2 := add_le_add h1 h2
  have h_algebra : L₀ * (R * πA) * (ε * R * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2
      = ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2 := by ring
  linarith

lemma quadForm_transfer_le_kappa_part {Q : V →L[ℝ] V} {L₀ ε ε₀ R πA βA : ℝ}
    (hQ_bound : ∀ v : V, ‖Q v‖ ≤ L₀ * ‖v‖)
    (hQ_symm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (hL₀ : 0 ≤ L₀) (hε : 0 ≤ ε) (hε₀ : 0 ≤ ε₀) (hR : 0 ≤ R) (hπ : 0 ≤ πA)
    (hε_le : ε ≤ ε₀)
    {w z : V} (hwz : ‖w - z‖ ≤ ε * R * βA) (hz : ‖z‖ ≤ R * πA) :
    |quadForm Q w - quadForm Q z| ≤ ε * R ^ 2 * (L₀ * πA * βA + 1/2 * L₀ * ε₀ * βA ^ 2) := by
  have h_aux : |quadForm Q w - quadForm Q z| ≤ ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2 :=
    quadForm_transfer_aux (L₀ := L₀) (ε := ε) (R := R) (πA := πA) (βA := βA)
      hQ_bound hQ_symm hL₀ hR hπ hwz hz
  have h_sq : 1/2 * L₀ * (ε * R * βA) ^ 2 ≤ ε * R ^ 2 * (1/2 * L₀ * ε₀ * βA ^ 2) := by
    have hε_sq : (ε * R * βA) ^ 2 = ε ^ 2 * R ^ 2 * βA ^ 2 := by ring
    have h_target : ε * R ^ 2 * (1/2 * L₀ * ε₀ * βA ^ 2) = 1/2 * L₀ * ε₀ * (ε * R ^ 2 * βA ^ 2) := by ring
    have h_this : 1/2 * L₀ * (ε * R * βA) ^ 2 = 1/2 * L₀ * (ε ^ 2 * R ^ 2 * βA ^ 2) := by
      rw [hε_sq]
    rw [h_this, h_target]
    have hε2 : ε ^ 2 ≤ ε * ε₀ := by
      have : ε ^ 2 = ε * ε := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hε_le hε
    have h_ineq : ε ^ 2 * R ^ 2 * βA ^ 2 ≤ ε * ε₀ * R ^ 2 * βA ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_right hε2 (sq_nonneg _)
    calc 1/2 * L₀ * (ε ^ 2 * R ^ 2 * βA ^ 2)
        ≤ 1/2 * L₀ * (ε * ε₀ * R ^ 2 * βA ^ 2) :=
          mul_le_mul_of_nonneg_left h_ineq (by positivity)
      _ = 1/2 * L₀ * ε₀ * (ε * R ^ 2 * βA ^ 2) := by ring
  have h_first : ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2
      ≤ ε * R ^ 2 * (L₀ * πA * βA) + ε * R ^ 2 * (1/2 * L₀ * ε₀ * βA ^ 2) :=
    add_le_add_right h_sq _
  have h_factor : ε * R ^ 2 * (L₀ * πA * βA) + ε * R ^ 2 * (1/2 * L₀ * ε₀ * βA ^ 2)
      = ε * R ^ 2 * (L₀ * πA * βA + 1/2 * L₀ * ε₀ * βA ^ 2) := by ring
  linarith

/-- Terminal objective-gap transfer to quadratic response (source kappa). -/
theorem terminal_gap_transfer
    {Q : V →L[ℝ] V} {L₀ ε ε₀ R hN πA βA fStar : ℝ}
    (hQ : QData V Q L₀)
    (hε : 0 ≤ ε) (hε₀ : 0 ≤ ε₀) (hε_le : ε ≤ ε₀)
    (hR : 0 ≤ R) (hπ : 0 ≤ πA)
    {w z : V} {f_at_w : ℝ}
    (h_residual : |f_at_w - fStar - quadForm Q w| ≤ ε / 2 * ‖w‖ ^ 2)
    (h_norm_w : ‖w‖ ≤ R * hN)
    (h_displacement : ‖w - z‖ ≤ ε * R * βA)
    (h_norm_z : ‖z‖ ≤ R * πA) :
    |f_at_w - fStar - quadForm Q z| ≤ ε * R ^ 2 * kappa_const hN πA βA L₀ ε₀ := by
  have h_split : f_at_w - fStar - quadForm Q z
      = (f_at_w - fStar - quadForm Q w) + (quadForm Q w - quadForm Q z) := by ring
  rw [h_split]
  have h_res_bound : |f_at_w - fStar - quadForm Q w| ≤ ε * R ^ 2 * (1/2 * hN ^ 2) := by
    have h1 : ε / 2 * ‖w‖ ^ 2 ≤ ε / 2 * (R * hN) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) h_norm_w 2
    have h2 : ε / 2 * (R * hN) ^ 2 = ε * R ^ 2 * (1/2 * hN ^ 2) := by ring
    linarith
  have h_quad_bound : |quadForm Q w - quadForm Q z|
      ≤ ε * R ^ 2 * (L₀ * πA * βA + 1/2 * L₀ * ε₀ * βA ^ 2) :=
    quadForm_transfer_le_kappa_part hQ.hQ_bound hQ.hQ_symm hQ.hL₀_nonneg hε hε₀ hR hπ hε_le
      h_displacement h_norm_z
  have h_kappa_eq : ε * R ^ 2 * (1/2 * hN ^ 2) + ε * R ^ 2 * (L₀ * πA * βA + 1/2 * L₀ * ε₀ * βA ^ 2)
      = ε * R ^ 2 * kappa_const hN πA βA L₀ ε₀ := by unfold kappa_const; ring
  calc |(f_at_w - fStar - quadForm Q w) + (quadForm Q w - quadForm Q z)|
      ≤ |f_at_w - fStar - quadForm Q w| + |quadForm Q w - quadForm Q z| := abs_add_le _ _
    _ ≤ ε * R ^ 2 * (1/2 * hN ^ 2) + ε * R ^ 2 * (L₀ * πA * βA + 1/2 * L₀ * ε₀ * βA ^ 2) :=
        add_le_add h_res_bound h_quad_bound
    _ = ε * R ^ 2 * kappa_const hN πA βA L₀ ε₀ := h_kappa_eq

/-- Sharper intermediate bound without weakening epsilon^2 to epsilon*epsilon0. -/
theorem terminal_gap_transfer_sharp
    {Q : V →L[ℝ] V} {L₀ ε R hN πA βA fStar : ℝ}
    (hQ : QData V Q L₀)
    (hε : 0 ≤ ε) (hR : 0 ≤ R) (hπ : 0 ≤ πA)
    {w z : V} {f_at_w : ℝ}
    (h_residual : |f_at_w - fStar - quadForm Q w| ≤ ε / 2 * ‖w‖ ^ 2)
    (h_norm_w : ‖w‖ ≤ R * hN)
    (h_displacement : ‖w - z‖ ≤ ε * R * βA)
    (h_norm_z : ‖z‖ ≤ R * πA) :
    |f_at_w - fStar - quadForm Q z|
      ≤ ε * R ^ 2 * (1/2 * hN ^ 2)
        + ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2 := by
  have h_split : f_at_w - fStar - quadForm Q z
      = (f_at_w - fStar - quadForm Q w) + (quadForm Q w - quadForm Q z) := by ring
  rw [h_split]
  have h_res_bound : |f_at_w - fStar - quadForm Q w| ≤ ε * R ^ 2 * (1/2 * hN ^ 2) := by
    have h1 : ε / 2 * ‖w‖ ^ 2 ≤ ε / 2 * (R * hN) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) h_norm_w 2
    have h2 : ε / 2 * (R * hN) ^ 2 = ε * R ^ 2 * (1/2 * hN ^ 2) := by ring
    linarith
  have h_quad_bound : |quadForm Q w - quadForm Q z|
      ≤ ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2 :=
    quadForm_transfer_aux (L₀ := L₀) (ε := ε) (R := R) (πA := πA) (βA := βA) hQ.hQ_bound hQ.hQ_symm hQ.hL₀_nonneg hR hπ h_displacement h_norm_z
  calc |(f_at_w - fStar - quadForm Q w) + (quadForm Q w - quadForm Q z)|
      ≤ |f_at_w - fStar - quadForm Q w| + |quadForm Q w - quadForm Q z| := abs_add_le _ _
    _ ≤ ε * R ^ 2 * (1/2 * hN ^ 2) + (ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2) := by
        linarith
    _ = ε * R ^ 2 * (1/2 * hN ^ 2) + ε * R ^ 2 * (L₀ * πA * βA) + 1/2 * L₀ * (ε * R * βA) ^ 2 := by ring

/-- Nonsymmetric variant: without self-adjointness. -/
theorem quadForm_diff_le_nonsymm {Q : V →L[ℝ] V} {L₀ : ℝ}
    (hQ_bound : ∀ v : V, ‖Q v‖ ≤ L₀ * ‖v‖)
    (hL₀ : 0 ≤ L₀)
    (w z : V) :
    |quadForm Q w - quadForm Q z| ≤ L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖z‖ * ‖w - z‖ := by
  -- Weaker bound via crude triangle: |<W,QW>-<Z,QZ>| <= L0||W-Z||(||W||+||Z||)
  -- quadForm diff = 1/2|...| <= L0||W-Z||(||W||+||Z||)/2
  -- For the interface we prove a valid (loose) upper bound.
  have h_split : (1/2 : ℝ) * @inner ℝ V _ (Q w) w - 1/2 * @inner ℝ V _ (Q z) z
      = 1/2 * (@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z) := by ring
  have bnd : |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z|
      ≤ L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖ := by
    have h_a_eq : @inner ℝ V _ (Q w) w - @inner ℝ V _ (Q w) z
        = @inner ℝ V _ (Q w) (w - z) := by rw [← inner_sub_right]
    have h_b_eq : @inner ℝ V _ (Q w) z - @inner ℝ V _ (Q z) z
        = @inner ℝ V _ (Q w - Q z) z := by rw [inner_sub_left]
    have h_Qsub : Q w - Q z = Q (w - z) := by
      have h := Q.map_sub w z; exact h.symm
    have bnd_a : |@inner ℝ V _ (Q w) (w - z)| ≤ L₀ * ‖w‖ * ‖w - z‖ := by
      calc |@inner ℝ V _ (Q w) (w - z)| ≤ ‖Q w‖ * ‖w - z‖ := abs_real_inner_le_norm _ _
        _ ≤ L₀ * ‖w‖ * ‖w - z‖ := mul_le_mul_of_nonneg_right (hQ_bound w) (norm_nonneg _)
    have bnd_b : |@inner ℝ V _ (Q (w - z)) z| ≤ L₀ * ‖w - z‖ * ‖z‖ := by
      calc |@inner ℝ V _ (Q (w - z)) z| ≤ ‖Q (w - z)‖ * ‖z‖ := abs_real_inner_le_norm _ _
        _ ≤ L₀ * ‖w - z‖ * ‖z‖ := mul_le_mul_of_nonneg_right (hQ_bound (w - z)) (norm_nonneg _)
    have tri : |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z|
        ≤ |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q w) z| + |@inner ℝ V _ (Q w) z - @inner ℝ V _ (Q z) z| := by
      have : @inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z
          = (@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q w) z) + (@inner ℝ V _ (Q w) z - @inner ℝ V _ (Q z) z) := by ring
      rw [this]; exact abs_add_le _ _
    have h1 : |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q w) z| ≤ L₀ * ‖w‖ * ‖w - z‖ := by
      rw [h_a_eq]; exact bnd_a
    have h2 : |@inner ℝ V _ (Q w) z - @inner ℝ V _ (Q z) z| ≤ L₀ * ‖w - z‖ * ‖z‖ := by
      rw [h_b_eq, h_Qsub]; exact bnd_b
    calc |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z|
        ≤ |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q w) z| + |@inner ℝ V _ (Q w) z - @inner ℝ V _ (Q z) z| := tri
      _ ≤ L₀ * ‖w‖ * ‖w - z‖ + L₀ * ‖w - z‖ * ‖z‖ := add_le_add h1 h2
      _ = L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖ := by ring
  have h_half : |1/2 * (@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z)|
      = 1/2 * |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/2)]
  have h_le : 1/2 * |@inner ℝ V _ (Q w) w - @inner ℝ V _ (Q z) z|
      ≤ 1/2 * (L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖) :=
    mul_le_mul_of_nonneg_left bnd (by positivity)
  have h_final : (1/2 : ℝ) * (L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖)
      ≤ L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖z‖ * ‖w - z‖ := by
    have h_nn : 0 ≤ L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖ := by positivity
    have h_half_le : (1/2 : ℝ) * (L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖) ≤ L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖ := by
      calc (1/2 : ℝ) * (L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖)
          ≤ 1 * (L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖) :=
            mul_le_mul_of_nonneg_right (by norm_num) h_nn
        _ = L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖ := by ring
    have h_rw : L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖ = L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖z‖ * ‖w - z‖ := by ring
    calc (1/2 : ℝ) * (L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖)
        ≤ L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖w - z‖ * ‖z‖ := h_half_le
      _ = L₀ * ‖w - z‖ * ‖w‖ + L₀ * ‖z‖ * ‖w - z‖ := h_rw
  unfold quadForm; rw [h_split, h_half]
  linarith

end NearQuadratic
