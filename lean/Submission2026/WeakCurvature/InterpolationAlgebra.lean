module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace WeakCurvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def interpResidual (c : ℝ) (f_i f_j : ℝ) (x_i x_j g_i g_j : E) : ℝ :=
  f_i - f_j - @inner ℝ E _ g_j (x_i - x_j) - (1/2 : ℝ) * ‖g_i - g_j‖ ^ 2
    + c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2

theorem interpResidual_self (c : ℝ) (f : ℝ) (x g : E) :
    interpResidual c f f x x g g = 0 := by
  unfold interpResidual
  simp [sub_self]

theorem norm_sub_sub_sq (x_i x_j g_i g_j : E) :
    ‖x_i - x_j - (g_i - g_j)‖ ^ 2 =
    ‖x_i - x_j‖ ^ 2 - 2 * @inner ℝ E _ (x_i - x_j) (g_i - g_j) + ‖g_i - g_j‖ ^ 2 := by
  have h := @norm_sub_sq_real E _ _ (x_i - x_j) (g_i - g_j)
  simpa using h

theorem interpResidual_expand (c : ℝ) (f_i f_j : ℝ) (x_i x_j g_i g_j : E) :
    interpResidual c f_i f_j x_i x_j g_i g_j =
    f_i - f_j - @inner ℝ E _ g_j (x_i - x_j)
    + c * ‖x_i - x_j‖ ^ 2
    - 2 * c * @inner ℝ E _ (x_i - x_j) (g_i - g_j)
    + (c - 1/2) * ‖g_i - g_j‖ ^ 2 := by
  unfold interpResidual
  have hsq := norm_sub_sub_sq (E:=E) x_i x_j g_i g_j
  calc f_i - f_j - @inner ℝ E _ g_j (x_i - x_j) - 1 / 2 * ‖g_i - g_j‖ ^ 2
        + c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2
      = f_i - f_j - @inner ℝ E _ g_j (x_i - x_j) - 1 / 2 * ‖g_i - g_j‖ ^ 2
        + c * (‖x_i - x_j‖ ^ 2 - 2 * @inner ℝ E _ (x_i - x_j) (g_i - g_j) + ‖g_i - g_j‖ ^ 2) := by
          rw [hsq]
      _ = f_i - f_j - @inner ℝ E _ g_j (x_i - x_j)
        + c * ‖x_i - x_j‖ ^ 2 - 2 * c * @inner ℝ E _ (x_i - x_j) (g_i - g_j)
        + (c - 1 / 2) * ‖g_i - g_j‖ ^ 2 := by ring

omit [InnerProductSpace ℝ E] in
theorem norm_sub_swap (x_i x_j g_i g_j : E) :
    ‖x_j - x_i - (g_j - g_i)‖ = ‖x_i - x_j - (g_i - g_j)‖ := by
  have h : x_j - x_i - (g_j - g_i) = -(x_i - x_j - (g_i - g_j)) := by abel
  rw [h, norm_neg]

theorem norm_sub_swap_sq (x_i x_j g_i g_j : E) :
    ‖x_j - x_i - (g_j - g_i)‖ ^ 2 = ‖x_i - x_j - (g_i - g_j)‖ ^ 2 := by
  rw [norm_sub_swap]

theorem interpResidual_add_swap (c : ℝ) (f_i f_j : ℝ) (x_i x_j g_i g_j : E) :
    interpResidual c f_i f_j x_i x_j g_i g_j
    + interpResidual c f_j f_i x_j x_i g_j g_i
    = @inner ℝ E _ (g_i - g_j) (x_i - x_j) - ‖g_i - g_j‖ ^ 2
      + 2 * c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2 := by
  unfold interpResidual
  have hswap : ‖x_j - x_i - (g_j - g_i)‖ ^ 2 = ‖x_i - x_j - (g_i - g_j)‖ ^ 2 :=
    norm_sub_swap_sq _ _ _ _
  have hnorm_rev : ‖g_j - g_i‖ = ‖g_i - g_j‖ := norm_sub_rev _ _
  have h_inner_gi_neg : @inner ℝ E _ g_i (x_j - x_i) = - @inner ℝ E _ g_i (x_i - x_j) := by
    have : x_j - x_i = -(x_i - x_j) := by abel
    rw [this, inner_neg_right]
  have h_inner_diff : @inner ℝ E _ (g_i - g_j) (x_i - x_j)
      = @inner ℝ E _ g_i (x_i - x_j) - @inner ℝ E _ g_j (x_i - x_j) := by
    rw [inner_sub_left]
  calc (f_i - f_j - @inner ℝ E _ g_j (x_i - x_j) - 1/2 * ‖g_i - g_j‖ ^ 2 + c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2)
      + (f_j - f_i - @inner ℝ E _ g_i (x_j - x_i) - 1/2 * ‖g_j - g_i‖ ^ 2 + c * ‖x_j - x_i - (g_j - g_i)‖ ^ 2)
      = - @inner ℝ E _ g_j (x_i - x_j) - @inner ℝ E _ g_i (x_j - x_i)
        - 1/2 * ‖g_i - g_j‖ ^ 2 - 1/2 * ‖g_j - g_i‖ ^ 2
        + c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2 + c * ‖x_j - x_i - (g_j - g_i)‖ ^ 2 := by ring
    _ = - @inner ℝ E _ g_j (x_i - x_j) + @inner ℝ E _ g_i (x_i - x_j)
        - ‖g_i - g_j‖ ^ 2 + 2 * c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2 := by
          rw [h_inner_gi_neg, hswap, hnorm_rev]; ring
    _ = @inner ℝ E _ (g_i - g_j) (x_i - x_j) - ‖g_i - g_j‖ ^ 2
        + 2 * c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2 := by
          rw [h_inner_diff]; ring

theorem interpResidual_sub_swap (c : ℝ) (f_i f_j : ℝ) (x_i x_j g_i g_j : E) :
    interpResidual c f_i f_j x_i x_j g_i g_j
    - interpResidual c f_j f_i x_j x_i g_j g_i
    = 2 * (f_i - f_j) - @inner ℝ E _ (g_i + g_j) (x_i - x_j) := by
  unfold interpResidual
  have hswap : ‖x_j - x_i - (g_j - g_i)‖ ^ 2 = ‖x_i - x_j - (g_i - g_j)‖ ^ 2 :=
    norm_sub_swap_sq _ _ _ _
  have hnorm_rev : ‖g_j - g_i‖ = ‖g_i - g_j‖ := norm_sub_rev _ _
  have h_inner_gi_neg : @inner ℝ E _ g_i (x_j - x_i) = - @inner ℝ E _ g_i (x_i - x_j) := by
    have : x_j - x_i = -(x_i - x_j) := by abel
    rw [this, inner_neg_right]
  have h_inner_add : @inner ℝ E _ (g_i + g_j) (x_i - x_j)
      = @inner ℝ E _ g_i (x_i - x_j) + @inner ℝ E _ g_j (x_i - x_j) := by
    rw [inner_add_left]
  have h1 : (f_i - f_j - @inner ℝ E _ g_j (x_i - x_j) - 1/2 * ‖g_i - g_j‖ ^ 2 + c * ‖x_i - x_j - (g_i - g_j)‖ ^ 2)
      - (f_j - f_i - @inner ℝ E _ g_i (x_j - x_i) - 1/2 * ‖g_j - g_i‖ ^ 2 + c * ‖x_j - x_i - (g_j - g_i)‖ ^ 2)
      = 2 * (f_i - f_j) - @inner ℝ E _ g_j (x_i - x_j) + @inner ℝ E _ g_i (x_j - x_i) := by
          rw [hswap, hnorm_rev]; ring
  rw [h1, h_inner_gi_neg]
  calc 2 * (f_i - f_j) - @inner ℝ E _ g_j (x_i - x_j) + -@inner ℝ E _ g_i (x_i - x_j)
      = 2 * (f_i - f_j) - (@inner ℝ E _ g_i (x_i - x_j) + @inner ℝ E _ g_j (x_i - x_j)) := by ring
    _ = 2 * (f_i - f_j) - @inner ℝ E _ (g_i + g_j) (x_i - x_j) := by rw [h_inner_add]

theorem weighted_pair_N1 (c t₀ t₁ : ℝ) (f₀ f₁ : ℝ) (x₀ x₁ g₀ g₁ : E) :
    t₁ * interpResidual c f₀ f₁ x₀ x₁ g₀ g₁
    + (t₁ - t₀) * interpResidual c f₁ f₀ x₁ x₀ g₁ g₀
    = t₀ * (f₀ - f₁)
      + t₁ * @inner ℝ E _ g₁ (x₁ - x₀)
      - (t₁ - t₀) * @inner ℝ E _ g₀ (x₁ - x₀)
      + (2 * t₁ - t₀) * (- (1/2) * ‖g₀ - g₁‖ ^ 2 + c * ‖x₀ - x₁ - (g₀ - g₁)‖ ^ 2) := by
  unfold interpResidual
  have h1 : x₀ - x₁ = -(x₁ - x₀) := by abel
  have hnorm_g : ‖g₀ - g₁‖ = ‖g₁ - g₀‖ := norm_sub_rev _ _
  have hnorm_g_sq : ‖g₀ - g₁‖ ^ 2 = ‖g₁ - g₀‖ ^ 2 := by rw [hnorm_g]
  have hnorm_xg : ‖x₀ - x₁ - (g₀ - g₁)‖ = ‖x₁ - x₀ - (g₁ - g₀)‖ := by
    have : x₀ - x₁ - (g₀ - g₁) = -(x₁ - x₀ - (g₁ - g₀)) := by abel
    rw [this, norm_neg]
  have hnorm_xg_sq : ‖x₀ - x₁ - (g₀ - g₁)‖ ^ 2 = ‖x₁ - x₀ - (g₁ - g₀)‖ ^ 2 := by rw [hnorm_xg]
  have hinner0 : @inner ℝ E _ g₁ (x₀ - x₁) = - @inner ℝ E _ g₁ (x₁ - x₀) := by
    rw [h1, inner_neg_right]
  rw [hinner0, hnorm_g_sq, hnorm_xg_sq]
  ring

theorem weighted_pair_N1_telescope (c t₀ t₁ : ℝ) (f₀ f₁ : ℝ) (x₀ x₁ g₀ g₁ : E) :
    t₁ * interpResidual c f₀ f₁ x₀ x₁ g₀ g₁
    + (t₁ - t₀) * interpResidual c f₁ f₀ x₁ x₀ g₁ g₀
    - t₀ * (f₀ - f₁)
    = t₁ * @inner ℝ E _ g₁ (x₁ - x₀)
      - (t₁ - t₀) * @inner ℝ E _ g₀ (x₁ - x₀)
      + (2 * t₁ - t₀) * (- (1/2) * ‖g₀ - g₁‖ ^ 2 + c * ‖x₀ - x₁ - (g₀ - g₁)‖ ^ 2) := by
  have h := weighted_pair_N1 (E:=E) c t₀ t₁ f₀ f₁ x₀ x₁ g₀ g₁
  linarith

theorem objective_split (f₀ f₁ f_star g₁normSq ν : ℝ) :
    f₀ - f_star - g₁normSq / ν
    = (f₁ - f_star - (1/2) * g₁normSq) + (f₀ - f₁ - g₁normSq / ν + (1/2) * g₁normSq) := by
  ring

theorem certificate_N1_rearrangement (c t₀ t₁ ν : ℝ) (f₀ f₁ f_star : ℝ)
    (x₀ x₁ g₀ g₁ : E) :
    (f₀ - f_star - ‖g₁‖ ^ 2 / ν)
    - (f₁ - f_star - (1/2) * ‖g₁‖ ^ 2)
    - (t₁ * interpResidual c f₀ f₁ x₀ x₁ g₀ g₁
       + (t₁ - t₀) * interpResidual c f₁ f₀ x₁ x₀ g₁ g₀)
    = (f₀ - f₁ - ‖g₁‖ ^ 2 / ν + (1/2) * ‖g₁‖ ^ 2)
      - t₀ * (f₀ - f₁)
      - t₁ * @inner ℝ E _ g₁ (x₁ - x₀)
      + (t₁ - t₀) * @inner ℝ E _ g₀ (x₁ - x₀)
      - (2 * t₁ - t₀) * (- (1/2) * ‖g₀ - g₁‖ ^ 2 + c * ‖x₀ - x₁ - (g₀ - g₁)‖ ^ 2) := by
  have h := weighted_pair_N1 (E:=E) c t₀ t₁ f₀ f₁ x₀ x₁ g₀ g₁
  linarith

theorem certificate_N1_t0_one (c t₁ ν : ℝ) (f₀ f₁ f_star : ℝ)
    (x₀ x₁ g₀ g₁ : E) :
    (f₀ - f_star - ‖g₁‖ ^ 2 / ν)
    - (f₁ - f_star - (1/2) * ‖g₁‖ ^ 2)
    - (t₁ * interpResidual c f₀ f₁ x₀ x₁ g₀ g₁
       + (t₁ - 1) * interpResidual c f₁ f₀ x₁ x₀ g₁ g₀)
    = - ‖g₁‖ ^ 2 / ν + (1/2) * ‖g₁‖ ^ 2
      - t₁ * @inner ℝ E _ g₁ (x₁ - x₀)
      + (t₁ - 1) * @inner ℝ E _ g₀ (x₁ - x₀)
      - (2 * t₁ - 1) * (- (1/2) * ‖g₀ - g₁‖ ^ 2 + c * ‖x₀ - x₁ - (g₀ - g₁)‖ ^ 2) := by
  have h := certificate_N1_rearrangement (E:=E) c 1 t₁ ν f₀ f₁ f_star x₀ x₁ g₀ g₁
  have h2 : (f₀ - f₁ - ‖g₁‖ ^ 2 / ν + 1 / 2 * ‖g₁‖ ^ 2) - 1 * (f₀ - f₁)
      = -‖g₁‖ ^ 2 / ν + 1 / 2 * ‖g₁‖ ^ 2 := by ring
  linarith

#print axioms interpResidual
#print axioms interpResidual_self
#print axioms norm_sub_sub_sq
#print axioms interpResidual_expand
#print axioms norm_sub_swap
#print axioms norm_sub_swap_sq
#print axioms interpResidual_add_swap
#print axioms interpResidual_sub_swap
#print axioms weighted_pair_N1
#print axioms weighted_pair_N1_telescope
#print axioms objective_split
#print axioms certificate_N1_rearrangement
#print axioms certificate_N1_t0_one

end WeakCurvature
