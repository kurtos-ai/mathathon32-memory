module
public import Continuation.SmoothDualCore

@[expose] public section

open EuclideanSpace

noncomputable section

namespace SmoothDual

variable {d n : ℕ} [NeZero n] {L : ℝ}
variable (x : Fin n → E d) (g : Fin n → E d) (f : Fin n → ℝ)

-- Target 1 definition exactly as in spec
noncomputable def F_conj (p : E d) : ℝ :=
  sSup { y : ℝ | ∃ u : E d, y = @inner ℝ (E d) _ u p - H (x:=x) (g:=g) (f:=f) L u }

-- TARGET 1: completed-square global bound, no coercivity
lemma F_conj_bddAbove (hL : 0 < L) (p : E d) :
    BddAbove { y : ℝ | ∃ u : E d, y = @inner ℝ (E d) _ u p - H (x:=x) (g:=g) (f:=f) L u } := by
  have hn : 0 < n := Nat.pos_of_neZero n
  let i0 : Fin n := ⟨0, hn⟩
  -- Explicit upper bound as required
  refine ⟨f i0 + @inner ℝ (E d) _ (p - x i0) (g i0) + L / 2 * ‖p - x i0‖ ^ 2, ?_⟩
  intro y hy
  obtain ⟨u, rfl⟩ := hy
  -- Use H_ge_Hi and Hi_eq to get lower bound on H u
  have hHi_eq : Hi (x:=x) (g:=g) (f:=f) L i0 u = @inner ℝ (E d) _ (x i0) u - f i0 + 1 / (2 * L) * ‖u - g i0‖ ^ 2 :=
    Hi_eq (x:=x) (g:=g) (f:=f) (L:=L) i0 u
  have hHge : H (x:=x) (g:=g) (f:=f) L u ≥ @inner ℝ (E d) _ (x i0) u - f i0 + 1 / (2 * L) * ‖u - g i0‖ ^ 2 := by
    have h1 : Hi (x:=x) (g:=g) (f:=f) L i0 u ≤ H (x:=x) (g:=g) (f:=f) L u :=
      H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) u i0
    linarith [hHi_eq]
  -- The key completed-square equality
  have completed_square_eq :
      ‖u - g i0 - L • (p - x i0)‖ ^ 2 =
        ‖u - g i0‖ ^ 2 - 2 * L * @inner ℝ (E d) _ (u - g i0) (p - x i0) + L ^ 2 * ‖p - x i0‖ ^ 2 := by
    have h_norm_sub : ‖u - g i0 - L • (p - x i0)‖ ^ 2 =
        ‖u - g i0‖ ^ 2 - 2 * @inner ℝ (E d) _ (u - g i0) (L • (p - x i0)) + ‖L • (p - x i0)‖ ^ 2 := by
      rw [norm_sub_sq_real]
    have h_inner_smul : @inner ℝ (E d) _ (u - g i0) (L • (p - x i0)) = L * @inner ℝ (E d) _ (u - g i0) (p - x i0) := by
      rw [real_inner_smul_right]
    have h_norm_smul : ‖L • (p - x i0)‖ ^ 2 = L ^ 2 * ‖p - x i0‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc ‖u - g i0 - L • (p - x i0)‖ ^ 2
        = ‖u - g i0‖ ^ 2 - 2 * @inner ℝ (E d) _ (u - g i0) (L • (p - x i0)) + ‖L • (p - x i0)‖ ^ 2 := by rw [h_norm_sub]
      _ = ‖u - g i0‖ ^ 2 - 2 * (L * @inner ℝ (E d) _ (u - g i0) (p - x i0)) + L ^ 2 * ‖p - x i0‖ ^ 2 := by rw [h_inner_smul, h_norm_smul]
      _ = ‖u - g i0‖ ^ 2 - 2 * L * @inner ℝ (E d) _ (u - g i0) (p - x i0) + L ^ 2 * ‖p - x i0‖ ^ 2 := by ring
  have h_norm_nonneg : 0 ≤ ‖u - g i0 - L • (p - x i0)‖ ^ 2 := sq_nonneg _
  -- Derive the crucial inner bound from nonnegativity
  have h_inner_bound : @inner ℝ (E d) _ (u - g i0) (p - x i0) - 1 / (2 * L) * ‖u - g i0‖ ^ 2 ≤ L / 2 * ‖p - x i0‖ ^ 2 := by
    have h2Lpos : 0 < 2 * L := by linarith
    have h_norm_ge : ‖u - g i0‖ ^ 2 - 2 * L * @inner ℝ (E d) _ (u - g i0) (p - x i0) + L ^ 2 * ‖p - x i0‖ ^ 2 ≥ 0 := by
      linarith [h_norm_nonneg, completed_square_eq]
    have h1 : 2 * L * @inner ℝ (E d) _ (u - g i0) (p - x i0) ≤ ‖u - g i0‖ ^ 2 + L ^ 2 * ‖p - x i0‖ ^ 2 := by linarith
    have h2 : @inner ℝ (E d) _ (u - g i0) (p - x i0) ≤ (‖u - g i0‖ ^ 2 + L ^ 2 * ‖p - x i0‖ ^ 2) / (2 * L) := by
      rw [le_div_iff₀ h2Lpos]
      linarith
    have h3 : (‖u - g i0‖ ^ 2 + L ^ 2 * ‖p - x i0‖ ^ 2) / (2 * L) - 1 / (2 * L) * ‖u - g i0‖ ^ 2 = L / 2 * ‖p - x i0‖ ^ 2 := by
      have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL
      field_simp
      ring
    linarith
  -- Combine to get final inequality
  have h_main : @inner ℝ (E d) _ u p - H (x:=x) (g:=g) (f:=f) L u ≤
      f i0 + @inner ℝ (E d) _ (p - x i0) (g i0) + L / 2 * ‖p - x i0‖ ^ 2 := by
    have h1 : @inner ℝ (E d) _ u p - H (x:=x) (g:=g) (f:=f) L u ≤
        @inner ℝ (E d) _ u p - (@inner ℝ (E d) _ (x i0) u - f i0 + 1 / (2 * L) * ‖u - g i0‖ ^ 2) := by linarith
    have h2 : @inner ℝ (E d) _ u p - (@inner ℝ (E d) _ (x i0) u - f i0 + 1 / (2 * L) * ‖u - g i0‖ ^ 2) =
        f i0 + (@inner ℝ (E d) _ u p - @inner ℝ (E d) _ (x i0) u) - 1 / (2 * L) * ‖u - g i0‖ ^ 2 := by ring
    have h3 : @inner ℝ (E d) _ u p - @inner ℝ (E d) _ (x i0) u = @inner ℝ (E d) _ (u - g i0) (p - x i0) + @inner ℝ (E d) _ (g i0) (p - x i0) := by
      have h_a : @inner ℝ (E d) _ u p - @inner ℝ (E d) _ (x i0) u = @inner ℝ (E d) _ u p - @inner ℝ (E d) _ u (x i0) := by
        rw [real_inner_comm (x i0) u]
      have h_b : @inner ℝ (E d) _ u p - @inner ℝ (E d) _ u (x i0) = @inner ℝ (E d) _ u (p - x i0) := by
        rw [← inner_sub_right (𝕜:=ℝ) (x:=u) (y:=p) (z:=x i0)]
      have h_c : @inner ℝ (E d) _ u (p - x i0) = @inner ℝ (E d) _ (u - g i0) (p - x i0) + @inner ℝ (E d) _ (g i0) (p - x i0) := by
        have : u = u - g i0 + g i0 := by abel
        conv_lhs => rw [this]
        rw [inner_add_left]
      linarith
    have h4 : f i0 + (@inner ℝ (E d) _ (u - g i0) (p - x i0) + @inner ℝ (E d) _ (g i0) (p - x i0)) - 1 / (2 * L) * ‖u - g i0‖ ^ 2 =
        f i0 + @inner ℝ (E d) _ (g i0) (p - x i0) + (@inner ℝ (E d) _ (u - g i0) (p - x i0) - 1 / (2 * L) * ‖u - g i0‖ ^ 2) := by ring
    have h5 : @inner ℝ (E d) _ (g i0) (p - x i0) = @inner ℝ (E d) _ (p - x i0) (g i0) := real_inner_comm _ _
    linarith [h_inner_bound, h5]
  linarith

end SmoothDual

namespace SmoothDual

variable {d n : ℕ} [NeZero n] {L : ℝ}
variable (x : Fin n → E d) (g : Fin n → E d) (f : Fin n → ℝ)
-- TARGET 2: F_conj at data points
theorem F_conj_at_xi (hL : 0 < L) (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖ ^ 2 ≥ 0) (i : Fin n) : F_conj (x:=x) (g:=g) (f:=f) (L:=L) (x i) = f i := by
  have hBdd : BddAbove { y : ℝ | ∃ u : E d, y = @inner ℝ (E d) _ u (x i) - H (x:=x) (g:=g) (f:=f) L u } :=
    F_conj_bddAbove (x:=x) (g:=g) (f:=f) (L:=L) hL (x i)
  have hNe : Set.Nonempty { y : ℝ | ∃ u : E d, y = @inner ℝ (E d) _ u (x i) - H (x:=x) (g:=g) (f:=f) L u } := by
    use f i
    use g i
    have hH : H (x:=x) (g:=g) (f:=f) L (g i) = @inner ℝ (E d) _ (g i) (x i) - f i :=
      H_contact' (x:=x) (g:=g) (f:=f) (L:=L) hTHG i
    have : @inner ℝ (E d) _ (g i) (x i) - H (x:=x) (g:=g) (f:=f) L (g i) = f i := by linarith
    exact this.symm
  apply le_antisymm
  · -- sSup ≤ f i via csSup_le using Hi/H_ge_Hi upper bound
    unfold F_conj
    apply csSup_le hNe
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    have hHi_eq : Hi (x:=x) (g:=g) (f:=f) L i u = @inner ℝ (E d) _ (x i) u - f i + 1 / (2 * L) * ‖u - g i‖ ^ 2 :=
      Hi_eq (x:=x) (g:=g) (f:=f) (L:=L) i u
    have hHge : H (x:=x) (g:=g) (f:=f) L u ≥ @inner ℝ (E d) _ (x i) u - f i + 1 / (2 * L) * ‖u - g i‖ ^ 2 := by
      have h1 : Hi (x:=x) (g:=g) (f:=f) L i u ≤ H (x:=x) (g:=g) (f:=f) L u :=
        H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) u i
      linarith
    have hpos : 0 ≤ 1 / (2 * L) * ‖u - g i‖ ^ 2 := by positivity
    have hcomm : @inner ℝ (E d) _ (x i) u = @inner ℝ (E d) _ u (x i) := real_inner_comm _ _
    linarith
  · -- f i ≤ sSup via le_csSup at u = g i
    unfold F_conj
    apply le_csSup hBdd
    use g i
    have hH : H (x:=x) (g:=g) (f:=f) L (g i) = @inner ℝ (E d) _ (g i) (x i) - f i :=
      H_contact' (x:=x) (g:=g) (f:=f) (L:=L) hTHG i
    show f i = @inner ℝ (E d) _ (g i) (x i) - H (x:=x) (g:=g) (f:=f) L (g i)
    linarith

-- TARGET 3: subgradient inequality
theorem F_conj_subgradient (hL : 0 < L) (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖ ^ 2 ≥ 0) (i : Fin n) (v : E d) :
    F_conj (x:=x) (g:=g) (f:=f) (L:=L) (x i + v) ≥ f i + @inner ℝ (E d) _ (g i) v := by
  have hFi : F_conj (x:=x) (g:=g) (f:=f) (L:=L) (x i) = f i :=
    F_conj_at_xi (x:=x) (g:=g) (f:=f) (L:=L) hL hTHG i
  have hBdd : BddAbove { y : ℝ | ∃ u : E d, y = @inner ℝ (E d) _ u (x i + v) - H (x:=x) (g:=g) (f:=f) L u } :=
    F_conj_bddAbove (x:=x) (g:=g) (f:=f) (L:=L) hL (x i + v)
  have h_ge : F_conj (x:=x) (g:=g) (f:=f) (L:=L) (x i + v) ≥ @inner ℝ (E d) _ (g i) (x i + v) - H (x:=x) (g:=g) (f:=f) L (g i) := by
    unfold F_conj
    apply le_csSup hBdd
    use g i
  have hH : H (x:=x) (g:=g) (f:=f) L (g i) = @inner ℝ (E d) _ (g i) (x i) - f i :=
    H_contact' (x:=x) (g:=g) (f:=f) (L:=L) hTHG i
  have h1 : @inner ℝ (E d) _ (g i) (x i + v) - H (x:=x) (g:=g) (f:=f) L (g i) = f i + @inner ℝ (E d) _ (g i) v := by
    rw [hH, inner_add_right]
    ring
  linarith

end SmoothDual
