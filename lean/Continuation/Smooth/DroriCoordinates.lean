module
public import Continuation.Smooth.DroriHardData
public import Continuation.Smooth.Sufficient
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace SmoothDrori

theorem hardX_apply (N : ℕ) (R : ℝ) (i : ℕ) (j : Fin (N+1)) :
    hardX N R i j = if j.val < i then
      -(zetaStar N R j.val - zetaStar N R (i+1)) /
        Real.sqrt (zetaStar N R j.val - zetaStar N R (j.val+1)) else 0 := by
  classical
  simp only [hardX, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp_all [PiLp.smul_apply, PiLp.single_apply]
  · intro b _ hbj
    split_ifs <;> simp_all [PiLp.smul_apply, PiLp.single_apply, Ne.symm hbj]
  · simp

theorem hardG_apply (N : ℕ) (L R : ℝ) (i : ℕ) (j : Fin (N+1)) :
    hardG N L R i j = if j.val = i then
      L * Real.sqrt (zetaStar N R i - zetaStar N R (i+1)) else 0 := by
  classical
  by_cases hi : i ≤ N
  · simp only [hardG, dif_pos hi, PiLp.single_apply]
    have he : j = (⟨i, by omega⟩ : Fin (N+1)) ↔ j.val = i := by
      exact Fin.ext_iff
    simp only [he]
  · have hji : j.val ≠ i := by have := j.isLt; omega
    simp [hardG,hi,hji]

theorem hardG_inner (N : ℕ) (L R : ℝ) (i : ℕ) (hi : i ≤ N)
    (v : EuclideanSpace ℝ (Fin (N+1))) :
    ⟪hardG N L R i,v⟫_ℝ =
      L * Real.sqrt (zetaStar N R i-zetaStar N R (i+1)) * v ⟨i,by omega⟩ := by
  simp [hardG, hi, EuclideanSpace.inner_single_left]

theorem hardG_inner_hardX (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (i j : ℕ) (hi : i ≤ N) :
    ⟪hardG N L R i,hardX N R j⟫_ℝ =
      if i < j then -L*(zetaStar N R i-zetaStar N R (j+1)) else 0 := by
  rw [hardG_inner N L R i hi, hardX_apply]
  simp only
  split_ifs with hij
  · have hd : 0 < zetaStar N R i-zetaStar N R (i+1) :=
      sub_pos.mpr (zetaStar_strictAnti N R hN hR i hi)
    have hs : Real.sqrt (zetaStar N R i-zetaStar N R (i+1)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hd)
    field_simp
  · ring

theorem hardG_inner_hardG_ne (N : ℕ) (L R : ℝ) (i j : ℕ)
    (hi : i ≤ N) (hij : i ≠ j) :
    ⟪hardG N L R i,hardG N L R j⟫_ℝ = 0 := by
  rw [hardG_inner N L R i hi,hardG_apply]
  simp [hij]

theorem hardF_sub_norm (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L)
    (hR : 0 < R) (i : ℕ) (hi : i ≤ N+1) :
    hardF N L R i - 1/(2*L)*‖hardG N L R i‖^2 = L*zetaStar N R (i+1) := by
  by_cases hiN : i ≤ N
  · have hd := le_of_lt (sub_pos.mpr (zetaStar_strictAnti N R hN hR i hiN))
    rw [hardG_norm_sq N L R i hiN hd]
    simp only [hardF,hiN,dite_true]
    field_simp
    ring
  · have hei : i = N+1 := by omega
    subst i
    simp [hardF, hardG, zetaStar_last]

theorem zetaStar_antitone_bounded (N : ℕ) (R : ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ N+1) : zetaStar N R j ≤ zetaStar N R i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (zetaStar_strictAnti N R hN hR j (by omega)).le.trans (ih (by omega))

theorem hardG_norm_sub_sq (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hij : i ≠ j) :
    ‖hardG N L R i-hardG N L R j‖^2 =
      L^2*((zetaStar N R i-zetaStar N R (i+1))+
        (zetaStar N R j-zetaStar N R (j+1))) := by
  rw [norm_sub_sq_real, hardG_inner_hardG_ne N L R i j hi hij,
    hardG_norm_sq N L R i hi (sub_nonneg.mpr
      (zetaStar_strictAnti N R hN hR i hi).le),
    hardG_norm_sq N L R j hj (sub_nonneg.mpr
      (zetaStar_strictAnti N R hN hR j hj).le)]
  ring

/-- Every pair of Drori data, including the zero-gradient minimizer datum,
    satisfies the smooth convex interpolation inequality. -/
theorem hardData_interpolation (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L)
    (hR : 0 < R) (i j : ℕ) (hi : i ≤ N+1) (hj : j ≤ N+1) :
    0 ≤ hardF N L R i-hardF N L R j-
      ⟪hardG N L R j,hardX N R i-hardX N R j⟫_ℝ-
      1/(2*L)*‖hardG N L R i-hardG N L R j‖^2 := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hiN : i ≤ N
  · by_cases hjN : j ≤ N
    · rw [inner_sub_right, hardG_inner_hardX N L R hN hR j i hjN,
        hardG_inner_hardX N L R hN hR j j hjN,
        hardG_norm_sub_sq N L R hN hR i j hiN hjN hij]
      simp only [lt_self_iff_false, if_false, sub_zero, hardF, hiN,hjN,dite_true]
      by_cases hji : j < i
      · rw [if_pos hji]
        have he : L/2*(zetaStar N R i+zetaStar N R (i+1))-
            L/2*(zetaStar N R j+zetaStar N R (j+1))-
            -(L*(zetaStar N R j-zetaStar N R (i+1)))-
            1/(2*L)*(L^2*((zetaStar N R i-zetaStar N R (i+1))+
              (zetaStar N R j-zetaStar N R (j+1)))) = 0 := by field_simp; ring
        nlinarith [he]
      · rw [if_neg hji]
        have hz := zetaStar_antitone_bounded N R hN hR (i+1) j (by omega) hj
        have he : L/2*(zetaStar N R i+zetaStar N R (i+1))-
            L/2*(zetaStar N R j+zetaStar N R (j+1))-
            0-1/(2*L)*(L^2*((zetaStar N R i-zetaStar N R (i+1))+
              (zetaStar N R j-zetaStar N R (j+1)))) =
            L*(zetaStar N R (i+1)-zetaStar N R j) := by field_simp; ring
        rw [he]
        exact mul_nonneg hL.le (sub_nonneg.mpr hz)
    · have hej : j = N+1 := by omega
      subst j
      have hG : hardG N L R (N+1) = 0 := by simp [hardG]
      have hF : hardF N L R (N+1) = 0 := by simp [hardF]
      rw [hG,hF]
      simpa only [sub_zero, inner_zero_left] using
        (show 0 ≤ hardF N L R i-1/(2*L)*‖hardG N L R i‖^2 from
          by rw [hardF_sub_norm N L R hN hL hR i hi]
             exact mul_nonneg hL.le (zetaStar_nonneg N R hR.le (i+1)))
  · have hei : i = N+1 := by omega
    have hjN : j ≤ N := by omega
    subst i
    have hG : hardG N L R (N+1) = 0 := by simp [hardG]
    have hF : hardF N L R (N+1) = 0 := by simp [hardF]
    rw [hG,hF, zero_sub, zero_sub, norm_neg, inner_sub_right,
      hardG_inner_hardX N L R hN hR j (N+1) hjN,
      hardG_inner_hardX N L R hN hR j j hjN,
      hardG_norm_sq N L R j hjN (sub_nonneg.mpr
        (zetaStar_strictAnti N R hN hR j hjN).le)]
    simp only [show j < N+1 by omega, if_true, lt_self_iff_false, if_false,
      show N+1+1=N+2 by omega, zetaStar_last,sub_zero,hardF,hjN,dite_true]
    have he : -(L/2*(zetaStar N R j+zetaStar N R (j+1)))-
        -L*zetaStar N R j - 1/(2*L)*(L^2*(zetaStar N R j-zetaStar N R (j+1))) = 0 :=
      by field_simp; ring
    nlinarith [he]

/-- Actual smooth convex interpolants of the hard data exist. This statement
    alone does not claim the zero-chain property of Drori's orthant construction. -/
theorem exists_hardData_interpolant (N : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    ∃ F : EuclideanSpace ℝ (Fin (N+1)) → ℝ,
    ∃ G : EuclideanSpace ℝ (Fin (N+1)) → EuclideanSpace ℝ (Fin (N+1)),
      (∀ p, HasGradientAt F (G p) p) ∧ ConvexOn ℝ Set.univ F ∧
      LipschitzWith (Real.toNNReal L) G ∧
      ∀ i ≤ N+1, F (hardX N R i) = hardF N L R i ∧
        G (hardX N R i) = hardG N L R i := by
  obtain ⟨F,G,hGrad,hConv,hLip,hData⟩ := SmoothInterpolation.sufficient hL
    (fun i : Fin (N+2) => hardX N R i.val)
    (fun i : Fin (N+2) => hardG N L R i.val)
    (fun i : Fin (N+2) => hardF N L R i.val)
    (fun i j => hardData_interpolation N L R hN hL hR i.val j.val (by omega) (by omega))
  exact ⟨F,G,hGrad,hConv,hLip,fun i hi => hData ⟨i,by omega⟩⟩

end SmoothDrori
