module
public import Continuation.RootIsolation.SimpleRoots
@[expose] public section
open Polynomial Filter Topology RootIsolation
noncomputable section
namespace RootIsolation.SimpleRoots

lemma sign_between_endpoint_and_local_neighborhood (p : Polynomial ℚ)
    (a b x u : ℝ) (hx : p.aeval x = 0)
    (h_a_lt_u : a < u) (h_u_lt_x : u < x)
    (h_x_le_b : x ≤ b) (h_a_le_b : a ≤ b)
    (h_a_u_opposite : p.aeval a * p.aeval u < 0) :
    ∃ y ∈ Set.Ioo a u, p.aeval y = 0 := by
  have h_cont : ContinuousOn (fun t => p.aeval t) (Set.Icc a u) :=
    (poly_aeval_continuous p).continuousOn
  have h_ab : a < u := h_a_lt_u
  have h_sign : p.aeval a * p.aeval u < 0 := h_a_u_opposite
  have h_cases : 0 < p.aeval a ∧ p.aeval u < 0 ∨ p.aeval a < 0 ∧ 0 < p.aeval u := by
    have h1 := mul_neg_iff.mp h_sign
    exact h1
  have h_pre : IsPreconnected (Set.Icc a u) := isPreconnected_Icc
  have h_cont0 : ContinuousOn (fun _ : ℝ => (0:ℝ)) (Set.Icc a u) := continuousOn_const
  rcases h_cases with ⟨ha_pos, hu_neg⟩ | ⟨ha_neg, hu_pos⟩
  · have h_exists : ∃ c ∈ Set.Icc a u, (0:ℝ) = p.aeval c := by
      apply IsPreconnected.intermediate_value₂ h_pre
        (Set.mem_Icc.mpr ⟨le_refl a, le_of_lt h_ab⟩) (Set.mem_Icc.mpr ⟨le_of_lt h_ab, le_refl u⟩) h_cont0 h_cont
      · exact le_of_lt ha_pos
      · exact le_of_lt hu_neg
    obtain ⟨c, hc_mem, hc_eq⟩ := h_exists
    have h_c_ne_a : c ≠ a := by intro h_eq; rw [h_eq] at hc_eq; linarith
    have h_c_ne_u : c ≠ u := by intro h_eq; rw [h_eq] at hc_eq; linarith
    exact ⟨c, ⟨lt_of_le_of_ne hc_mem.1 (Ne.symm h_c_ne_a), lt_of_le_of_ne hc_mem.2 h_c_ne_u⟩, hc_eq.symm⟩
  · have h_exists : ∃ c ∈ Set.Icc a u, p.aeval c = 0 := by
      apply IsPreconnected.intermediate_value₂ h_pre
        (Set.mem_Icc.mpr ⟨le_refl a, le_of_lt h_ab⟩) (Set.mem_Icc.mpr ⟨le_of_lt h_ab, le_refl u⟩) h_cont h_cont0
      · exact le_of_lt ha_neg
      · exact le_of_lt hu_pos
    obtain ⟨c, hc_mem, hc_eq⟩ := h_exists
    have h_c_ne_a : c ≠ a := by intro h_eq; rw [h_eq] at hc_eq; linarith
    have h_c_ne_u : c ≠ u := by intro h_eq; rw [h_eq] at hc_eq; linarith
    exact ⟨c, ⟨lt_of_le_of_ne hc_mem.1 (Ne.symm h_c_ne_a), lt_of_le_of_ne hc_mem.2 h_c_ne_u⟩, hc_eq⟩

lemma sign_between_local_and_endpoint_neighborhood (p : Polynomial ℚ)
    (a b x u : ℝ) (hx : p.aeval x = 0)
    (h_x_lt_u : x < u) (h_u_lt_b : u < b)
    (h_a_le_x : a ≤ x)
    (h_u_b_opposite : p.aeval u * p.aeval b < 0) :
    ∃ y ∈ Set.Ioo u b, p.aeval y = 0 := by
  have h_cont : ContinuousOn (fun t => p.aeval t) (Set.Icc u b) :=
    (poly_aeval_continuous p).continuousOn
  have h_sign : p.aeval u * p.aeval b < 0 := h_u_b_opposite
  have h_ab : u < b := h_u_lt_b
  have h_cases : 0 < p.aeval u ∧ p.aeval b < 0 ∨ p.aeval u < 0 ∧ 0 < p.aeval b := by
    have h1 := mul_neg_iff.mp h_sign
    exact h1
  have h_pre : IsPreconnected (Set.Icc u b) := isPreconnected_Icc
  have h_cont0 : ContinuousOn (fun _ : ℝ => (0:ℝ)) (Set.Icc u b) := continuousOn_const
  rcases h_cases with ⟨hu_pos, hb_neg⟩ | ⟨hu_neg, hb_pos⟩
  · have h_exists : ∃ c ∈ Set.Icc u b, (0:ℝ) = p.aeval c := by
      apply IsPreconnected.intermediate_value₂ h_pre
        (Set.mem_Icc.mpr ⟨le_refl u, le_of_lt h_ab⟩) (Set.mem_Icc.mpr ⟨le_of_lt h_ab, le_refl b⟩) h_cont0 h_cont
      · exact le_of_lt hu_pos
      · exact le_of_lt hb_neg
    obtain ⟨c, hc_mem, hc_eq⟩ := h_exists
    have h_c_ne_u : c ≠ u := by intro h_eq; rw [h_eq] at hc_eq; linarith
    have h_c_ne_b : c ≠ b := by intro h_eq; rw [h_eq] at hc_eq; linarith
    exact ⟨c, ⟨lt_of_le_of_ne hc_mem.1 (Ne.symm h_c_ne_u), lt_of_le_of_ne hc_mem.2 h_c_ne_b⟩, hc_eq.symm⟩
  · have h_exists : ∃ c ∈ Set.Icc u b, p.aeval c = 0 := by
      apply IsPreconnected.intermediate_value₂ h_pre
        (Set.mem_Icc.mpr ⟨le_refl u, le_of_lt h_ab⟩) (Set.mem_Icc.mpr ⟨le_of_lt h_ab, le_refl b⟩) h_cont h_cont0
      · exact le_of_lt hu_neg
      · exact le_of_lt hb_pos
    obtain ⟨c, hc_mem, hc_eq⟩ := h_exists
    have h_c_ne_u : c ≠ u := by intro h_eq; rw [h_eq] at hc_eq; linarith
    have h_c_ne_b : c ≠ b := by intro h_eq; rw [h_eq] at hc_eq; linarith
    exact ⟨c, ⟨lt_of_le_of_ne hc_mem.1 (Ne.symm h_c_ne_u), lt_of_le_of_ne hc_mem.2 h_c_ne_b⟩, hc_eq⟩

theorem endpoint_sign_of_unique_simple_root (p : Polynomial ℚ) (x a b : ℝ)
    (hx : p.aeval x = 0) (hd : p.derivative.aeval x ≠ 0)
    (h_a_lt_x : a < x) (h_x_lt_b : x < b)
    (h_no_other : ∀ y, p.aeval y = 0 → y ∈ Set.Icc a b → y = x)
    (h_a_ne : p.aeval a ≠ 0) (h_b_ne : p.aeval b ≠ 0) :
    p.aeval a * p.aeval b < 0 := by
  obtain ⟨ε0, hε0_pos, h_sign⟩ := exists_deriv_sign_nhd p x hd
  have h_xa_pos : 0 < x - a := by linarith
  have h_bx_pos : 0 < b - x := by linarith
  let l := if ε0 / 2 < x - a then x - ε0 / 2 else (a + x) / 2
  let r := if ε0 / 2 < b - x then x + ε0 / 2 else (x + b) / 2
  have h_l_lt_x : l < x := by
    simp only [l]
    by_cases h : ε0 / 2 < x - a
    · simp [h]; linarith
    · simp [h]; linarith
  have h_a_lt_l : a < l := by
    simp only [l]
    by_cases h : ε0 / 2 < x - a
    · simp [h]; linarith
    · simp [h]; linarith
  have h_x_lt_r : x < r := by
    simp only [r]
    by_cases h : ε0 / 2 < b - x
    · simp [h]; linarith
    · simp [h]; linarith
  have h_r_lt_b : r < b := by
    simp only [r]
    by_cases h : ε0 / 2 < b - x
    · simp [h]; linarith
    · simp [h]; linarith
  have h_l_gt : x - ε0 < l := by
    simp only [l]
    by_cases h : ε0 / 2 < x - a
    · simp [h]; linarith
    · simp [h]
      have h1 : a ≥ x - ε0 := by
        have : ¬ ε0 / 2 < x - a := h
        linarith
      linarith
  have h_r_lt : r < x + ε0 := by
    simp only [r]
    by_cases h : ε0 / 2 < b - x
    · simp [h]; linarith
    · simp [h]
      have h1 : b ≤ x + ε0 := by
        have : ¬ ε0 / 2 < b - x := h
        linarith
      linarith
  have h_l_sign : p.aeval l * p.derivative.aeval x < 0 :=
    mvt_left_sign p x hd ε0 hε0_pos h_sign l h_l_lt_x h_l_gt hx
  have h_r_sign : 0 < p.aeval r * p.derivative.aeval x :=
    mvt_right_sign p x hd ε0 hε0_pos h_sign r h_x_lt_r h_r_lt hx
  by_contra h_not_neg
  have h_not_neg' : ¬ p.aeval a * p.aeval b < 0 := h_not_neg
  have h_prod_pos : 0 < p.aeval a * p.aeval b := by
    have h_prod_ne : p.aeval a * p.aeval b ≠ 0 := mul_ne_zero h_a_ne h_b_ne
    have h_le_or_gt := lt_or_gt_of_ne h_prod_ne
    rcases h_le_or_gt with h_neg | h_pos
    · exact absurd h_neg h_not_neg'
    · exact h_pos
  by_cases hd_pos : 0 < p.derivative.aeval x
  · have hl_neg : p.aeval l < 0 := by nlinarith
    have hr_pos : 0 < p.aeval r := by nlinarith
    have h_cases : (0 < p.aeval a ∧ 0 < p.aeval b) ∨ (p.aeval a < 0 ∧ p.aeval b < 0) := by
      have h1 := mul_pos_iff.mp h_prod_pos
      rcases h1 with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
      · left; exact ⟨ha_pos, hb_pos⟩
      · right; exact ⟨ha_neg, hb_neg⟩
    rcases h_cases with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
    · have h_opposite : p.aeval a * p.aeval l < 0 := mul_neg_of_pos_of_neg ha_pos hl_neg
      obtain ⟨y, hy_mem, hy_root⟩ := sign_between_endpoint_and_local_neighborhood p a b x l hx h_a_lt_l h_l_lt_x (le_of_lt h_x_lt_b) (le_of_lt (lt_trans h_a_lt_l (lt_trans h_l_lt_x h_x_lt_b))) h_opposite
      have hy_in_Icc : y ∈ Set.Icc a b := ⟨le_of_lt hy_mem.1, le_trans (le_of_lt hy_mem.2) (le_of_lt h_l_lt_x) |> fun h => le_trans h (le_of_lt h_x_lt_b)⟩
      have hy_eq_x : y = x := h_no_other y hy_root hy_in_Icc
      have hy_lt_x : y < x := lt_trans hy_mem.2 h_l_lt_x
      linarith
    · have h_opposite : p.aeval r * p.aeval b < 0 := mul_neg_of_pos_of_neg hr_pos hb_neg
      obtain ⟨y, hy_mem, hy_root⟩ := sign_between_local_and_endpoint_neighborhood p a b x r hx h_x_lt_r h_r_lt_b (le_of_lt h_a_lt_x) h_opposite
      have hy_in_Icc : y ∈ Set.Icc a b := ⟨le_trans (le_of_lt h_a_lt_x) (le_of_lt h_x_lt_r) |> fun h => le_trans h (le_of_lt hy_mem.1), le_of_lt hy_mem.2⟩
      have hy_eq_x : y = x := h_no_other y hy_root hy_in_Icc
      have hy_gt_x : x < y := lt_trans h_x_lt_r hy_mem.1
      linarith
  · have hd_neg : p.derivative.aeval x < 0 := by
      rcases lt_or_gt_of_ne hd with h_neg | h_pos
      · exact h_neg
      · exact absurd h_pos hd_pos
    have hl_pos : 0 < p.aeval l := by nlinarith
    have hr_neg : p.aeval r < 0 := by nlinarith
    have h_cases : (0 < p.aeval a ∧ 0 < p.aeval b) ∨ (p.aeval a < 0 ∧ p.aeval b < 0) := by
      have h1 := mul_pos_iff.mp h_prod_pos
      rcases h1 with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
      · left; exact ⟨ha_pos, hb_pos⟩
      · right; exact ⟨ha_neg, hb_neg⟩
    rcases h_cases with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
    · have h_opposite : p.aeval r * p.aeval b < 0 := mul_neg_of_neg_of_pos hr_neg hb_pos
      obtain ⟨y, hy_mem, hy_root⟩ := sign_between_local_and_endpoint_neighborhood p a b x r hx h_x_lt_r h_r_lt_b (le_of_lt h_a_lt_x) h_opposite
      have hy_in_Icc : y ∈ Set.Icc a b := ⟨le_trans (le_of_lt h_a_lt_x) (le_of_lt h_x_lt_r) |> fun h => le_trans h (le_of_lt hy_mem.1), le_of_lt hy_mem.2⟩
      have hy_eq_x : y = x := h_no_other y hy_root hy_in_Icc
      have hy_gt_x : x < y := lt_trans h_x_lt_r hy_mem.1
      linarith
    · have h_opposite : p.aeval a * p.aeval l < 0 := mul_neg_of_neg_of_pos ha_neg hl_pos
      obtain ⟨y, hy_mem, hy_root⟩ := sign_between_endpoint_and_local_neighborhood p a b x l hx h_a_lt_l h_l_lt_x (le_of_lt h_x_lt_b) (le_of_lt (lt_trans h_a_lt_l (lt_trans h_l_lt_x h_x_lt_b))) h_opposite
      have hy_in_Icc : y ∈ Set.Icc a b := ⟨le_of_lt hy_mem.1, le_trans (le_of_lt hy_mem.2) (le_of_lt h_l_lt_x) |> fun h => le_trans h (le_of_lt h_x_lt_b)⟩
      have hy_eq_x : y = x := h_no_other y hy_root hy_in_Icc
      have hy_lt_x : y < x := lt_trans hy_mem.2 h_l_lt_x
      linarith

theorem every_simple_root_mem_filteredIntervals_of_separation
    (p : Polynomial ℚ) (eps : ℚ) (heps : 0 < eps)
    (hsep : ∀ x y:ℝ, p.aeval x = 0 → p.aeval y = 0 → x ≠ y → (eps:ℝ) ≤ |x - y|)
    (B : ℚ) (hB : 0 < B) (hBspec : ∀ x:ℝ, p.aeval x = 0 → ‖x‖ ≤ (B:ℝ))
    (h_simple : ∀ x:ℝ, p.aeval x = 0 → p.derivative.aeval x ≠0) :
    ∃ delta : ℚ, 0 < delta ∧ ∀ x:ℝ,
      (p.aeval x = 0) → ∃ I ∈ filteredIntervals p B delta, x ∈ I.toSet := by
  let delta : ℚ := eps / 2
  have h_delta_pos : 0 < delta := by simp [delta]; linarith
  use delta, h_delta_pos
  intro x hx
  have hd : p.derivative.aeval x ≠ 0 := h_simple x hx
  have hp_ne : p ≠ 0 := by intro h_eq; simp [h_eq] at hd
  have h_cover := cover_from_cauchyBound p hp_ne B hB hBspec delta h_delta_pos x hx
  obtain ⟨a, b, h_mem, h_x_mem⟩ := h_cover
  have h_x_le : (a : ℝ) ≤ x := h_x_mem.1
  have h_x_ge : x ≤ (b : ℝ) := h_x_mem.2
  have h_b_eq : b = a + delta := partition_interval_length' B delta a b h_mem
  have h_ba_real : (b : ℝ) - (a : ℝ) = (delta : ℝ) := by
    have h_eq : b = a + delta := h_b_eq
    have h_cast : ((b : ℚ) : ℝ) = ((a + delta : ℚ) : ℝ) := by rw [h_eq]
    rw [h_cast]; push_cast; ring
  have h_delta_lt_eps : (delta : ℝ) < (eps : ℝ) := by
    show ((eps / 2 : ℚ) : ℝ) < (eps : ℝ)
    have h_eps_pos : 0 < (eps : ℝ) := by exact_mod_cast heps
    push_cast; linarith
  have h_unique_in_cell : ∀ y, p.aeval y = 0 → y ∈ Set.Icc (a : ℝ) (b : ℝ) → y = x := by
    intro y hy hy_mem
    by_contra h_ne
    have h_y_ne_x : y ≠ x := h_ne
    have h_sep_le : (eps : ℝ) ≤ |x - y| := hsep x y hx hy (Ne.symm h_y_ne_x)
    have h_dist_le : |x - y| ≤ (b : ℝ) - (a : ℝ) := by
      have ha_le_x : (a : ℝ) ≤ x := h_x_le
      have hx_le_b : x ≤ (b : ℝ) := h_x_ge
      have ha_le_y : (a : ℝ) ≤ y := hy_mem.1
      have hy_le_b : y ≤ (b : ℝ) := hy_mem.2
      apply abs_le.mpr
      constructor
      · linarith
      · linarith
    have h_le : |x - y| ≤ (delta : ℝ) := by rw [h_ba_real] at h_dist_le; exact h_dist_le
    linarith
  by_cases h_x_eq_a : x = (a : ℝ)
  · have h_eval_a : p.eval a = 0 := by
      have h_aeval : p.aeval (a : ℝ) = 0 := by rw [← h_x_eq_a]; exact hx
      have h_coe : p.aeval (a : ℝ) = ((p.eval a : ℚ) : ℝ) := aeval_coe_eq_coe_eval p a
      rw [h_coe] at h_aeval
      exact_mod_cast h_aeval
    have h_a_in : a ∈ pointRoots p B delta := by
      rw [pointRoots_mem_iff]
      constructor
      · obtain ⟨i, h_i, h_a_eq, _⟩ := partitionPoints_consecutive_form' B delta a b h_mem
        have h_i_lt : i < (partitionPoints B delta).length := Nat.lt_of_succ_lt h_i
        have h_a_eq' : a = (partitionPoints B delta)[i]'h_i_lt := h_a_eq
        rw [h_a_eq']
        exact List.getElem_mem h_i_lt
      · exact h_eval_a
    have h_iso : IsoInterval.point a ∈ filteredIntervals p B delta := by
      simp only [filteredIntervals, List.mem_append, List.mem_map]
      left
      exact ⟨a, h_a_in, rfl⟩
    exact ⟨IsoInterval.point a, h_iso, by simp [IsoInterval.toSet, h_x_eq_a]⟩
  · by_cases h_x_eq_b : x = (b : ℝ)
    · have h_eval_b : p.eval b = 0 := by
        have h_aeval : p.aeval (b : ℝ) = 0 := by rw [← h_x_eq_b]; exact hx
        have h_coe : p.aeval (b : ℝ) = ((p.eval b : ℚ) : ℝ) := aeval_coe_eq_coe_eval p b
        rw [h_coe] at h_aeval
        exact_mod_cast h_aeval
      have h_b_in : b ∈ pointRoots p B delta := by
        rw [pointRoots_mem_iff]
        constructor
        · obtain ⟨i, h_i, _, h_b_eq2⟩ := partitionPoints_consecutive_form' B delta a b h_mem
          have h_b_eq' : b = (partitionPoints B delta)[i + 1]'h_i := h_b_eq2
          rw [h_b_eq']
          exact List.getElem_mem h_i
        · exact h_eval_b
      have h_iso : IsoInterval.point b ∈ filteredIntervals p B delta := by
        simp only [filteredIntervals, List.mem_append, List.mem_map]
        left
        exact ⟨b, h_b_in, rfl⟩
      exact ⟨IsoInterval.point b, h_iso, by simp [IsoInterval.toSet, h_x_eq_b]⟩
    · have h_a_lt_x : (a : ℝ) < x := lt_of_le_of_ne h_x_le (Ne.symm h_x_eq_a)
      have h_x_lt_b : x < (b : ℝ) := lt_of_le_of_ne h_x_ge h_x_eq_b
      have h_a_not_root : p.aeval (a : ℝ) ≠ 0 := by
        intro h_eq
        have h_mem_a : (a : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨le_refl _, le_of_lt (lt_trans h_a_lt_x h_x_lt_b)⟩
        have h_eq_x : (a : ℝ) = x := h_unique_in_cell (a : ℝ) h_eq h_mem_a
        linarith
      have h_b_not_root : p.aeval (b : ℝ) ≠ 0 := by
        intro h_eq
        have h_mem_b : (b : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨le_of_lt (lt_trans h_a_lt_x h_x_lt_b), le_refl _⟩
        have h_eq_x : (b : ℝ) = x := h_unique_in_cell (b : ℝ) h_eq h_mem_b
        linarith
      have h_sign : p.aeval (a : ℝ) * p.aeval (b : ℝ) < 0 :=
        endpoint_sign_of_unique_simple_root p x (a : ℝ) (b : ℝ) hx hd h_a_lt_x h_x_lt_b h_unique_in_cell h_a_not_root h_b_not_root
      have h_prod : p.eval a * p.eval b < 0 := by
        have h_aeval_a : p.aeval (a : ℝ) = ((p.eval a : ℚ) : ℝ) := aeval_coe_eq_coe_eval p a
        have h_aeval_b : p.aeval (b : ℝ) = ((p.eval b : ℚ) : ℝ) := aeval_coe_eq_coe_eval p b
        have h_sign' : ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) < 0 := by
          rw [← h_aeval_a, ← h_aeval_b]; exact h_sign
        have h_cast : ((p.eval a * p.eval b : ℚ) : ℝ) = ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) := by push_cast; ring
        rw [← h_cast] at h_sign'
        exact_mod_cast h_sign'
      have h_open : (a, b) ∈ signChangingIntervals p B delta := by
        rw [signChangingIntervals_mem_iff]; exact ⟨h_mem, h_prod⟩
      have h_iso : IsoInterval.openInterval a b ∈ filteredIntervals p B delta := by
        simp only [filteredIntervals, List.mem_append, List.mem_map]
        right
        exact ⟨(a, b), h_open, rfl⟩
      exact ⟨IsoInterval.openInterval a b, h_iso, by simp [IsoInterval.toSet]; exact ⟨h_a_lt_x, h_x_lt_b⟩⟩


end RootIsolation.SimpleRoots

end
