module
public import Continuation.RootIsolation.Partition
@[expose] public section

open Polynomial

namespace RootIsolation

lemma partitionPoints_eq_range_map (B delta : ℚ) :
    partitionPoints B delta = (List.range (numSteps B delta + 1)).map (fun j : ℕ => -B + (j : ℚ) * delta) := by
  simp [partitionPoints, ← List.map_eq_flatMap, Function.comp]

lemma partitionPoints_get (B delta : ℚ) (i : ℕ) (h : i < (partitionPoints B delta).length) :
    (partitionPoints B delta)[i] = -B + (i : ℚ) * delta := by
  have h_eq := partitionPoints_eq_range_map B delta
  have h_len : (partitionPoints B delta).length = numSteps B delta + 1 := partitionPoints_length B delta
  have h1 : i < numSteps B delta + 1 := h_len ▸ h
  have h_range : i < (List.range (numSteps B delta + 1)).length := by simp [h1]
  have h_map_len : i < ((List.range (numSteps B delta + 1)).map (fun j : ℕ => -B + (j : ℚ) * delta)).length := by simp [h1]
  have h_get : ((List.range (numSteps B delta + 1)).map (fun j : ℕ => -B + (j : ℚ) * delta))[i]'h_map_len = -B + (i : ℚ) * delta := by
    rw [List.getElem_map]
    rw [List.getElem_range h_range]
  have h2 : (partitionPoints B delta)[i]'h = ((List.range (numSteps B delta + 1)).map (fun j : ℕ => -B + (j : ℚ) * delta))[i]'h_map_len := by
    exact List.getElem_of_eq h_eq h
  rw [h2, h_get]

lemma consecutivePairs_mem (l : List ℚ) (i : ℕ) (h : i + 1 < l.length) :
    (l[i]'(by omega), l[i + 1]'h) ∈ consecutivePairs l := by
  have h_len : i < (l.zip l.tail).length := by
    simp [List.length_zip, List.length_tail]
    omega
  have h_eq : (l.zip l.tail)[i]'h_len = (l[i]'(by omega), l[i + 1]'h) := by
    rw [List.getElem_zip]
    have h_tail : l.tail[i]'(by simp [List.length_tail]; omega) = l[i + 1]'h := by
      apply List.getElem_tail
    simp [h_tail]
  have h_mem : (l.zip l.tail)[i]'h_len ∈ l.zip l.tail := List.getElem_mem h_len
  rw [h_eq] at h_mem
  have h_consec : consecutivePairs l = l.zip l.tail := by
    unfold consecutivePairs
    cases l with
    | nil => simp
    | cons hd tl => simp
  rw [← h_consec] at h_mem
  exact h_mem

theorem original_statement_false :
    ¬ (∀ (p : Polynomial ℚ) (_hp : p ≠ 0) (B : ℚ) (_hB : 0 ≤ B)
      (hB_spec : ∀ x : ℝ, p.aeval x = 0 → ‖x‖ ≤ ((B : ℚ) : ℝ))
      (delta : ℚ) (_h_delta_pos : 0 < delta) (x : ℝ) (_hx : p.aeval x = 0),
      ∃ a b : ℚ, (a, b) ∈ consecutivePairs (partitionPoints B delta) ∧ x ∈ Set.Icc (a : ℝ) (b : ℝ)) := by
  intro h
  have h_inst := h Polynomial.X (by simp) 0 (le_refl 0)
    (by
      intro y hy
      have hy' : y = 0 := by simpa [Polynomial.aeval_X] using hy
      rw [hy']
      simp)
    (1 : ℚ) (by norm_num) (0 : ℝ) (by simp [Polynomial.aeval_X])
  have h_empty : consecutivePairs (partitionPoints (0 : ℚ) (1 : ℚ)) = [] := by
    have h1 : numSteps (0 : ℚ) (1 : ℚ) = 0 := by simp [numSteps]
    have h2 : partitionPoints (0 : ℚ) (1 : ℚ) = [0] := by
      simp [partitionPoints, h1]
    simp [h2, consecutivePairs]
  simp [h_empty] at h_inst

theorem cover_from_cauchyBound (p : Polynomial ℚ) (hp : p ≠ 0) (B : ℚ) (hB : 0 < B)
    (hB_spec : ∀ x : ℝ, p.aeval x = 0 → ‖x‖ ≤ ((B : ℚ) : ℝ))
    (delta : ℚ) (h_delta_pos : 0 < delta) (x : ℝ) (hx : p.aeval x = 0) :
    ∃ a b : ℚ, (a, b) ∈ consecutivePairs (partitionPoints B delta) ∧ x ∈ Set.Icc (a : ℝ) (b : ℝ) := by
  have h_norm_le : ‖x‖ ≤ ((B : ℚ) : ℝ) := hB_spec x hx
  have h_abs_le : |x| ≤ ((B : ℚ) : ℝ) := by rwa [Real.norm_eq_abs] at h_norm_le
  have h_x_le_B : x ≤ ((B : ℚ) : ℝ) := (abs_le.mp h_abs_le).2
  have h_negB_le_x : -((B : ℚ) : ℝ) ≤ x := by
    have h1 := (abs_le.mp h_abs_le).1
    linarith
  have hB_real_pos : (0 : ℝ) < ((B : ℚ) : ℝ) := by exact_mod_cast hB
  have hd_real_pos : (0 : ℝ) < ((delta : ℚ) : ℝ) := by exact_mod_cast h_delta_pos
  have hd_real_ne : ((delta : ℚ) : ℝ) ≠ 0 := ne_of_gt hd_real_pos
  let N : ℕ := numSteps B delta
  have h_len : (partitionPoints B delta).length = N + 1 := by rw [partitionPoints_length]
  have hN_pos : 0 < N := by
    have h_eq : N = ⌈2 * B / delta⌉₊ := by simp [N, numSteps, show ¬ delta ≤ 0 from by linarith]
    rw [h_eq]
    exact Nat.ceil_pos.mpr (by positivity)
  let q : ℝ := (x + ((B : ℚ) : ℝ)) / ((delta : ℚ) : ℝ)
  have h_q_nonneg : 0 ≤ q := by
    apply div_nonneg <;> linarith
  have h_q_le : q ≤ 2 * ((B : ℚ) : ℝ) / ((delta : ℚ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hd_real_pos)
    linarith
  have h2B_div_le_N : 2 * ((B : ℚ) : ℝ) / ((delta : ℚ) : ℝ) ≤ (N : ℝ) := by
    have h1 : (2 * B / delta : ℚ) ≤ (N : ℚ) := by
      have h_eq : N = ⌈2 * B / delta⌉₊ := by simp [N, numSteps, show ¬ delta ≤ 0 from by linarith]
      rw [h_eq]
      exact Nat.le_ceil _
    have h_cast : ((2 * B / delta : ℚ) : ℝ) = 2 * ((B : ℚ) : ℝ) / ((delta : ℚ) : ℝ) := by push_cast; ring
    calc 2 * ((B : ℚ) : ℝ) / ((delta : ℚ) : ℝ) = ((2 * B / delta : ℚ) : ℝ) := h_cast.symm
      _ ≤ ((N : ℚ) : ℝ) := by exact_mod_cast h1
      _ = (N : ℝ) := by push_cast; rfl
  have h_q_le_N : q ≤ (N : ℝ) := le_trans h_q_le h2B_div_le_N
  let i : ℕ := ⌊q⌋₊
  have h_i_le : (i : ℝ) ≤ q := Nat.floor_le h_q_nonneg
  have h_q_lt_next : q < (i : ℝ) + 1 := Nat.lt_floor_add_one q
  by_cases hq_lt : q < (N : ℝ)
  · have h_i_lt_N : i < N := by
      have h1 : (i : ℝ) < (N : ℝ) := lt_of_le_of_lt h_i_le hq_lt
      exact_mod_cast h1
    have h_a_le_x : ((-B + (i : ℚ) * delta : ℚ) : ℝ) ≤ x := by
      have h1 : (i : ℝ) * ((delta : ℚ) : ℝ) ≤ x + ((B : ℚ) : ℝ) := by
        have h2 : (i : ℝ) ≤ q := h_i_le
        have h3 : (i : ℝ) * ((delta : ℚ) : ℝ) ≤ q * ((delta : ℚ) : ℝ) := mul_le_mul_of_nonneg_right h2 (le_of_lt hd_real_pos)
        have h4 : q * ((delta : ℚ) : ℝ) = x + ((B : ℚ) : ℝ) := by simp [q, div_mul_cancel₀ _ hd_real_ne]
        linarith
      have h_cast : ((-B + (i : ℚ) * delta : ℚ) : ℝ) = -((B : ℚ) : ℝ) + (i : ℝ) * ((delta : ℚ) : ℝ) := by push_cast; ring
      linarith
    have h_x_le_b : x ≤ ((-B + ((i + 1 : ℕ) : ℚ) * delta : ℚ) : ℝ) := by
      have h1 : x + ((B : ℚ) : ℝ) < ((i : ℝ) + 1) * ((delta : ℚ) : ℝ) := by
        have h2 : q < (i : ℝ) + 1 := h_q_lt_next
        have h3 : q * ((delta : ℚ) : ℝ) < ((i : ℝ) + 1) * ((delta : ℚ) : ℝ) := mul_lt_mul_of_pos_right h2 hd_real_pos
        have h4 : q * ((delta : ℚ) : ℝ) = x + ((B : ℚ) : ℝ) := by simp [q, div_mul_cancel₀ _ hd_real_ne]
        linarith
      have h_cast : ((-B + ((i + 1 : ℕ) : ℚ) * delta : ℚ) : ℝ) = -((B : ℚ) : ℝ) + ((i : ℝ) + 1) * ((delta : ℚ) : ℝ) := by push_cast; ring
      linarith
    let a : ℚ := -B + (i : ℚ) * delta
    let b : ℚ := -B + ((i + 1 : ℕ) : ℚ) * delta
    have h_i_lt_len : i + 1 < (partitionPoints B delta).length := by rw [h_len]; omega
    have h_mem := consecutivePairs_mem (partitionPoints B delta) i h_i_lt_len
    have h_i_lt : i < (partitionPoints B delta).length := by rw [h_len]; omega
    have h_ip1_lt : i + 1 < (partitionPoints B delta).length := h_i_lt_len
    have h_a_eq : (partitionPoints B delta)[i]'h_i_lt = a := by
      have h1 := partitionPoints_get B delta i h_i_lt
      simp [a] at h1 ⊢
      exact h1
    have h_b_eq : (partitionPoints B delta)[i + 1]'h_ip1_lt = b := by
      have h1 := partitionPoints_get B delta (i + 1) h_ip1_lt
      simp [b] at h1 ⊢
      exact h1
    have h_pair_mem : (a, b) ∈ consecutivePairs (partitionPoints B delta) := by
      have h_eq : (a, b) = ((partitionPoints B delta)[i]'h_i_lt, (partitionPoints B delta)[i + 1]'h_ip1_lt) := by
        simp [h_a_eq, h_b_eq]
      rw [h_eq]
      exact h_mem
    exact ⟨a, b, h_pair_mem, ⟨h_a_le_x, h_x_le_b⟩⟩
  · have h_N_le_q : (N : ℝ) ≤ q := not_lt.mp hq_lt
    have h_q_eq_N : q = (N : ℝ) := le_antisymm h_q_le_N h_N_le_q
    have h_x_eq_B : x = ((B : ℚ) : ℝ) := by
      have h1 : x + ((B : ℚ) : ℝ) = (N : ℝ) * ((delta : ℚ) : ℝ) := by
        have h2 : q * ((delta : ℚ) : ℝ) = x + ((B : ℚ) : ℝ) := by simp [q, div_mul_cancel₀ _ hd_real_ne]
        rw [h_q_eq_N] at h2
        linarith
      have h2 : (N : ℝ) * ((delta : ℚ) : ℝ) = 2 * ((B : ℚ) : ℝ) := by
        have h_le : 2 * ((B : ℚ) : ℝ) ≤ (N : ℝ) * ((delta : ℚ) : ℝ) := (div_le_iff₀ hd_real_pos).mp h2B_div_le_N
        have h_ge : (N : ℝ) * ((delta : ℚ) : ℝ) ≤ 2 * ((B : ℚ) : ℝ) := by
          have h4 : x + ((B : ℚ) : ℝ) ≤ 2 * ((B : ℚ) : ℝ) := by linarith [h_x_le_B]
          rw [h1] at h4
          linarith
        linarith
      linarith
    let i : ℕ := N - 1
    have h_i_lt_N : i < N := by omega
    have h_i_eq : i + 1 = N := by omega
    have h_a_le_x : ((-B + (i : ℚ) * delta : ℚ) : ℝ) ≤ x := by
      have h1 : ((-B + (i : ℚ) * delta : ℚ) : ℝ) = -((B : ℚ) : ℝ) + (i : ℝ) * ((delta : ℚ) : ℝ) := by push_cast; ring
      rw [h1, h_x_eq_B]
      have h2 : (i : ℝ) = (N : ℝ) - 1 := by
        have h_eq : (i + 1 : ℕ) = N := h_i_eq
        have h_cast1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
          have h1 : ((i + 1 : ℕ) : ℝ) = ((i : ℕ) : ℝ) + 1 := by push_cast; ring
          simpa using h1
        have h_cast2 : ((N : ℕ) : ℝ) = (N : ℝ) := rfl
        have h3 : (i : ℝ) + 1 = (N : ℝ) := by
          calc (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) := h_cast1.symm
            _ = ((N : ℕ) : ℝ) := by rw [h_eq]
            _ = (N : ℝ) := rfl
        linarith
      rw [h2]
      have h3 : (N : ℝ) * ((delta : ℚ) : ℝ) = 2 * ((B : ℚ) : ℝ) := by
        have h_le : 2 * ((B : ℚ) : ℝ) ≤ (N : ℝ) * ((delta : ℚ) : ℝ) := (div_le_iff₀ hd_real_pos).mp h2B_div_le_N
        have h_ge : (N : ℝ) * ((delta : ℚ) : ℝ) ≤ 2 * ((B : ℚ) : ℝ) := by
          have h4 : x + ((B : ℚ) : ℝ) ≤ 2 * ((B : ℚ) : ℝ) := by linarith [h_x_le_B]
          have h5 : x + ((B : ℚ) : ℝ) = (N : ℝ) * ((delta : ℚ) : ℝ) := by
            have h2 : q * ((delta : ℚ) : ℝ) = x + ((B : ℚ) : ℝ) := by simp [q, div_mul_cancel₀ _ hd_real_ne]
            rw [h_q_eq_N] at h2
            linarith
          linarith
        linarith
      nlinarith
    have h_x_le_b : x ≤ ((-B + ((i + 1 : ℕ) : ℚ) * delta : ℚ) : ℝ) := by
      have h1 : ((-B + ((i + 1 : ℕ) : ℚ) * delta : ℚ) : ℝ) = -((B : ℚ) : ℝ) + ((i + 1 : ℕ) : ℝ) * ((delta : ℚ) : ℝ) := by push_cast; ring
      rw [h1, h_x_eq_B]
      have h2 : ((i + 1 : ℕ) : ℝ) = (N : ℝ) := by
        rw [h_i_eq]
      rw [h2]
      have h3 : (N : ℝ) * ((delta : ℚ) : ℝ) = 2 * ((B : ℚ) : ℝ) := by
        have h_le : 2 * ((B : ℚ) : ℝ) ≤ (N : ℝ) * ((delta : ℚ) : ℝ) := (div_le_iff₀ hd_real_pos).mp h2B_div_le_N
        have h_ge : (N : ℝ) * ((delta : ℚ) : ℝ) ≤ 2 * ((B : ℚ) : ℝ) := by
          have h4 : x + ((B : ℚ) : ℝ) ≤ 2 * ((B : ℚ) : ℝ) := by linarith [h_x_le_B]
          have h5 : x + ((B : ℚ) : ℝ) = (N : ℝ) * ((delta : ℚ) : ℝ) := by
            have h2 : q * ((delta : ℚ) : ℝ) = x + ((B : ℚ) : ℝ) := by simp [q, div_mul_cancel₀ _ hd_real_ne]
            rw [h_q_eq_N] at h2
            linarith
          linarith
        linarith
      linarith
    let a : ℚ := -B + (i : ℚ) * delta
    let b : ℚ := -B + ((i + 1 : ℕ) : ℚ) * delta
    have h_i_lt_len : i + 1 < (partitionPoints B delta).length := by rw [h_len, h_i_eq]; exact Nat.lt_succ_self N
    have h_mem := consecutivePairs_mem (partitionPoints B delta) i h_i_lt_len
    have h_i_lt : i < (partitionPoints B delta).length := by
      rw [h_len]
      omega
    have h_ip1_lt : i + 1 < (partitionPoints B delta).length := h_i_lt_len
    have h_a_eq : (partitionPoints B delta)[i]'h_i_lt = a := by
      have h1 := partitionPoints_get B delta i h_i_lt
      simp [a] at h1 ⊢
      exact h1
    have h_b_eq : (partitionPoints B delta)[i + 1]'h_ip1_lt = b := by
      have h1 := partitionPoints_get B delta (i + 1) h_ip1_lt
      simp [b] at h1 ⊢
      exact h1
    have h_pair_mem : (a, b) ∈ consecutivePairs (partitionPoints B delta) := by
      have h_eq : (a, b) = ((partitionPoints B delta)[i]'h_i_lt, (partitionPoints B delta)[i + 1]'h_ip1_lt) := by
        simp [h_a_eq, h_b_eq]
      rw [h_eq]
      exact h_mem
    exact ⟨a, b, h_pair_mem, ⟨h_a_le_x, h_x_le_b⟩⟩

end RootIsolation
