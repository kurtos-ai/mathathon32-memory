module
public import Continuation.RootIsolation.Partition
public import Continuation.RootIsolation.Cover
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-! A simple real root belongs to the actual rational sign-filtered grid output
for every sufficiently small positive mesh. The mesh threshold is existential;
this module does not claim effective root isolation or a computable threshold. -/
@[expose] public section

open Polynomial Filter Topology RootIsolation

namespace RootIsolation.SimpleRoots

noncomputable section

def polyMapToReal (p : Polynomial ℚ) : Polynomial ℝ := p.map (algebraMap ℚ ℝ)

lemma eval_map_algebraMap_eq_aeval (p : Polynomial ℚ) (x : ℝ) :
    (polyMapToReal p).eval x = p.aeval x := by
  simp [polyMapToReal, Polynomial.aeval_def, Polynomial.eval_map]

lemma aeval_coe_eq_coe_eval (p : Polynomial ℚ) (q : ℚ) : p.aeval (q : ℝ) = ((p.eval q : ℚ) : ℝ) := by
  rw [Polynomial.aeval_def]
  have h1 : (q : ℝ) = (algebraMap ℚ ℝ) q := by simp
  rw [h1, Polynomial.eval₂_hom (f := algebraMap ℚ ℝ) (x := q)]
  simp

lemma poly_aeval_continuous (p : Polynomial ℚ) : Continuous (fun x : ℝ => p.aeval x) := by
  have h : (fun x : ℝ => p.aeval x) = (fun x => (polyMapToReal p).eval x) := by
    funext x; rw [eval_map_algebraMap_eq_aeval]
  rw [h]; exact Polynomial.continuous_aeval _

lemma exists_deriv_sign_nhd (p : Polynomial ℚ) (x : ℝ) (hd : p.derivative.aeval x ≠ 0) :
    ∃ ε > 0, ∀ y, dist y x < ε → p.derivative.aeval y * p.derivative.aeval x > 0 := by
  have hcont : ContinuousAt (fun y : ℝ => p.derivative.aeval y) x := (poly_aeval_continuous p.derivative).continuousAt
  by_cases hd_pos : 0 < p.derivative.aeval x
  · have h_ev : ∀ᶠ y in 𝓝 x, 0 < p.derivative.aeval y := by
      have h_mem : Set.Ioi (0 : ℝ) ∈ 𝓝 (p.derivative.aeval x) := Ioi_mem_nhds hd_pos
      exact hcont.eventually_mem h_mem
    rw [Metric.eventually_nhds_iff] at h_ev
    obtain ⟨ε, hε_pos, hε⟩ := h_ev
    use ε, hε_pos
    intro y hy
    have hy_pos : 0 < p.derivative.aeval y := hε hy
    nlinarith
  · have hd_neg : p.derivative.aeval x < 0 := by
      have h_le : ¬ 0 < p.derivative.aeval x := hd_pos
      have h_lt_or_gt := lt_or_gt_of_ne hd
      rcases h_lt_or_gt with h_neg | h_pos
      · exact h_neg
      · exact absurd h_pos h_le
    have h_ev : ∀ᶠ y in 𝓝 x, p.derivative.aeval y < 0 := by
      have h_mem : Set.Iio (0 : ℝ) ∈ 𝓝 (p.derivative.aeval x) := Iio_mem_nhds hd_neg
      exact hcont.eventually_mem h_mem
    rw [Metric.eventually_nhds_iff] at h_ev
    obtain ⟨ε, hε_pos, hε⟩ := h_ev
    use ε, hε_pos
    intro y hy
    have hy_neg : p.derivative.aeval y < 0 := hε hy
    nlinarith

lemma mvt_right_sign (p : Polynomial ℚ) (x : ℝ) (hd : p.derivative.aeval x ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (h_sign : ∀ y, dist y x < ε → p.derivative.aeval y * p.derivative.aeval x > 0)
    (y : ℝ) (hy : x < y) (hy_lt : y < x + ε) (hx : p.aeval x = 0) :
    0 < p.aeval y * p.derivative.aeval x := by
  let f := fun t : ℝ => p.aeval t
  let f' := fun t : ℝ => p.derivative.aeval t
  have h_hasDeriv : ∀ c ∈ Set.Ioo x y, HasDerivAt f (f' c) c := by
    intro c _; exact p.hasDerivAt_aeval (𝕜 := ℝ) c
  have h_cont : ContinuousOn f (Set.Icc x y) := (poly_aeval_continuous p).continuousOn
  have hab : x < y := hy
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope (f := f) (f' := f') hab h_cont h_hasDeriv
  have hc_dist : dist c x < ε := by
    have h_c_lt : c < x + ε := lt_trans hc_mem.2 hy_lt
    have h_c_gt : x < c := hc_mem.1
    have h1 : c - x < ε := by linarith
    have h2 : 0 ≤ c - x := by linarith
    have h_abs : |c - x| = c - x := abs_of_nonneg h2
    have h_dist_eq : dist c x = |c - x| := by rw [Real.dist_eq]
    rw [h_dist_eq, h_abs]
    exact h1
  have h_sign_c : 0 < f' c * f' x := h_sign c hc_dist
  have h_fx : f x = 0 := hx
  have h_eq : f' c = (f y - f x) / (y - x) := hc_eq
  rw [h_fx] at h_eq
  have h_yx_pos : 0 < y - x := by linarith
  have h_fy_eq : f y = f' c * (y - x) := by
    have h1 : f' c = f y / (y - x) := by rw [h_eq]; simp
    calc f y = f y / (y - x) * (y - x) := by field_simp
      _ = f' c * (y - x) := by rw [← h1]
  have h_prod_pos : 0 < f' c * f' x := h_sign_c
  have h : 0 < f y * f' x := by
    calc f y * f' x = (f' c * (y - x)) * f' x := by rw [h_fy_eq]
      _ = f' c * f' x * (y - x) := by ring
      _ > 0 := mul_pos h_prod_pos h_yx_pos
  exact h

lemma mvt_left_sign (p : Polynomial ℚ) (x : ℝ) (hd : p.derivative.aeval x ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (h_sign : ∀ y, dist y x < ε → p.derivative.aeval y * p.derivative.aeval x > 0)
    (y : ℝ) (hy : y < x) (hy_gt : x - ε < y) (hx : p.aeval x = 0) :
    p.aeval y * p.derivative.aeval x < 0 := by
  let f := fun t : ℝ => p.aeval t
  let f' := fun t : ℝ => p.derivative.aeval t
  have h_hasDeriv : ∀ c ∈ Set.Ioo y x, HasDerivAt f (f' c) c := by
    intro c _; exact p.hasDerivAt_aeval (𝕜 := ℝ) c
  have h_cont : ContinuousOn f (Set.Icc y x) := (poly_aeval_continuous p).continuousOn
  have hab : y < x := hy
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope (f := f) (f' := f') hab h_cont h_hasDeriv
  have hc_dist : dist c x < ε := by
    have h_c_gt : x - ε < c := lt_trans hy_gt hc_mem.1
    have h_c_lt : c < x := hc_mem.2
    have h1 : x - c < ε := by linarith
    have h2 : 0 ≤ x - c := by linarith
    have h_abs : |c - x| = x - c := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have h_dist_eq : dist c x = |c - x| := by rw [Real.dist_eq]
    rw [h_dist_eq, h_abs]
    exact h1
  have h_sign_c : 0 < f' c * f' x := h_sign c hc_dist
  have h_fx : f x = 0 := hx
  have h_eq : f' c = (f x - f y) / (x - y) := hc_eq
  rw [h_fx] at h_eq
  have h_yx_pos : 0 < x - y := by linarith
  have h_fy_eq : f y = f' c * (y - x) := by
    have h1 : f' c = (- f y) / (x - y) := by rw [h_eq]; ring
    have h2 : f' c * (x - y) = - f y := by
      have : f' c * (x - y) = (- f y / (x - y)) * (x - y) := by rw [← h1]
      rw [this]; field_simp
    have : y - x = -(x - y) := by ring
    linarith
  have h_prod_pos : 0 < f' c * f' x := h_sign_c
  have h_yx_neg : y - x < 0 := by linarith
  have h : f y * f' x < 0 := by
    calc f y * f' x = (f' c * (y - x)) * f' x := by rw [h_fy_eq]
      _ = f' c * f' x * (y - x) := by ring
      _ < 0 := mul_neg_of_pos_of_neg h_prod_pos h_yx_neg
  exact h

theorem simple_root_sign_change (p : Polynomial ℚ) (x : ℝ) (hx : p.aeval x = 0)
    (hd : p.derivative.aeval x ≠ 0) :
    ∃ l r : ℝ, l < x ∧ x < r ∧ p.aeval l * p.aeval r < 0 := by
  obtain ⟨ε, hε_pos, h_sign⟩ := exists_deriv_sign_nhd p x hd
  let l := x - ε / 2
  let r := x + ε / 2
  have hl_lt : l < x := by simp [l]; linarith
  have hx_lt_r : x < r := by simp [r]; linarith
  have hl_gt : x - ε < l := by simp [l]; linarith
  have hr_lt : r < x + ε := by simp [r]; linarith
  have hl_sign : p.aeval l * p.derivative.aeval x < 0 :=
    mvt_left_sign p x hd ε hε_pos h_sign l hl_lt hl_gt hx
  have hr_sign : 0 < p.aeval r * p.derivative.aeval x :=
    mvt_right_sign p x hd ε hε_pos h_sign r hx_lt_r hr_lt hx
  have h_prod : p.aeval l * p.aeval r < 0 := by
    by_cases hd_pos : 0 < p.derivative.aeval x
    · have hl_neg : p.aeval l < 0 := by nlinarith
      have hr_pos : 0 < p.aeval r := by nlinarith
      nlinarith
    · have hd_neg : p.derivative.aeval x < 0 := by
        have h_ne : p.derivative.aeval x ≠ 0 := hd
        rcases lt_or_gt_of_ne h_ne with h_neg | h_pos
        · exact h_neg
        · exact absurd h_pos hd_pos
      have hl_pos : 0 < p.aeval l := by nlinarith
      have hr_neg : p.aeval r < 0 := by nlinarith
      nlinarith
  exact ⟨l, r, hl_lt, hx_lt_r, h_prod⟩

def pointRoots (p : Polynomial ℚ) (B delta : ℚ) : List ℚ :=
  (partitionPoints B delta).filter (fun q => decide (p.eval q = 0))

def signChangingIntervals (p : Polynomial ℚ) (B delta : ℚ) : List (ℚ × ℚ) :=
  (consecutivePairs (partitionPoints B delta)).filter (fun ab => decide (p.eval ab.1 * p.eval ab.2 < 0))

inductive IsoInterval where
  | point : ℚ → IsoInterval
  | openInterval : ℚ → ℚ → IsoInterval
deriving DecidableEq, Repr

def IsoInterval.toSet : IsoInterval → Set ℝ
  | IsoInterval.point q => {(q : ℝ)}
  | IsoInterval.openInterval l r => Set.Ioo (l : ℝ) (r : ℝ)

def filteredIntervals (p : Polynomial ℚ) (B delta : ℚ) : List IsoInterval :=
  (pointRoots p B delta).map IsoInterval.point ++
  (signChangingIntervals p B delta).map (fun ab => IsoInterval.openInterval ab.1 ab.2)

lemma pointRoots_mem_iff (p : Polynomial ℚ) (B delta : ℚ) (q : ℚ) :
    q ∈ pointRoots p B delta ↔ q ∈ partitionPoints B delta ∧ p.eval q = 0 := by
  simp [pointRoots]

lemma signChangingIntervals_mem_iff (p : Polynomial ℚ) (B delta : ℚ) (a b : ℚ) :
    (a, b) ∈ signChangingIntervals p B delta ↔ (a, b) ∈ consecutivePairs (partitionPoints B delta) ∧ p.eval a * p.eval b < 0 := by
  simp [signChangingIntervals]

lemma partitionPoints_consecutive_form' (B delta : ℚ) (a b : ℚ)
    (h_mem : (a, b) ∈ consecutivePairs (partitionPoints B delta)) :
    ∃ i : ℕ, ∃ h_i : i + 1 < (partitionPoints B delta).length,
      a = (partitionPoints B delta)[i]'(Nat.lt_of_succ_lt h_i) ∧ b = (partitionPoints B delta)[i + 1]'h_i := by
  have h_eq : consecutivePairs (partitionPoints B delta) = (partitionPoints B delta).zip (partitionPoints B delta).tail := by
    simp [consecutivePairs]
  rw [h_eq] at h_mem
  rw [List.mem_iff_getElem] at h_mem
  obtain ⟨idx, h_idx, h_eq⟩ := h_mem
  have h_len_zip : ((partitionPoints B delta).zip (partitionPoints B delta).tail).length = (partitionPoints B delta).length - 1 := by
    simp [List.length_zip, List.length_tail]
  have h_idx_lt_len : idx < (partitionPoints B delta).length - 1 := by
    rw [h_len_zip] at h_idx
    exact h_idx
  have h_i_lt : idx < (partitionPoints B delta).length := by omega
  have h_ip1_lt : idx + 1 < (partitionPoints B delta).length := by omega
  have h_get_zip : ((partitionPoints B delta).zip (partitionPoints B delta).tail)[idx]'(by rw [h_len_zip]; omega) = ((partitionPoints B delta)[idx]'h_i_lt, (partitionPoints B delta)[idx + 1]'h_ip1_lt) := by
    rw [List.getElem_zip]
    have h_tail_eq : (partitionPoints B delta).tail[idx]'(by simp [List.length_tail]; omega) = (partitionPoints B delta)[idx + 1]'h_ip1_lt := by
      have h_tail_lt : idx < (partitionPoints B delta).tail.length := by simp [List.length_tail]; omega
      exact List.getElem_tail h_tail_lt
    simp [h_tail_eq]
  rw [h_get_zip] at h_eq
  exact ⟨idx, h_ip1_lt, (congrArg Prod.fst h_eq).symm, (congrArg Prod.snd h_eq).symm⟩

lemma partitionPoints_get_eq' (B delta : ℚ) (i : ℕ) (h : i < (partitionPoints B delta).length) :
    (partitionPoints B delta)[i] = -B + (i : ℚ) * delta := by
  exact partitionPoints_get B delta i h

lemma partition_interval_length' (B delta : ℚ) (a b : ℚ) (h_mem : (a, b) ∈ consecutivePairs (partitionPoints B delta)) :
    b = a + delta := by
  obtain ⟨i, h_i, h_a, h_b⟩ := partitionPoints_consecutive_form' B delta a b h_mem
  have h_i_lt : i < (partitionPoints B delta).length := Nat.lt_of_succ_lt h_i
  have h_a_eq : a = -B + (i : ℚ) * delta := by
    rw [h_a]
    exact partitionPoints_get_eq' B delta i h_i_lt
  have h_b_eq : b = -B + ((i + 1 : ℕ) : ℚ) * delta := by
    rw [h_b]
    exact partitionPoints_get_eq' B delta (i + 1) h_i
  have h_cast : ((i + 1 : ℕ) : ℚ) = (i : ℚ) + 1 := by push_cast; ring
  rw [h_cast] at h_b_eq
  have h_eq : b = a + delta := by
    rw [h_a_eq, h_b_eq]
    ring
  exact h_eq

theorem simple_root_mem_filteredIntervals (p : Polynomial ℚ) (x : ℝ) (hx : p.aeval x = 0) (hd : p.derivative.aeval x ≠ 0)
    (B : ℚ) (hB : 0 < B) (hB_spec : ∀ y : ℝ, p.aeval y = 0 → ‖y‖ ≤ ((B : ℚ) : ℝ)) :
    ∃ ε > 0, ∀ delta : ℚ, 0 < delta → (delta : ℝ) < ε → ∃ I ∈ filteredIntervals p B delta, x ∈ I.toSet := by
  obtain ⟨ε0, hε0_pos, h_sign⟩ := exists_deriv_sign_nhd p x hd
  have hε0_ne : ε0 ≠ 0 := ne_of_gt hε0_pos
  let ε := ε0 / 2
  have hε_pos : 0 < ε := by positivity
  have hε_lt : ε < ε0 := by
    have : ε = ε0 / 2 := rfl
    linarith
  use ε, hε_pos
  intro delta hDelta hDelta_small
  have hp_ne : p ≠ 0 := by intro h_eq; simp [h_eq] at hd
  have h_cover := cover_from_cauchyBound p hp_ne B hB hB_spec delta hDelta x hx
  obtain ⟨a, b, h_mem, h_x_mem⟩ := h_cover
  have h_x_le : (a : ℝ) ≤ x := h_x_mem.1
  have h_x_ge : x ≤ (b : ℝ) := h_x_mem.2
  have h_b_eq : b = a + delta := partition_interval_length' B delta a b h_mem
  have h_ba : (b : ℝ) - (a : ℝ) = (delta : ℝ) := by
    have h_eq : b = a + delta := h_b_eq
    have h_cast : ((b : ℚ) : ℝ) = ((a + delta : ℚ) : ℝ) := by rw [h_eq]
    rw [h_cast]; push_cast; ring
  have h_a_le_delta : |(a : ℝ) - x| ≤ (delta : ℝ) := by
    have h_dist_eq : |(a : ℝ) - x| = x - (a : ℝ) := by rw [abs_of_nonpos (by linarith)]; ring
    have h_le2 : x - (a : ℝ) ≤ (b : ℝ) - (a : ℝ) := by linarith
    calc |(a : ℝ) - x| = x - (a : ℝ) := h_dist_eq
      _ ≤ (b : ℝ) - (a : ℝ) := h_le2
      _ = (delta : ℝ) := h_ba
  have h_b_le_delta : |(b : ℝ) - x| ≤ (delta : ℝ) := by
    have h_dist_eq : |(b : ℝ) - x| = (b : ℝ) - x := by rw [abs_of_nonneg (by linarith)]
    have h_le2 : (b : ℝ) - x ≤ (b : ℝ) - (a : ℝ) := by linarith
    calc |(b : ℝ) - x| = (b : ℝ) - x := h_dist_eq
      _ ≤ (b : ℝ) - (a : ℝ) := h_le2
      _ = (delta : ℝ) := h_ba
  have h_a_dist : dist (a : ℝ) x < ε0 := by
    have h_eq : dist (a : ℝ) x = |(a : ℝ) - x| := by rw [Real.dist_eq]
    rw [h_eq]
    calc |(a : ℝ) - x| ≤ (delta : ℝ) := h_a_le_delta
      _ < ε := hDelta_small
      _ < ε0 := hε_lt
  have h_b_dist : dist (b : ℝ) x < ε0 := by
    have h_eq : dist (b : ℝ) x = |(b : ℝ) - x| := by rw [Real.dist_eq]
    rw [h_eq]
    calc |(b : ℝ) - x| ≤ (delta : ℝ) := h_b_le_delta
      _ < ε := hDelta_small
      _ < ε0 := hε_lt
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
    use IsoInterval.point a
    constructor
    · exact h_iso
    · simp [IsoInterval.toSet, h_x_eq_a]
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
      use IsoInterval.point b
      constructor
      · exact h_iso
      · simp [IsoInterval.toSet, h_x_eq_b]
    · have h_a_lt_x : (a : ℝ) < x := lt_of_le_of_ne h_x_le (Ne.symm h_x_eq_a)
      have h_x_lt_b : x < (b : ℝ) := lt_of_le_of_ne h_x_ge h_x_eq_b
      have h_a_sign : p.aeval (a : ℝ) * p.derivative.aeval x < 0 := by
        have h_gt : x - ε0 < (a : ℝ) := by
          have h_dist_lt : dist (a : ℝ) x < ε0 := h_a_dist
          rw [Real.dist_eq] at h_dist_lt
          have h_abs : |(a : ℝ) - x| = x - (a : ℝ) := by rw [abs_of_nonpos (by linarith)]; ring
          rw [h_abs] at h_dist_lt
          linarith
        exact mvt_left_sign p x hd ε0 hε0_pos h_sign (a : ℝ) h_a_lt_x h_gt hx
      have h_b_sign : 0 < p.aeval (b : ℝ) * p.derivative.aeval x := by
        have h_lt : (b : ℝ) < x + ε0 := by
          have h_dist_lt : dist (b : ℝ) x < ε0 := h_b_dist
          rw [Real.dist_eq] at h_dist_lt
          have h_abs : |(b : ℝ) - x| = (b : ℝ) - x := by rw [abs_of_nonneg (by linarith)]
          rw [h_abs] at h_dist_lt
          linarith
        exact mvt_right_sign p x hd ε0 hε0_pos h_sign (b : ℝ) h_x_lt_b h_lt hx
      have h_prod : p.eval a * p.eval b < 0 := by
        have h_aeval_a : p.aeval (a : ℝ) = ((p.eval a : ℚ) : ℝ) := aeval_coe_eq_coe_eval p a
        have h_aeval_b : p.aeval (b : ℝ) = ((p.eval b : ℚ) : ℝ) := aeval_coe_eq_coe_eval p b
        have h_a_sign' : ((p.eval a : ℚ) : ℝ) * p.derivative.aeval x < 0 := by rw [← h_aeval_a]; exact h_a_sign
        have h_b_sign' : 0 < ((p.eval b : ℚ) : ℝ) * p.derivative.aeval x := by rw [← h_aeval_b]; exact h_b_sign
        by_cases hd_pos : 0 < p.derivative.aeval x
        · have ha_neg : ((p.eval a : ℚ) : ℝ) < 0 := by nlinarith
          have hb_pos : 0 < ((p.eval b : ℚ) : ℝ) := by nlinarith
          have h_prod_real : ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) < 0 := mul_neg_of_neg_of_pos ha_neg hb_pos
          have h_cast : ((p.eval a * p.eval b : ℚ) : ℝ) = ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) := by push_cast; ring
          rw [← h_cast] at h_prod_real
          exact_mod_cast h_prod_real
        · have hd_neg : p.derivative.aeval x < 0 := by
            rcases lt_or_gt_of_ne hd with h_neg | h_pos
            · exact h_neg
            · exact absurd h_pos hd_pos
          have ha_pos : 0 < ((p.eval a : ℚ) : ℝ) := by nlinarith
          have hb_neg : ((p.eval b : ℚ) : ℝ) < 0 := by nlinarith
          have h_prod_real : ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) < 0 := mul_neg_of_pos_of_neg ha_pos hb_neg
          have h_cast : ((p.eval a * p.eval b : ℚ) : ℝ) = ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) := by push_cast; ring
          rw [← h_cast] at h_prod_real
          exact_mod_cast h_prod_real
      have h_open : (a, b) ∈ signChangingIntervals p B delta := by
        rw [signChangingIntervals_mem_iff]; exact ⟨h_mem, h_prod⟩
      have h_iso : IsoInterval.openInterval a b ∈ filteredIntervals p B delta := by
        simp only [filteredIntervals, List.mem_append, List.mem_map]
        right
        exact ⟨(a, b), h_open, rfl⟩
      use IsoInterval.openInterval a b
      constructor
      · exact h_iso
      · simp [IsoInterval.toSet]; exact ⟨h_a_lt_x, h_x_lt_b⟩


end
end RootIsolation.SimpleRoots
