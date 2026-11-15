module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.MeanValue
set_option linter.unusedVariables false

@[expose] public section
open Polynomial
noncomputable section
namespace RootIsolation

def coeffAbsSum (p : Polynomial ℚ) (C : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * C ^ i

lemma aeval_bound_of_coeffAbsSum (p : Polynomial ℚ) (C : ℚ) (hC : 0 ≤ C) (x : ℝ) (hx : |x| ≤ (C : ℝ)) :
    |p.aeval x| ≤ (coeffAbsSum p C : ℝ) := by
  have h_eq : p.aeval x = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) * x ^ i :=
      (by have h := Polynomial.aeval_eq_sum_range (R := ℚ) (S := ℝ) (p := p) (x := x)
          simp only [Algebra.smul_def] at h
          exact h)
  rw [h_eq]
  calc |∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) * x ^ i|
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ) * x ^ i| := by
        have := norm_sum_le (s := Finset.range (p.natDegree + 1)) (fun i => (p.coeff i : ℝ) * x ^ i)
        simp only [Real.norm_eq_abs] at this; exact this
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * |x| ^ i := by congr 1; ext i; rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * (C : ℝ) ^ i := by
        apply Finset.sum_le_sum; intro i _; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx _) (abs_nonneg _)
    _ = (coeffAbsSum p C : ℝ) := by unfold coeffAbsSum; push_cast; rfl

lemma abs_le_C_of_mem_Icc {a b C : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ C) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) : |x| ≤ C := by
  exact abs_le.mpr ⟨by linarith [(abs_le.mp ha).1, hx.1], by linarith [(abs_le.mp hb).2, hx.2]⟩

lemma bezout_at_root (q A B : Polynomial ℚ)
    (hBezout : (A.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)) +
                B.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)).derivative) = 1)
    (x : ℝ) (hx : q.aeval x = 0) : B.aeval x * q.derivative.aeval x = 1 := by
  have h1 : (A.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)) +
              B.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)).derivative).aeval x = (1 : Polynomial ℝ).aeval x := by rw [hBezout]
  simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_one] at h1
  have hqa : (q.map (algebraMap ℚ ℝ)).aeval x = q.aeval x := by simp [Polynomial.aeval_def, Polynomial.eval_map]
  rw [hqa, hx, mul_zero, zero_add] at h1
  have hBeval : (B.map (algebraMap ℚ ℝ)).aeval x = B.aeval x := by simp [Polynomial.aeval_def, Polynomial.eval_map]
  have hqder : (q.map (algebraMap ℚ ℝ)).derivative.aeval x = q.derivative.aeval x := by rw [Polynomial.derivative_map]; simp [Polynomial.aeval_def, Polynomial.eval_map]
  rw [hBeval, hqder] at h1; exact h1

theorem separationBound_of_bezout
    (q : Polynomial ℚ) (hq : q ≠ 0) (A B : Polynomial ℚ)
    (C K M : ℚ) (hC_ge1 : 1 ≤ C) (hK_ge1 : 1 ≤ K) (hM_ge1 : 1 ≤ M)
    (hBezout : (A.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)) +
                B.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)).derivative) = 1)
    (hC : ∀ x : ℝ, q.aeval x = 0 → |x| ≤ (C : ℝ))
    (hK : (K : ℝ) ≥ (coeffAbsSum B C : ℝ))
    (hM : (M : ℝ) ≥ (coeffAbsSum (q.derivative.derivative) C : ℝ))
    (a b : ℝ) (ha : q.aeval a = 0) (hb : q.aeval b = 0) (hab : a ≠ b) :
    |a - b| ≥ (1 : ℝ) / ((K : ℝ) * (M : ℝ)) := by
  have hC0 : (0 : ℚ) ≤ C := by linarith
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by linarith)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by linarith)
  have hKM_pos : (0 : ℝ) < (K : ℝ) * (M : ℝ) := mul_pos hK_pos hM_pos
  have h_bezout_a : B.aeval a * q.derivative.aeval a = 1 := bezout_at_root q A B hBezout a ha
  have h_one_le_K_q' : (1 : ℝ) ≤ (K : ℝ) * |q.derivative.aeval a| := by
    have h1 : |B.aeval a| * |q.derivative.aeval a| = 1 := by
      calc |B.aeval a| * |q.derivative.aeval a| = |B.aeval a * q.derivative.aeval a| := (abs_mul _ _).symm
        _ = |1| := by rw [h_bezout_a]
        _ = 1 := abs_one
    have h2 : |B.aeval a| ≤ (K : ℝ) := by
      calc |B.aeval a| ≤ (coeffAbsSum B C : ℝ) := aeval_bound_of_coeffAbsSum B C hC0 a (hC a ha)
        _ ≤ (K : ℝ) := hK
    nlinarith [abs_nonneg (q.derivative.aeval a)]
  have h_lt_or_gt : a < b ∨ b < a := lt_or_gt_of_ne hab
  have h_main : ∀ {a b : ℝ}, a < b → q.aeval a = 0 → q.aeval b = 0 → |a - b| ≥ 1 / ((K : ℝ) * (M : ℝ)) := by
    intro a' b' h_lt ha' hb'
    let f : ℝ → ℝ := fun x => q.aeval x
    have hf_cont : ContinuousOn f (Set.Icc a' b') := (Polynomial.continuous_aeval q).continuousOn
    have hf_eq : f a' = f b' := by simp [f, ha', hb']
    obtain ⟨c, hc_mem, hc_deriv⟩ := exists_deriv_eq_zero h_lt hf_cont hf_eq
    have hc_deriv_eq : q.derivative.aeval c = 0 := by
      have h1 : deriv f c = q.derivative.aeval c := Polynomial.deriv_aeval (q := q) (x := c)
      rw [h1] at hc_deriv; exact hc_deriv
    let g : ℝ → ℝ := fun x => q.derivative.aeval x
    have hg_hasDeriv : ∀ x, HasDerivAt g (q.derivative.derivative.aeval x) x :=
      fun x => Polynomial.hasDerivAt_aeval (q := q.derivative) (x := x)
    have hg_diff : ∀ x ∈ Set.Icc a' b', DifferentiableAt ℝ g x := fun x _ => (hg_hasDeriv x).differentiableAt
    have hg_bound : ∀ x ∈ Set.Icc a' b', ‖deriv g x‖ ≤ (M : ℝ) := by
      intro x hx
      have hx_abs : |x| ≤ (C : ℝ) := abs_le_C_of_mem_Icc (hC a' ha') (hC b' hb') (le_of_lt h_lt) hx
      have hg_eq : deriv g x = q.derivative.derivative.aeval x := Polynomial.deriv_aeval (q := q.derivative) (x := x)
      rw [hg_eq, Real.norm_eq_abs]
      calc |q.derivative.derivative.aeval x| ≤ (coeffAbsSum (q.derivative.derivative) C : ℝ) :=
            aeval_bound_of_coeffAbsSum _ C hC0 x hx_abs
        _ ≤ (M : ℝ) := hM
    have hg_convex : Convex ℝ (Set.Icc a' b') := convex_Icc a' b'
    have ha_mem : a' ∈ Set.Icc a' b' := Set.left_mem_Icc.mpr (le_of_lt h_lt)
    have hc_mem_Icc : c ∈ Set.Icc a' b' := Set.Ioo_subset_Icc_self hc_mem
    have h_lip := Convex.norm_image_sub_le_of_norm_deriv_le hg_diff hg_bound hg_convex ha_mem hc_mem_Icc
    have h_g_eq : g c = 0 := by simp [g, hc_deriv_eq]
    have h_g_a : g a' = q.derivative.aeval a' := rfl
    have h_norm : ‖g c - g a'‖ = |q.derivative.aeval a'| := by
      rw [h_g_eq, h_g_a, show (0 : ℝ) - q.derivative.aeval a' = -(q.derivative.aeval a') from by ring, norm_neg, Real.norm_eq_abs]
    have h_dist : ‖c - a'‖ = |c - a'| := Real.norm_eq_abs _
    have h_le1 : |q.derivative.aeval a'| ≤ (M : ℝ) * |c - a'| := by
      have h1 := h_lip; rw [h_norm, h_dist] at h1; exact h1
    have h_c_le_b : |c - a'| ≤ |b' - a'| := by
      have h1 : a' < c := hc_mem.1
      have h2 : c < b' := hc_mem.2
      have h3 : 0 ≤ c - a' := by linarith
      have h4 : 0 ≤ b' - a' := by linarith
      have h5 : c - a' ≤ b' - a' := by linarith
      rw [abs_of_nonneg h3, abs_of_nonneg h4]; exact h5
    have h_le2 : |q.derivative.aeval a'| ≤ (M : ℝ) * |b' - a'| :=
      le_trans h_le1 (mul_le_mul_of_nonneg_left h_c_le_b (le_of_lt hM_pos))
    have h_bezout_a' : B.aeval a' * q.derivative.aeval a' = 1 := bezout_at_root q A B hBezout a' ha'
    have h1_le : (1 : ℝ) ≤ (K : ℝ) * |q.derivative.aeval a'| := by
      have h1 : |B.aeval a'| * |q.derivative.aeval a'| = 1 := by
        calc |B.aeval a'| * |q.derivative.aeval a'| = |B.aeval a' * q.derivative.aeval a'| := (abs_mul _ _).symm
          _ = |1| := by rw [h_bezout_a']
          _ = 1 := abs_one
      have h2 : |B.aeval a'| ≤ (K : ℝ) := by
        calc |B.aeval a'| ≤ (coeffAbsSum B C : ℝ) := aeval_bound_of_coeffAbsSum B C hC0 a' (hC a' ha')
          _ ≤ (K : ℝ) := hK
      nlinarith [abs_nonneg (q.derivative.aeval a')]
    have h2_le : (1 : ℝ) ≤ (K : ℝ) * ((M : ℝ) * |b' - a'|) :=
      le_trans h1_le (mul_le_mul_of_nonneg_left h_le2 (le_of_lt hK_pos))
    have h3 : (1 : ℝ) ≤ (K : ℝ) * (M : ℝ) * |b' - a'| := by
      have : (K : ℝ) * ((M : ℝ) * |b' - a'|) = (K : ℝ) * (M : ℝ) * |b' - a'| := by ring
      linarith
    have h4 : |a' - b'| = |b' - a'| := abs_sub_comm a' b'
    have h5 : (1 : ℝ) / ((K : ℝ) * (M : ℝ)) ≤ |a' - b'| := by rw [h4, div_le_iff₀ hKM_pos]; linarith
    exact h5
  rcases h_lt_or_gt with h_lt | h_gt
  · exact h_main h_lt ha hb
  · rw [abs_sub_comm]; exact h_main h_gt hb ha

def separationEps (K M : ℚ) : ℚ := 1 / (2 * K * M)
lemma separationEps_pos (K M : ℚ) (hK : 0 < K) (hM : 0 < M) : 0 < separationEps K M := by unfold separationEps; positivity
lemma separationEps_le (K M : ℚ) (hK : 1 ≤ K) (hM : 1 ≤ M) : (separationEps K M : ℝ) ≤ 1 / ((K : ℝ) * (M : ℝ)) := by
  unfold separationEps
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by linarith)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by linarith)
  have hKM_pos : (0 : ℝ) < (K : ℝ) * (M : ℝ) := mul_pos hK_pos hM_pos
  have h_le : (K : ℝ) * (M : ℝ) ≤ 2 * (K : ℝ) * (M : ℝ) := by nlinarith
  have h_inv : 1 / (2 * (K : ℝ) * (M : ℝ)) ≤ 1 / ((K : ℝ) * (M : ℝ)) := one_div_le_one_div_of_le hKM_pos h_le
  have h_eq : ((1 / (2 * K * M) : ℚ) : ℝ) = 1 / (2 * (K : ℝ) * (M : ℝ)) := by push_cast; ring
  rw [h_eq]; exact h_inv

theorem separation_ge_eps
    (q : Polynomial ℚ) (hq : q ≠ 0) (A B : Polynomial ℚ)
    (C K M : ℚ) (hC_ge1 : 1 ≤ C) (hK_ge1 : 1 ≤ K) (hM_ge1 : 1 ≤ M)
    (hBezout : (A.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)) +
                B.map (algebraMap ℚ ℝ) * (q.map (algebraMap ℚ ℝ)).derivative) = 1)
    (hC : ∀ x : ℝ, q.aeval x = 0 → |x| ≤ (C : ℝ))
    (hK : (K : ℝ) ≥ (coeffAbsSum B C : ℝ))
    (hM : (M : ℝ) ≥ (coeffAbsSum (q.derivative.derivative) C : ℝ))
    (a b : ℝ) (ha : q.aeval a = 0) (hb : q.aeval b = 0) (hab : a ≠ b) :
    |a - b| ≥ (separationEps K M : ℝ) := by
  have h_main := separationBound_of_bezout q hq A B C K M hC_ge1 hK_ge1 hM_ge1 hBezout hC hK hM a b ha hb hab
  have h_le := separationEps_le K M hK_ge1 hM_ge1
  linarith

def squarefreePart (p : Polynomial ℚ) : Polynomial ℚ :=
  p / EuclideanDomain.gcd p p.derivative

lemma squarefreePart_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) : squarefreePart p ≠ 0 := by
  unfold squarefreePart
  intro h
  have h_gcd_ne_zero : EuclideanDomain.gcd p p.derivative ≠ 0 := by
    intro h0; have h1 := (EuclideanDomain.gcd_eq_zero_iff).mp h0; exact hp h1.1
  have h1 : p = 0 := by
    calc p = EuclideanDomain.gcd p p.derivative * (p / EuclideanDomain.gcd p p.derivative) :=
            (EuclideanDomain.mul_div_cancel' h_gcd_ne_zero (EuclideanDomain.gcd_dvd_left _ _)).symm
      _ = EuclideanDomain.gcd p p.derivative * 0 := by rw [h]
      _ = 0 := by simp
  exact hp h1

theorem existsBezout_of_coprime (q : Polynomial ℚ) (hq : IsCoprime q q.derivative) :
    ∃ A B : Polynomial ℚ, A * q + B * q.derivative = 1 := hq

theorem existsBezout_of_gcd_one (q : Polynomial ℚ) (hq : EuclideanDomain.gcd q q.derivative = 1) :
    ∃ A B : Polynomial ℚ, A * q + B * q.derivative = 1 := by
  have h_gcd_eq : (EuclideanDomain.gcd q q.derivative : Polynomial ℚ) =
      q * EuclideanDomain.gcdA q q.derivative + q.derivative * EuclideanDomain.gcdB q q.derivative := EuclideanDomain.gcd_eq_gcd_ab q q.derivative
  rw [hq] at h_gcd_eq
  refine ⟨EuclideanDomain.gcdA q q.derivative, EuclideanDomain.gcdB q q.derivative, ?_⟩
  have h_comm : q * EuclideanDomain.gcdA q q.derivative + q.derivative * EuclideanDomain.gcdB q q.derivative =
                EuclideanDomain.gcdA q q.derivative * q + EuclideanDomain.gcdB q q.derivative * q.derivative := by ring
  rw [h_comm] at h_gcd_eq; exact h_gcd_eq.symm

lemma squarefreePart_dvd (p : Polynomial ℚ) : squarefreePart p ∣ p := by
  unfold squarefreePart; exact EuclideanDomain.div_dvd_of_dvd (EuclideanDomain.gcd_dvd_left _ _)

theorem root_of_squarefreePart_root (p : Polynomial ℚ) (a : ℝ) (h : (squarefreePart p).aeval a = 0) :
    p.aeval a = 0 := by
  have h_dvd : squarefreePart p ∣ p := squarefreePart_dvd p
  obtain ⟨r, hr⟩ := h_dvd
  rw [hr, Polynomial.aeval_mul, h, zero_mul]



end RootIsolation
