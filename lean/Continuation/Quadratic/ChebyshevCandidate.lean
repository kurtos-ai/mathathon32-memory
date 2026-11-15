module
public import Continuation.Quadratic.Foundations
public import Mathlib
@[expose] public section
noncomputable section
namespace QuadraticFoundations
open Polynomial Finset Real

theorem chebM_s_comp_neg (N : ℕ) : (chebM_s N).comp (-X) = chebM_s N := by
  have hEq : chebM N = X * chebM_s N := chebM_eq_X_mul_s N
  have hchebEval : ∀ x : ℝ, (chebM N).eval x = x * (chebM_s N).eval x := by
    intro x
    have h := congrArg (fun p => p.eval x) hEq
    simp [eval_mul, eval_X] at h
    exact h
  have hneg : ∀ x : ℝ, (chebM N).eval (-x) = - (chebM N).eval x := chebM_eval_neg N
  have hevenEval : ∀ x : ℝ, (chebM_s N).eval (-x) = (chebM_s N).eval x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hxne : (-x : ℝ) ≠ 0 := neg_ne_zero.mpr hx
      have h1 : (chebM N).eval (-x) = (-x) * (chebM_s N).eval (-x) := hchebEval (-x)
      have h2 : (chebM N).eval x = x * (chebM_s N).eval x := hchebEval x
      have h3 : (chebM N).eval (-x) = - (chebM N).eval x := hneg x
      have h4 : (-x) * (chebM_s N).eval (-x) = - (x * (chebM_s N).eval x) := by rw [← h1, ← h2, h3]
      have h5 : (-x) * (chebM_s N).eval (-x) = (-x) * (chebM_s N).eval x := by
        have : - (x * (chebM_s N).eval x) = (-x) * (chebM_s N).eval x := by ring
        rw [this] at h4
        exact h4
      exact mul_left_cancel₀ hxne h5
  apply Polynomial.funext
  intro x
  simp [eval_comp, hevenEval x]

theorem chebM_s_odd_coeff_zero (N : ℕ) (k : ℕ) (hk : Odd k) : (chebM_s N).coeff k = 0 := by
  have hcomp := chebM_s_comp_neg N
  have hcoeff := comp_neg_X_coeff (chebM_s N) k
  rw [hcomp] at hcoeff
  have h1 : (chebM_s N).coeff k = (-1 : ℝ) ^ k * (chebM_s N).coeff k := by
    rw [← hcoeff]
  have hpow : (-1 : ℝ) ^ k = -1 := hk.neg_one_pow
  rw [hpow] at h1
  linarith

theorem chebM_derivative_eval_zero (N : ℕ) : (chebM N).derivative.eval (0 : ℝ) = (-1 : ℝ) ^ N * (2 * (N : ℝ) + 1) := by
  unfold chebM
  have h := Polynomial.Chebyshev.T_derivative_eq_U (R:=ℝ) (2 * (N : ℤ) + 1)
  have h1 : (2 * (N : ℤ) + 1 - 1 : ℤ) = 2 * (N : ℤ) := by omega
  rw [h1] at h
  rw [h]
  simp only [eval_mul, eval_intCast]
  have hU : (Polynomial.Chebyshev.U ℝ (2 * (N : ℤ))).eval (0 : ℝ) = (-1 : ℝ) ^ N := by
    have h2 := Polynomial.Chebyshev.U_eval_two_mul_zero (R:=ℝ) (N : ℤ)
    have hcast : ((N : ℤ).negOnePow : ℝ) = (-1 : ℝ) ^ N := by
      have h3 := Int.cast_negOnePow ℝ (N : ℤ)
      have h4 : ((-1 : ℝ) ^ N : ℝ) = ((-1 : ℝ) ^ (N : ℤ) : ℝ) := by rw [zpow_natCast]
      calc ((N : ℤ).negOnePow : ℝ) = (-1 : ℝ) ^ (N : ℤ) := h3
        _ = (-1 : ℝ) ^ N := h4.symm
    rw [h2, hcast]
  rw [hU]
  have hcast2 : ((2 * (N : ℤ) + 1 : ℤ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
  calc ((2 * (N : ℤ) + 1 : ℤ) : ℝ) * (-1 : ℝ) ^ N = (-1 : ℝ) ^ N * ((2 * (N : ℤ) + 1 : ℤ) : ℝ) := by ring
    _ = (-1 : ℝ) ^ N * (2 * (N : ℝ) + 1) := by rw [hcast2]

-- evenHalve construction
noncomputable def evenHalve (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (p.coeff (2 * k))

theorem evenHalve_coeff (p : ℝ[X]) (n : ℕ) : (evenHalve p).coeff n = if n ≤ p.natDegree then p.coeff (2 * n) else 0 := by
  unfold evenHalve
  by_cases hn : n ≤ p.natDegree
  · have hn_mem : n ∈ Finset.range (p.natDegree + 1) := by simp [hn]
    have h1 : (∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (p.coeff (2 * k))).coeff n = p.coeff (2 * n) := by
      rw [Polynomial.finsetSum_coeff]
      have h2 : ∀ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial k (p.coeff (2 * k))).coeff n = if k = n then p.coeff (2 * n) else 0 := by
        intro k hk
        rw [Polynomial.coeff_monomial]
        by_cases hk_eq : k = n
        · subst hk_eq; simp
        · simp [hk_eq]
      have h3 : ∑ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial k (p.coeff (2 * k))).coeff n =
          ∑ k ∈ Finset.range (p.natDegree + 1), (if k = n then p.coeff (2 * n) else (0 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact h2 k hk
      rw [h3]
      rw [Finset.sum_ite_eq' (Finset.range (p.natDegree + 1)) n (fun _ => p.coeff (2 * n))]
      simp [hn_mem]
    rw [h1]
    simp [hn]
  · simp only [hn, ite_false]
    have h1 : (∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (p.coeff (2 * k))).coeff n = 0 := by
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Polynomial.coeff_monomial]
      have hk_lt : k < p.natDegree + 1 := Finset.mem_range.mp hk
      have hk_le : k ≤ p.natDegree := by omega
      by_cases hkn : k = n
      · subst hkn; omega
      · simp [hkn]
    rw [h1]

-- Helper for monomial composition with X^2
theorem monomial_comp_X_sq (k : ℕ) (a : ℝ) : (Polynomial.monomial k a).comp (X ^ 2 : ℝ[X]) = Polynomial.monomial (2 * k) a := by
  have h1 : (Polynomial.monomial k a : ℝ[X]) = C a * X ^ k := by rw [C_mul_X_pow_eq_monomial]
  rw [h1]
  simp [mul_comp, C_comp, pow_comp, X_comp]
  have h2 : (X ^ 2 : ℝ[X]) ^ k = X ^ (2 * k) := by
    rw [← pow_mul, mul_comm]
  rw [h2]
  rw [C_mul_X_pow_eq_monomial]

theorem sum_comp_lemma {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ[X]) (q : ℝ[X]) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Polynomial.add_comp, ih]

theorem evenHalve_comp_X_sq (p : ℝ[X]) (hp_even : p.comp (-X) = p) : (evenHalve p).comp (X ^ 2 : ℝ[X]) = p := by
  unfold evenHalve
  rw [sum_comp_lemma]
  have h1 : ∀ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial k (p.coeff (2 * k))).comp (X ^ 2 : ℝ[X]) = Polynomial.monomial (2 * k) (p.coeff (2 * k)) := by
    intro k hk
    exact monomial_comp_X_sq k (p.coeff (2 * k))
  have h2 : ∑ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial k (p.coeff (2 * k))).comp (X ^ 2 : ℝ[X]) =
      ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial (2 * k) (p.coeff (2 * k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h1 k hk
  rw [h2]
  apply Polynomial.ext
  intro n
  have hcoeff : (∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial (2 * k) (p.coeff (2 * k))).coeff n = p.coeff n := by
    rw [Polynomial.finsetSum_coeff]
    by_cases hn_even : Even n
    · obtain ⟨m, hm⟩ := hn_even
      rw [show n = 2 * m from by omega]
      by_cases hm_le : m ≤ p.natDegree
      · have hm_mem : m ∈ Finset.range (p.natDegree + 1) := by simp [hm_le]
        have h_single : ∑ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial (2 * k) (p.coeff (2 * k))).coeff (2 * m) = p.coeff (2 * m) := by
          have h2 : ∀ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial (2 * k) (p.coeff (2 * k))).coeff (2 * m) = if k = m then p.coeff (2 * m) else 0 := by
            intro k hk
            rw [Polynomial.coeff_monomial]
            by_cases hkm : k = m
            · subst hkm; simp
            · have h1 : 2 * k ≠ 2 * m := by omega
              simp [h1, hkm]
          have h3 : ∑ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial (2 * k) (p.coeff (2 * k))).coeff (2 * m) =
              ∑ k ∈ Finset.range (p.natDegree + 1), (if k = m then p.coeff (2 * m) else (0 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact h2 k hk
          rw [h3]
          rw [Finset.sum_ite_eq' (Finset.range (p.natDegree + 1)) m (fun _ => p.coeff (2 * m))]
          simp [hm_mem]
        exact h_single
      · have hm_gt : p.natDegree < m := by omega
        have h_zero : ∑ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial (2 * k) (p.coeff (2 * k))).coeff (2 * m) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Polynomial.coeff_monomial]
          have hk_lt : k < p.natDegree + 1 := Finset.mem_range.mp hk
          have hk_ne : 2 * k ≠ 2 * m := by omega
          simp [hk_ne]
        rw [h_zero]
        have hcoeff_zero : p.coeff (2 * m) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hcoeff_zero]
    · have h_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
      have hp_coeff_odd : p.coeff n = 0 := by
        have hcomp := hp_even
        have hcoeff := comp_neg_X_coeff p n
        rw [hcomp] at hcoeff
        have hpow : (-1 : ℝ) ^ n = -1 := h_odd.neg_one_pow
        have h1 : p.coeff n = (-1 : ℝ) ^ n * p.coeff n := by rw [← hcoeff]
        rw [hpow] at h1
        linarith
      have h_sum_zero : ∑ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial (2 * k) (p.coeff (2 * k))).coeff n = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Polynomial.coeff_monomial]
        have : 2 * k ≠ n := by
          intro h
          have : Even n := ⟨k, by omega⟩
          contradiction
        simp [this]
      rw [h_sum_zero, hp_coeff_odd]
  exact hcoeff

noncomputable def chebM_q (N : ℕ) : ℝ[X] := evenHalve (chebM_s N)

theorem chebM_q_comp_X_sq (N : ℕ) : (chebM_q N).comp (X ^ 2 : ℝ[X]) = chebM_s N := by
  unfold chebM_q
  exact evenHalve_comp_X_sq (chebM_s N) (chebM_s_comp_neg N)

theorem chebM_s_eq_q_mul (N : ℕ) (x : ℝ) : (chebM_s N).eval x = (chebM_q N).eval (x ^ 2) := by
  have h := congrArg (fun p => p.eval x) (chebM_q_comp_X_sq N).symm
  simp [eval_comp, eval_pow, eval_X] at h
  exact h

noncomputable def p_star (N : ℕ) (L : ℝ) : ℝ[X] :=
  C (((-1 : ℝ) ^ N / (2 * (N : ℝ) + 1))) * (chebM_q N).comp (C (1 / L) * X)

theorem p_star_eval (N : ℕ) (L : ℝ) (u : ℝ) (hL : 0 < L) :
    u * (p_star N L).eval (L * u ^ 2) = ((-1 : ℝ) ^ N / (2 * (N : ℝ) + 1)) * (chebM N).eval u := by
  have hu : (1 / L : ℝ) * (L * u ^ 2) = u ^ 2 := by
    field_simp
  have hq : ((chebM_q N).comp (C (1 / L) * X)).eval (L * u ^ 2) = (chebM_s N).eval u := by
    rw [eval_comp]
    simp only [eval_mul, eval_C, eval_X, hu]
    exact (chebM_s_eq_q_mul N u).symm
  have hc : (chebM N).eval u = u * (chebM_s N).eval u := by
    rw [chebM_eq_X_mul_s N, eval_mul, eval_X]
  rw [p_star, eval_mul, eval_C, hq, hc]
  ring

theorem p_star_at_zero (N : ℕ) (L : ℝ) (_hL : 0 < L) : (p_star N L).eval 0 = 1 := by
  have hq : (p_star N L).eval (0 : ℝ) = ((-1 : ℝ) ^ N / (2 * (N : ℝ) + 1)) * (chebM_s N).eval (0 : ℝ) := by
    rw [p_star, eval_mul, eval_C]
    congr 1
    rw [eval_comp]
    simp only [eval_mul, eval_C, eval_X]
    have h0 : (1 / L : ℝ) * 0 = 0 := by ring
    rw [h0]
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] using (chebM_s_eq_q_mul N (0:ℝ)).symm
  have h_s0 : (chebM_s N).eval (0 : ℝ) = (-1 : ℝ) ^ N * (2 * (N : ℝ) + 1) := by
    have h5 := chebM_derivative_eval_zero N
    have hDeriv : (chebM N).derivative.eval (0 : ℝ) = (chebM_s N).eval (0 : ℝ) := by
      rw [chebM_eq_X_mul_s N, derivative_mul, derivative_X]
      simp only [eval_add, eval_mul, eval_X, one_mul, zero_mul, add_zero]
    linarith
  rw [hq, h_s0]
  have hsq : (-1 : ℝ) ^ N * (-1 : ℝ) ^ N = 1 := by
    rw [← pow_add, show N + N = 2 * N by ring, pow_mul]; norm_num
  have hne : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  nlinarith [hsq]


theorem p_star_natDegree_le (N : ℕ) (L : ℝ) : (p_star N L).natDegree ≤ N := by
  have hn : chebM N ≠ 0 := by
    intro h
    have hd := chebM_natDegree N
    rw [h, natDegree_zero] at hd
    omega
  have hs : chebM_s N ≠ 0 := by
    intro h
    apply hn
    rw [chebM_eq_X_mul_s N, h, mul_zero]
  have hds : (chebM_s N).natDegree = 2 * N := by
    have hd := chebM_natDegree N
    rw [chebM_eq_X_mul_s N, natDegree_X_mul hs] at hd
    omega
  have hq : (chebM_q N).natDegree ≤ N := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [chebM_q, evenHalve_coeff]
    split_ifs
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
    · rfl
  have hlin : (C (1/L) * X : ℝ[X]).natDegree ≤ 1 := by
    have h := natDegree_mul_le (p := (C (1/L) : ℝ[X])) (q := X)
    simpa using h
  have hc : ((chebM_q N).comp (C (1/L) * X)).natDegree ≤ N := by
    calc _ ≤ (chebM_q N).natDegree * (C (1/L) * X : ℝ[X]).natDegree := natDegree_comp_le
      _ ≤ N * 1 := Nat.mul_le_mul hq hlin
      _ = N := Nat.mul_one N
  have h := natDegree_mul_le
    (p := C (((-1 : ℝ)^N)/(2*(N:ℝ)+1)))
    (q := (chebM_q N).comp (C (1/L) * X))
  simp only [natDegree_C, zero_add] at h
  exact h.trans hc

theorem chebM_sq_le_one (N : ℕ) (u : ℝ) (hu : u ∈ Set.Icc (-1) 1) :
    (chebM N).eval u ^ 2 ≤ 1 := by
  conv_lhs => rw [← Real.cos_arccos hu.1 hu.2, chebM_eval_cos]
  exact Real.cos_sq_le_one _

theorem p_star_weight_identity (N : ℕ) (L : ℝ) (hL : 0 < L) (u : ℝ) :
    (L * u ^ 2) * (p_star N L).eval (L * u ^ 2) ^ 2 =
      (L / (2 * (N : ℝ) + 1)^2) * (chebM N).eval u ^ 2 := by
  have h := congrArg (fun x : ℝ => x ^ 2) (p_star_eval N L u hL)
  have hs : ((-1 : ℝ) ^ N)^2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [mul_pow, mul_pow, div_pow, hs] at h
  calc _ = L * (u ^ 2 * (p_star N L).eval (L * u ^ 2) ^ 2) := by ring
    _ = L * (1 / (2 * (N : ℝ) + 1)^2 * (chebM N).eval u ^ 2) := by rw [h]
    _ = _ := by ring

theorem p_star_weight_le (N : ℕ) (L : ℝ) (hL : 0 < L)
    (x : ℝ) (hx : x ∈ Set.Icc 0 L) :
    x * (p_star N L).eval x ^ 2 ≤ L / (2 * (N : ℝ) + 1)^2 := by
  let u := Real.sqrt (x / L)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : u ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hL).mpr hx.2)
  have hu : L * u ^ 2 = x := by
    dsimp [u]
    rw [Real.sq_sqrt (div_nonneg hx.1 hL.le)]
    field_simp
  have hid := p_star_weight_identity N L hL u
  rw [hu] at hid
  rw [hid]
  have hb := chebM_sq_le_one N u ⟨by linarith,hu1⟩
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (mul_one _)

theorem p_star_weight_at_L (N : ℕ) (L : ℝ) (hL : 0 < L) :
    L * (p_star N L).eval L ^ 2 = L / (2 * (N : ℝ) + 1)^2 := by
  have h := p_star_weight_identity N L hL 1
  simpa [chebM] using h

theorem p_star_isGreatest_weight (N : ℕ) (L : ℝ) (hL : 0 < L) :
    IsGreatest ((fun x : ℝ => x * (p_star N L).eval x ^ 2) '' Set.Icc 0 L)
      (L / (2 * (N : ℝ) + 1)^2) := by
  refine ⟨⟨L,⟨hL.le,le_refl _⟩,p_star_weight_at_L N L hL⟩,?_⟩
  rintro a ⟨x,hx,rfl⟩
  exact p_star_weight_le N L hL x hx

end QuadraticFoundations
