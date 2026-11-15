module
public import Continuation.Quadratic.Lower.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial
@[expose] public section
noncomputable section

/-!
# Quadratic alternation lower bound

For every `N`, every `L > 0`, and every `p : ℝ[X]` with `natDegree ≤ N` and `p.eval 0 = 1`,
there is `x ∈ [0,L]` with `L/(2N+1)^2 ≤ x * p.eval x ^ 2`.

Strategy: with `u_j = cos (jπ/M)`, `M = 2N+1`, the extremal identity
`u_j * p_star (L u_j^2) = (-1)^(N+j)/M` forces any strictly better `p` to give
`q = p - p_star` alternating signs at the `N+1` points, hence `N` interior roots plus
the root at `0`, contradicting `natDegree q ≤ N`.
-/
namespace QuadraticLower
open Polynomial Real QuadraticFoundations
open scoped Interval

def altU (N : ℕ) (j : ℕ) : ℝ := Real.cos ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1))
def altX (N : ℕ) (L : ℝ) (j : ℕ) : ℝ := L * (altU N j) ^ 2

lemma angle_lt_pi_div_two (N : ℕ) (j : ℕ) (hj : j ≤ N) :
    (j : ℝ) * Real.pi / (2 * (N : ℝ) + 1) < Real.pi / 2 := by
  have hM : (0 : ℝ) < 2 * (N : ℝ) + 1 := M_pos N
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2j : (2 * (j : ℝ) < 2 * (N : ℝ) + 1) := by
    have : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
    linarith
  calc (j : ℝ) * Real.pi / (2 * (N : ℝ) + 1)
      = (j : ℝ) / (2 * (N : ℝ) + 1) * Real.pi := by ring
    _ < (1 / 2 : ℝ) * Real.pi := by
        apply mul_lt_mul_of_pos_right _ hpi
        rw [div_lt_div_iff₀ hM (by norm_num : (0:ℝ) < 2)]
        linarith
    _ = Real.pi / 2 := by ring

lemma angle_mem_Icc_pi (N : ℕ) (j : ℕ) (hj : j ≤ N) :
    (j : ℝ) * Real.pi / (2 * (N : ℝ) + 1) ∈ Set.Icc (0 : ℝ) Real.pi := by
  constructor
  · exact angle_nonneg N j
  · calc (j : ℝ) * Real.pi / (2 * (N : ℝ) + 1)
        ≤ (N : ℝ) * Real.pi / (2 * (N : ℝ) + 1) := by
          apply div_le_div_of_nonneg_right _ (M_pos N).le
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) Real.pi_pos.le
      _ ≤ Real.pi := by
          rw [div_le_iff₀ (M_pos N)]
          nlinarith [Real.pi_pos]

lemma altU_pos (N : ℕ) (j : ℕ) (hj : j ≤ N) : 0 < altU N j := by
  unfold altU
  have h0 : 0 ≤ (j : ℝ) * Real.pi / (2 * (N : ℝ) + 1) := angle_nonneg N j
  have h1 : (j : ℝ) * Real.pi / (2 * (N : ℝ) + 1) < Real.pi / 2 := angle_lt_pi_div_two N j hj
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

lemma altU_nonneg (N : ℕ) (j : ℕ) (hj : j ≤ N) : 0 ≤ altU N j := (altU_pos N j hj).le
lemma altU_le_one (N : ℕ) (j : ℕ) : altU N j ≤ 1 := by unfold altU; exact Real.cos_le_one _
lemma altX_nonneg (N : ℕ) (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : j ≤ N) : 0 ≤ altX N L j := by unfold altX; positivity
lemma altX_pos (N : ℕ) (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : j ≤ N) : 0 < altX N L j := by unfold altX; have hu := altU_pos N j hj; positivity
lemma altX_le_L (N : ℕ) (L : ℝ) (hL : 0 < L) (j : ℕ) : altX N L j ≤ L := by
  unfold altX
  have h1 : (altU N j) ^ 2 ≤ 1 := by
    have h3 : -1 ≤ altU N j := by unfold altU; exact Real.neg_one_le_cos _
    have h4 : altU N j ≤ 1 := altU_le_one N j
    nlinarith [sq_nonneg (altU N j), sq_nonneg (altU N j - 1)]
  nlinarith
lemma altX_mem_Icc (N : ℕ) (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : j ≤ N) :
    altX N L j ∈ Set.Icc 0 L := ⟨altX_nonneg N L hL j hj, altX_le_L N L hL j⟩
lemma altX_zero : altX N L 0 = L := by unfold altX altU; simp

lemma angle_strictMono_aux (N : ℕ) (a b : ℕ) (hab : a < b) :
    (a : ℝ) * Real.pi / (2 * (N : ℝ) + 1) < (b : ℝ) * Real.pi / (2 * (N : ℝ) + 1) := by
  have hM : (0 : ℝ) < 2 * (N : ℝ) + 1 := M_pos N
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have ha : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  exact div_lt_div_of_pos_right (by nlinarith) hM

lemma altU_strictAnti_on (N : ℕ) : StrictAntiOn (fun j : ℕ => altU N j) (Set.Icc 0 N) := by
  intro a ha b hb hab
  unfold altU
  have hang := angle_strictMono_aux N a b hab
  have ha_mem := angle_mem_Icc_pi N a ha.2
  have hb_mem := angle_mem_Icc_pi N b hb.2
  exact Real.strictAntiOn_cos ha_mem hb_mem hang

lemma altX_strictAnti_on (N : ℕ) (L : ℝ) (hL : 0 < L) :
    StrictAntiOn (fun j : ℕ => altX N L j) (Set.Icc 0 N) := by
  intro a ha b hb hab
  unfold altX
  have hu_anti := altU_strictAnti_on N ha hb hab
  have ha_le : a ≤ N := ha.2
  have hb_le : b ≤ N := hb.2
  have h_sq : (altU N b) ^ 2 < (altU N a) ^ 2 := by
    have h1 : altU N b < altU N a := hu_anti
    nlinarith [sq_nonneg (altU N a), sq_nonneg (altU N b), sq_nonneg (altU N a - altU N b), altU_nonneg N a ha_le, altU_nonneg N b hb_le]
  nlinarith

lemma altX_injOn (N : ℕ) (L : ℝ) (hL : 0 < L) : Set.InjOn (fun j : ℕ => altX N L j) (Set.Icc 0 N) := by
  intro a ha b hb heq
  by_contra hne
  have hlt_or_gt : a < b ∨ b < a := by omega
  rcases hlt_or_gt with hlt | hlt
  · have hanti := altX_strictAnti_on N L hL ha hb hlt; linarith
  · have hanti := altX_strictAnti_on N L hL hb ha hlt; linarith

lemma altU_mul_p_star (N : ℕ) (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : j ≤ N) :
    altU N j * (p_star N L).eval (altX N L j) = (-1 : ℝ) ^ (N + j) / (2 * (N : ℝ) + 1) := by
  have h1 := p_star_eval N L (altU N j) hL
  have h2 : L * (altU N j) ^ 2 = altX N L j := by unfold altX; ring
  rw [h2] at h1
  have hcheb : (chebM N).eval (altU N j) = Real.cos ((j : ℝ) * Real.pi) := by
    unfold altU
    have hc := chebM_eval_cos N ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1))
    have harg : (2 * (N : ℝ) + 1) * ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1)) = (j : ℝ) * Real.pi := by field_simp
    rw [harg] at hc; exact hc
  rw [hcheb] at h1
  have hcos_jpi : Real.cos ((j : ℝ) * Real.pi) = (-1 : ℝ) ^ j := by
    have hj_cast : (j : ℝ) * Real.pi = ((j : ℤ) : ℝ) * Real.pi := by push_cast; ring
    rw [hj_cast]
    have hcos_int : Real.cos (((j : ℤ) : ℝ) * Real.pi) = ((-1 : ℝ) ^ (j : ℤ)) := by
      have := Real.cos_int_mul_pi (j : ℤ)
      have h_eq : ((-1 : ℝ) ^ (j : ℤ) : ℝ) = ((-1 : ℝ) ^ j : ℝ) := by rw [zpow_natCast]
      rw [h_eq] at this; exact this
    exact hcos_int
  rw [hcos_jpi] at h1
  have hpow : (-1 : ℝ) ^ N * (-1 : ℝ) ^ j = (-1 : ℝ) ^ (N + j) := by rw [pow_add]
  calc altU N j * (p_star N L).eval (altX N L j)
      = (-1 : ℝ) ^ N / (2 * (N : ℝ) + 1) * ((-1 : ℝ) ^ j) := h1
    _ = (-1 : ℝ) ^ (N + j) / (2 * (N : ℝ) + 1) := by field_simp; rw [hpow]

lemma violation_bound (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (h_viol : ∀ x ∈ Set.Icc (0 : ℝ) L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2)
    (j : ℕ) (hj : j ≤ N) :
    |altU N j * p.eval (altX N L j)| < 1 / (2 * (N : ℝ) + 1) := by
  have hx_mem := altX_mem_Icc N L hL j hj
  have h_viol_j := h_viol (altX N L j) hx_mem
  have h_eq : altX N L j * p.eval (altX N L j) ^ 2 = L * ((altU N j * p.eval (altX N L j)) ^ 2) := by unfold altX; ring
  rw [h_eq] at h_viol_j
  have h1 : (altU N j * p.eval (altX N L j)) ^ 2 < (1 / (2 * (N : ℝ) + 1)) ^ 2 := by
    have h_eq2 : L / (2 * (N : ℝ) + 1) ^ 2 = L * ((1 / (2 * (N : ℝ) + 1)) ^ 2) := by
      have hM : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have h_L_div : L * ((altU N j * p.eval (altX N L j)) ^ 2) < L * ((1 / (2 * (N : ℝ) + 1)) ^ 2) := by
      rw [← h_eq2]
      exact h_viol_j
    exact lt_of_mul_lt_mul_left h_L_div hL.le
  have h_abs_sq_lt : |altU N j * p.eval (altX N L j)| ^ 2 < (1 / (2 * (N : ℝ) + 1)) ^ 2 := by
    calc |altU N j * p.eval (altX N L j)| ^ 2 = (|altU N j * p.eval (altX N L j)|) ^ 2 := rfl
      _ < (1 / (2 * (N : ℝ) + 1)) ^ 2 := by
        have : |altU N j * p.eval (altX N L j)| ^ 2 = (altU N j * p.eval (altX N L j)) ^ 2 := sq_abs _
        rw [this]
        exact h1
  have h_nn : 0 ≤ 1 / (2 * (N : ℝ) + 1) := by positivity
  nlinarith [sq_nonneg (|altU N j * p.eval (altX N L j)| - 1 / (2 * (N : ℝ) + 1)),
             sq_nonneg (|altU N j * p.eval (altX N L j)| + 1 / (2 * (N : ℝ) + 1)),
             abs_nonneg (altU N j * p.eval (altX N L j))]

lemma neg_one_pow_eq_or (n : ℕ) : ((-1 : ℝ) ^ n = 1) ∨ ((-1 : ℝ) ^ n = -1) := by
  have h2 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h_cases : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
    have := sq_eq_one_iff.mp h2
    rcases this with h | h
    · left; linarith
    · right; linarith
  exact h_cases

lemma q_sign (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (h_viol : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2)
    (j : ℕ) (hj : j ≤ N) :
    (altU N j * (p - p_star N L).eval (altX N L j) < 0 ∧ (-1 : ℝ) ^ (N + j) = 1) ∨
    (altU N j * (p - p_star N L).eval (altX N L j) > 0 ∧ (-1 : ℝ) ^ (N + j) = -1) := by
  have h_bound := violation_bound N L hL p h_viol j hj
  have h_p_star_val := altU_mul_p_star N L hL j hj
  have h_q_mul : altU N j * (p - p_star N L).eval (altX N L j) = altU N j * p.eval (altX N L j) - (-1 : ℝ) ^ (N + j) / (2 * (N : ℝ) + 1) := by
    have h1 : (p - p_star N L).eval (altX N L j) = p.eval (altX N L j) - (p_star N L).eval (altX N L j) := by simp [eval_sub]
    rw [h1, mul_sub, h_p_star_val]
  have h_abs : |altU N j * p.eval (altX N L j)| < 1 / (2 * (N : ℝ) + 1) := h_bound
  have h_up : altU N j * p.eval (altX N L j) < 1 / (2 * (N : ℝ) + 1) := by
    linarith [abs_nonneg (altU N j * p.eval (altX N L j)), le_abs_self (altU N j * p.eval (altX N L j))]
  have h_low : -(1 / (2 * (N : ℝ) + 1)) < altU N j * p.eval (altX N L j) := by
    linarith [neg_abs_le (altU N j * p.eval (altX N L j))]
  by_cases h_sign : (-1 : ℝ) ^ (N + j) = 1
  · left
    constructor
    · have h_eq : (-1 : ℝ) ^ (N + j) / (2 * (N : ℝ) + 1) = 1 / (2 * (N : ℝ) + 1) := by rw [h_sign]
      rw [h_eq] at h_q_mul
      linarith
    · exact h_sign
  · right
    have h_sign_neg : (-1 : ℝ) ^ (N + j) = -1 := by
      rcases neg_one_pow_eq_or (N + j) with h1 | h2
      · exact absurd h1 h_sign
      · exact h2
    constructor
    · have h_eq : (-1 : ℝ) ^ (N + j) / (2 * (N : ℝ) + 1) = -1 / (2 * (N : ℝ) + 1) := by rw [h_sign_neg]
      rw [h_eq] at h_q_mul
      have h1 : altU N j * (p - p_star N L).eval (altX N L j) = altU N j * p.eval (altX N L j) + 1 / (2 * (N : ℝ) + 1) := by
        calc altU N j * (p - p_star N L).eval (altX N L j)
            = altU N j * p.eval (altX N L j) - -1 / (2 * (N : ℝ) + 1) := h_q_mul
          _ = altU N j * p.eval (altX N L j) + 1 / (2 * (N : ℝ) + 1) := by ring
      linarith [h1]
    · exact h_sign_neg

lemma q_eval_sign_alternates (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (h_viol : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2)
    (j : ℕ) (hj : j ≤ N) :
    (0 < (p - p_star N L).eval (altX N L j) ∧ (-1 : ℝ) ^ (N + j) = -1) ∨
    ((p - p_star N L).eval (altX N L j) < 0 ∧ (-1 : ℝ) ^ (N + j) = 1) := by
  have hq := q_sign N L hL p h_viol j hj
  have hu_pos := altU_pos N j hj
  rcases hq with ⟨h_neg, h1⟩ | ⟨h_pos, h1⟩
  · right
    constructor
    · by_contra h_nn
      have h_nn' : 0 ≤ (p - p_star N L).eval (altX N L j) := by linarith
      have : 0 ≤ altU N j * (p - p_star N L).eval (altX N L j) := mul_nonneg (le_of_lt hu_pos) h_nn'
      linarith
    · exact h1
  · left
    constructor
    · by_contra h_np
      have h_np' : (p - p_star N L).eval (altX N L j) ≤ 0 := by linarith
      have : altU N j * (p - p_star N L).eval (altX N L j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu_pos) h_np'
      linarith
    · exact h1

lemma q_consecutive_opposite_sign (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (h_viol : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2)
    (j : ℕ) (hj : j + 1 ≤ N) :
    (p - p_star N L).eval (altX N L j) * (p - p_star N L).eval (altX N L (j + 1)) < 0 := by
  have h1 := q_eval_sign_alternates N L hL p h_viol j (by omega)
  have h2 := q_eval_sign_alternates N L hL p h_viol (j+1) (by omega)
  have h_pow_flip : (-1 : ℝ) ^ (N + (j + 1)) = - ((-1 : ℝ) ^ (N + j)) := by
    rw [show N + (j + 1) = (N + j) + 1 by omega, pow_succ]; ring
  rcases h1 with ⟨h_pos1, h_eq1⟩ | ⟨h_neg1, h_eq1⟩
  · have h_eq1_neg1 : (-1 : ℝ) ^ (N + j) = -1 := h_eq1
    rcases h2 with ⟨h_pos2, h_eq2⟩ | ⟨h_neg2, h_eq2⟩
    · have : (-1 : ℝ) ^ (N + (j+1)) = -1 := h_eq2
      rw [h_pow_flip, h_eq1_neg1] at this; norm_num at this
    · nlinarith
  · have h_eq1_one : (-1 : ℝ) ^ (N + j) = 1 := h_eq1
    rcases h2 with ⟨h_pos2, h_eq2⟩ | ⟨h_neg2, h_eq2⟩
    · nlinarith
    · have : (-1 : ℝ) ^ (N + (j+1)) = 1 := h_eq2
      rw [h_pow_flip, h_eq1_one] at this; norm_num at this

lemma ivt_root_between (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (h_viol : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2)
    (j : ℕ) (hj : j + 1 ≤ N) :
    ∃ c ∈ Set.Ioo (altX N L (j+1)) (altX N L j), (p - p_star N L).eval c = 0 := by
  let q := p - p_star N L
  have h_opp : q.eval (altX N L j) * q.eval (altX N L (j+1)) < 0 :=
    q_consecutive_opposite_sign N L hL p h_viol j hj
  -- symmetry: product comm
  have h_opp' : q.eval (altX N L (j+1)) * q.eval (altX N L j) < 0 := by
    have : q.eval (altX N L (j+1)) * q.eval (altX N L j) = q.eval (altX N L j) * q.eval (altX N L (j+1)) := by ring
    rw [this]; exact h_opp
  have h_anti := altX_strictAnti_on N L hL
  have ha_mem : j ∈ Set.Icc 0 N := ⟨Nat.zero_le j, by omega⟩
  have hb_mem : j+1 ∈ Set.Icc 0 N := ⟨Nat.zero_le (j+1), by omega⟩
  have h_lt : altX N L (j+1) < altX N L j := h_anti ha_mem hb_mem (by omega)
  have h_le : altX N L (j+1) ≤ altX N L j := le_of_lt h_lt
  have h_cont : ContinuousOn (fun x => q.eval x) (Set.Icc (altX N L (j+1)) (altX N L j)) := by fun_prop
  have h_ne_left : q.eval (altX N L (j+1)) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h_opp'; linarith
  have h_ne_right : q.eval (altX N L j) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h_opp'; linarith
  have h_sign : (q.eval (altX N L (j+1)) < 0 ∧ 0 < q.eval (altX N L j)) ∨
                (0 < q.eval (altX N L (j+1)) ∧ q.eval (altX N L j) < 0) := by
    rcases lt_trichotomy (q.eval (altX N L (j+1))) 0 with h_lt | h_eq | h_gt
    · left; constructor; exact h_lt; nlinarith
    · exfalso; exact h_ne_left h_eq
    · right; constructor; exact h_gt; nlinarith
  rcases h_sign with ⟨h_lo_neg, h_hi_pos⟩ | ⟨h_lo_pos, h_hi_neg⟩
  · have h_mem : (0 : ℝ) ∈ Set.Ioo (q.eval (altX N L (j+1))) (q.eval (altX N L j)) := ⟨by linarith, by linarith⟩
    obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_Ioo h_le h_cont h_mem
    exact ⟨c, hc_mem, hc_eq⟩
  · have h_mem : (0 : ℝ) ∈ Set.Ioo (q.eval (altX N L j)) (q.eval (altX N L (j+1))) := ⟨by linarith, by linarith⟩
    obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_Ioo' h_le h_cont h_mem
    exact ⟨c, hc_mem, hc_eq⟩

lemma q_natDegree_le (N : ℕ) (L : ℝ) (p : ℝ[X]) (hp_deg : p.natDegree ≤ N) :
    (p - p_star N L).natDegree ≤ N := by
  calc (p - p_star N L).natDegree
      ≤ max p.natDegree (p_star N L).natDegree := natDegree_sub_le _ _
    _ ≤ N := Nat.max_le.mpr ⟨hp_deg, p_star_natDegree_le N L⟩

lemma q_eval_zero (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X]) (hp_zero : p.eval 0 = 1) :
    (p - p_star N L).eval 0 = 0 := by simp [eval_sub, hp_zero, p_star_at_zero N L hL]

lemma q_isRoot_zero (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X]) (hp_zero : p.eval 0 = 1) :
    (p - p_star N L).IsRoot 0 := by rw [Polynomial.IsRoot, q_eval_zero N L hL p hp_zero]

-- Helper to build Finset of roots via choice and proving disjointness
-- We will directly prove the contradiction without explicitly building Finset,
-- using polynomial root cardinality bound.

-- For the degree contradiction, we need to show that if q has N+1 distinct roots then
-- card ≤ natDegree, so N+1 ≤ natDegree ≤ N gives False.
-- We construct the set of roots: {0} ∪ {c_j : j < N} where c_j ∈ (x_{j+1}, x_j).

-- First prove intervals are disjoint and not containing 0
lemma altX_intervals_disjoint (N : ℕ) (L : ℝ) (hL : 0 < L) (a b : ℕ) (ha : a + 1 ≤ N) (hb : b + 1 ≤ N) (hab : a ≠ b) :
    Set.Ioo (altX N L (a+1)) (altX N L a) ∩ Set.Ioo (altX N L (b+1)) (altX N L b) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have h1 := hy.1
  have h2 := hy.2
  rcases Nat.lt_or_ge a b with h_lt | h_ge
  · have h_le : a + 1 ≤ b := Nat.succ_le_of_lt h_lt
    have ha1_mem : a + 1 ∈ Set.Icc 0 N := ⟨Nat.zero_le _, ha⟩
    have hb_mem : b ∈ Set.Icc 0 N := ⟨Nat.zero_le _, Nat.le_of_succ_le hb⟩
    have h_xb_le : altX N L b ≤ altX N L (a + 1) := by
      rcases Nat.eq_or_lt_of_le h_le with h_eq | h_lt2
      · rw [← h_eq]
      · exact le_of_lt (altX_strictAnti_on N L hL ha1_mem hb_mem h_lt2)
    have h_y1 : altX N L (a + 1) < y := h1.1
    have h_y2 : y < altX N L b := h2.2
    linarith
  · have h_lt : b < a := by omega
    have h_le : b + 1 ≤ a := Nat.succ_le_of_lt h_lt
    have hb1_mem : b + 1 ∈ Set.Icc 0 N := ⟨Nat.zero_le _, hb⟩
    have ha_mem : a ∈ Set.Icc 0 N := ⟨Nat.zero_le _, Nat.le_of_succ_le ha⟩
    have h_xa_le : altX N L a ≤ altX N L (b + 1) := by
      rcases Nat.eq_or_lt_of_le h_le with h_eq | h_lt2
      · rw [← h_eq]
      · exact le_of_lt (altX_strictAnti_on N L hL hb1_mem ha_mem h_lt2)
    have h_y1 : y < altX N L a := h1.2
    have h_y2 : altX N L (b + 1) < y := h2.1
    linarith

lemma Ioo_not_contain_zero (N : ℕ) (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : j + 1 ≤ N) :
    (0 : ℝ) ∉ Set.Ioo (altX N L (j+1)) (altX N L j) := by
  intro h_mem
  have h_pos : 0 < altX N L (j+1) := altX_pos N L hL (j+1) (by omega)
  linarith [h_mem.1]

-- Finset of roots helper (unused placeholder, kept for namespace)

-- Main degree contradiction via counting
lemma degree_contradiction (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (hp_deg : p.natDegree ≤ N) (hp_zero : p.eval 0 = 1)
    (h_viol : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2) : False := by
  let q := p - p_star N L
  have h_q_deg : q.natDegree ≤ N := q_natDegree_le N L p hp_deg
  have h_q_root0 : q.IsRoot 0 := q_isRoot_zero N L hL p hp_zero
  -- First handle q=0 case: then p = p_star, but p_star attains bound, contradiction
  by_cases h_q_zero : q = 0
  · -- q=0 => p = p_star
    have h_p_eq : p = p_star N L := by
      have : p - p_star N L = 0 := h_q_zero
      exact sub_eq_zero.mp this
    -- Then p_star at L attains L / M^2, violating h_viol at x=L
    have h_at_L : L ∈ Set.Icc (0:ℝ) L := ⟨hL.le, le_refl _⟩
    have h_viol_L := h_viol L h_at_L
    rw [h_p_eq] at h_viol_L
    have h_star_val := p_star_weight_at_L N L hL
    have h_eq : L * (p_star N L).eval L ^ 2 = L / (2 * (N : ℝ) + 1) ^ 2 := h_star_val
    linarith
  · -- q ≠ 0, we have N intervals giving N distinct roots plus 0 => N+1 roots
    -- We need to produce N+1 distinct roots and apply card_le_degree_of_subset_roots
    -- Construct the set of roots: for each j < N, pick c_j ∈ (x_{j+1}, x_j) with q(c_j)=0
    have h_exists_roots : ∀ j : ℕ, j < N → ∃ c ∈ Set.Ioo (altX N L (j+1)) (altX N L j), q.eval c = 0 := by
      intro j hj
      exact ivt_root_between N L hL p h_viol j (by omega)
    -- Use choice to get function
    choose c hc_mem hc_eq using h_exists_roots
    -- Define Finset S = {0} ∪ {c j | j < N}
    -- Need to show card = N+1 and all are roots
    -- Instead of building Finset directly, we can use the cardinality lemma:
    -- We have N distinct c_j plus 0, total N+1.
    -- Let's build Finset explicitly via Finset.range
    let S0 : Finset ℝ := Finset.image (fun j : Fin N => c j.val j.isLt) Finset.univ
    have h_S0_card : S0.card = N := by
      have h_inj : Function.Injective (fun j : Fin N => c j.val j.isLt) := by
        intro a b hab
        have ha_mem := hc_mem a.val a.isLt
        have hb_mem := hc_mem b.val b.isLt
        have ha_eq : c a.val a.isLt = c b.val b.isLt := hab
        by_contra hne
        have h_ne : (a.val : ℕ) ≠ b.val := by
          intro h_eq
          have : a = b := Fin.ext h_eq
          contradiction
        have h_disj := altX_intervals_disjoint N L hL a.val b.val (by omega) (by omega) h_ne
        have h_inter_mem : c a.val a.isLt ∈ Set.Ioo (altX N L (a.val+1)) (altX N L a.val) ∩ Set.Ioo (altX N L (b.val+1)) (altX N L b.val) := by
          constructor
          · exact ha_mem
          · rw [ha_eq]; exact hb_mem
        have h_empty : (Set.Ioo (altX N L (a.val+1)) (altX N L a.val) ∩ Set.Ioo (altX N L (b.val+1)) (altX N L b.val)).Nonempty := ⟨c a.val a.isLt, h_inter_mem⟩
        have h_not_empty : (Set.Ioo (altX N L (a.val+1)) (altX N L a.val) ∩ Set.Ioo (altX N L (b.val+1)) (altX N L b.val)) = ∅ := h_disj
        rw [h_not_empty] at h_inter_mem
        exact Set.notMem_empty _ h_inter_mem
      have h_card_univ : (Finset.univ : Finset (Fin N)).card = N := by simp
      rw [Finset.card_image_of_injective _ h_inj, h_card_univ]
    have h_zero_not_in_S0 : (0 : ℝ) ∉ S0 := by
      intro h_mem
      rw [Finset.mem_image] at h_mem
      obtain ⟨j, _, h_eq⟩ := h_mem
      have h_mem_j : (0 : ℝ) ∈ Set.Ioo (altX N L (j.val + 1)) (altX N L j.val) := by
        rw [← h_eq]
        exact hc_mem j.val j.isLt
      exact Ioo_not_contain_zero N L hL j.val (by omega) h_mem_j
    let S : Finset ℝ := insert (0 : ℝ) S0
    have h_S_card : S.card = N + 1 := by
      rw [Finset.card_insert_of_notMem h_zero_not_in_S0, h_S0_card]
    have h_S_subset_roots : S.val ⊆ q.roots := by
      intro x hx
      rw [Finset.mem_val] at hx
      -- x ∈ S means x=0 or x = c j for some j
      have h_mem : x ∈ S := Finset.mem_val.mp hx
      rw [Finset.mem_insert] at h_mem
      rcases h_mem with rfl | h_mem_S0
      · -- x=0
        rw [Polynomial.mem_roots h_q_zero]
        exact h_q_root0
      · -- x ∈ S0
        have h_in_S0 : x ∈ S0 := h_mem_S0
        rw [Finset.mem_image] at h_in_S0
        obtain ⟨j, _, rfl⟩ := h_in_S0
        have h_root : q.eval (c j.val j.isLt) = 0 := hc_eq j.val j.isLt
        rw [Polynomial.mem_roots h_q_zero]
        exact by rw [Polynomial.IsRoot, h_root]
    -- Now apply the cardinality bound: card ≤ natDegree
    have h_card_le : S.card ≤ q.natDegree := by
      have h := Polynomial.card_le_degree_of_subset_roots h_S_subset_roots
      -- h : S.card ≤ Multiset.card q.roots, and Multiset.card q.roots ≤ natDegree
      have h2 := Polynomial.card_roots' q
      omega
    -- But S.card = N+1 and q.natDegree ≤ N, contradiction
    have h_q_deg_le_N : q.natDegree ≤ N := h_q_deg
    omega

theorem strict_lower_bound (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (hp_deg : p.natDegree ≤ N) (hp_zero : p.eval 0 = 1) :
    ¬ (∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2) := by
  intro h_viol
  exact degree_contradiction N L hL p hp_deg hp_zero h_viol

theorem lower_bound_N0 (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (hp_deg : p.natDegree ≤ 0) (hp_zero : p.eval 0 = 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) L, L / (2 * ((0 : ℕ) : ℝ) + 1) ^ 2 ≤ x * p.eval x ^ 2 := by
  have h_p_eq_one : p = 1 := by
    have h_deg0 : p.natDegree = 0 := by omega
    have h_eq : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h_deg0
    have h_coeff : p.coeff 0 = p.eval 0 := by simp [Polynomial.coeff_zero_eq_eval_zero]
    rw [h_coeff] at h_eq
    rw [h_eq, hp_zero]; simp
  have hnorm : L / (2 * ((0:ℕ):ℝ) + 1) ^ 2 = L := by norm_num
  refine ⟨L, ⟨hL.le, le_refl _⟩, ?_⟩
  rw [h_p_eq_one, hnorm]
  simp

theorem quadratic_lower_bound (N : ℕ) (L : ℝ) (hL : 0 < L) (p : ℝ[X])
    (hp_deg : p.natDegree ≤ N) (hp_zero : p.eval 0 = 1) :
    ∃ x ∈ Set.Icc 0 L, L / (2 * (N : ℝ) + 1) ^ 2 ≤ x * p.eval x ^ 2 := by
  by_cases hN0 : N = 0
  · subst hN0
    exact lower_bound_N0 L hL p hp_deg hp_zero
  · by_contra h_neg
    -- h_neg : ¬∃ x ∈ Icc 0 L, L/M^2 ≤ x*p(x)^2
    -- So ∀ x ∈ Icc, ¬(L/M^2 ≤ x*p^2) => ∀ x ∈ Icc, x*p^2 < L/M^2
    have h_viol : ∀ x ∈ Set.Icc (0:ℝ) L, x * p.eval x ^ 2 < L / (2 * (N : ℝ) + 1) ^ 2 := by
      intro x hx
      have h_not_le : ¬ (L / (2 * (N : ℝ) + 1) ^ 2 ≤ x * p.eval x ^ 2) := by
        intro h_le
        exact h_neg ⟨x, hx, h_le⟩
      exact lt_of_not_ge h_not_le
    exact strict_lower_bound N L hL p hp_deg hp_zero h_viol


/-! ## Complete quadratic lower bound

Every predetermined method's error polynomial `p_N(d,T)` has `natDegree ≤ N` and
`p_N(0) = 1`; `history_risk_value` attains `R^2/2 * L/(2N+1)^2` with the one-register
schedule. The theorem below is the missing lower half: **no** polynomial of degree
`≤ N` with value `1` at `0` beats the constant `L/(2N+1)^2` on `[0,L]`.
-/

theorem bddAbove_eval_sq_image (L : ℝ) (p : ℝ[X]) :
    BddAbove ((fun x : ℝ => x * p.eval x ^ 2) '' Set.Icc 0 L) := by
  have hc : ContinuousOn (fun x : ℝ => x * p.eval x ^ 2) (Set.Icc 0 L) := by fun_prop
  exact (isCompact_Icc.image_of_continuousOn hc).bddAbove

theorem quadratic_lower_bound_of_degree (N : ℕ) {L : ℝ} (hL : 0 < L) (p : ℝ[X])
    (hp_deg : p.natDegree ≤ N) (hp_zero : p.eval 0 = 1) :
    L / (2 * (N : ℝ) + 1) ^ 2 ≤ sSup ((fun x : ℝ => x * p.eval x ^ 2) '' Set.Icc 0 L) := by
  obtain ⟨x, hx, hbound⟩ := quadratic_lower_bound N L hL p hp_deg hp_zero
  exact le_trans hbound (le_csSup (bddAbove_eval_sq_image L p) ⟨x, hx, rfl⟩)

end QuadraticLower
