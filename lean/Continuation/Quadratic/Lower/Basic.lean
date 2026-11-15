module
public import Continuation.Quadratic.Foundations
public import Continuation.Quadratic.ChebyshevCandidate
public import Mathlib
@[expose] public section
noncomputable section

/-!
# Quadratic lower bound: shared alternation toolkit

Alternation points `u_j = cos (jπ/M)`, `M = 2N+1`, and the counting lemma used to
turn `N+1` roots of a degree-`≤ N` difference into a contradiction.

Base: `Continuation.Quadratic.ChebyshevCandidate`
(SHA-256 6dc234a91782782309e9055cbdb27d2902115c5d0fd95fddef3ef996c0c17c3f).
-/
namespace QuadraticLower
open Polynomial Real
open QuadraticFoundations

/-- A nonzero real polynomial of `natDegree ≤ n` has at most `n` distinct roots in a
finite set. -/
theorem card_finset_roots_le {f : ℝ[X]} {n : ℕ} (hf : f ≠ 0) (hn : f.natDegree ≤ n)
    (s : Finset ℝ) (hs : ∀ x ∈ s, f.IsRoot x) : s.card ≤ n := by
  have hsub : s ≤ f.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    exact hs x hx
  calc s.card ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ ≤ n := hn

lemma M_pos (N : ℕ) : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity

lemma M_ne_zero (N : ℕ) : (2 * (N : ℝ) + 1) ≠ 0 := ne_of_gt (M_pos N)

lemma angle_nonneg (N : ℕ) (a : ℕ) : 0 ≤ (a : ℝ) * Real.pi / (2 * (N : ℝ) + 1) := by
  have hM : (0 : ℝ) < 2 * (N : ℝ) + 1 := M_pos N
  have := Real.pi_pos
  positivity

lemma angle_lt_half_pi (N : ℕ) {a : ℕ} (ha : a ≤ N) :
    (a : ℝ) * Real.pi / (2 * (N : ℝ) + 1) < Real.pi / 2 := by
  have hM : (0 : ℝ) < 2 * (N : ℝ) + 1 := M_pos N
  have ha' : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast ha
  rw [div_lt_div_iff₀ hM (by norm_num : (0 : ℝ) < 2)]
  nlinarith [Real.pi_pos]

/-- The alternation angles increase in `j` on `0 ≤ j ≤ N`, so the
points `u_j = cos (jπ/M)` strictly decrease. -/
theorem cos_altU_strictAntiOn (N : ℕ) :
    StrictAntiOn (fun j : ℕ => Real.cos ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1)))
      (Set.Icc 0 N) := by
  intro a ha b hb hab
  have hM : (0 : ℝ) < 2 * (N : ℝ) + 1 := M_pos N
  have han : (0 : ℝ) ≤ (a : ℝ) * Real.pi / (2 * (N : ℝ) + 1) := angle_nonneg N a
  have hbpi : (b : ℝ) * Real.pi / (2 * (N : ℝ) + 1) ≤ Real.pi := by
    have h := angle_lt_half_pi N hb.2
    linarith [Real.pi_pos]
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hang : (a : ℝ) * Real.pi / (2 * (N : ℝ) + 1)
      < (b : ℝ) * Real.pi / (2 * (N : ℝ) + 1) := by
    apply div_lt_div_of_pos_right _ hM
    nlinarith [Real.pi_pos]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi han hbpi hang

/-- Alternation identity of the extremal polynomial:
`u_j * p_star (L u_j²) = (-1)^(N+j) / (2N+1)`. -/
theorem cos_altU_mul_p_star (N : ℕ) (L : ℝ) (hL : 0 < L) (j : ℕ) :
    Real.cos ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1))
        * (p_star N L).eval (L * (Real.cos ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1))) ^ 2)
      = (-1 : ℝ) ^ (N + j) / (2 * (N : ℝ) + 1) := by
  have hev := p_star_eval N L (Real.cos ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1))) hL
  have hcheb := chebM_eval_cos N ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1))
  have harg : (2 * (N : ℝ) + 1) * ((j : ℝ) * Real.pi / (2 * (N : ℝ) + 1))
      = (j : ℝ) * Real.pi := by field_simp
  rw [hcheb, harg, Real.cos_nat_mul_pi] at hev
  have hpow : (-1 : ℝ) ^ N * (-1 : ℝ) ^ j = (-1 : ℝ) ^ (N + j) := by rw [pow_add]
  rw [hev]
  field_simp
  rw [hpow]

end QuadraticLower
