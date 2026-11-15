module
public import Mathlib.Tactic

@[expose] public section
set_option linter.unusedVariables false

/-!
# Decreasing Branch — Lemma w:wk:lem:branch (Appendix w:app:weak)

For `k > 0` and `z ≥ 0` define `f_z(k) = k + 2·z + z²/k`.
This file proves the elementary monotonicity actually used in Appendix w:app:weak:

* `f_z` decreases on `(0, z]` and increases on `[z, ∞)` when `z > 0`,
  by direct algebra `f(a)-f(b) = (a-b)(ab - z²)/(ab)`, no calculus;
* the `z = 0` case is handled separately (`f_0(k) = k`);
* the comparison form for replacing `k` by `k* ≤ k`:
  if the projected value is ≤ `4c` whenever `k* ≤ z`,
  then `f(k*) ≤ max{ f(k), 4c }`.

This is the scalar ingredient behind the `k+2z+z²/k` branch split
in Lemma w:wk:lem:branch: on the decreasing branch the projected
condition is ≤ `4c`, on the increasing branch ordinary monotonicity
applies. The hypothesis `c ≤ 1/4` (i.e. `q ≥ -1`) is what makes the
endpoint values `Ψ(s,s)` and `Ψ(s,s-h)` ≤ `4c` in SOURCE.md.

All proofs are algebraic; only `propext`, `Classical.choice`, `Quot.sound`
appear in `#print axioms`.
-/

noncomputable section

namespace WeakCurvature.DecreasingBranch

-- Definition used in Lemma w:wk:lem:geometry / w:wk:lem:branch
-- For k > 0, z ≥ 0 :  f(k) = k + 2z + z²/k
def f_branch (z k : ℝ) : ℝ := k + 2 * z + z ^ 2 / k

-- Algebraic identity: f(a) - f(b) = (a-b)(ab - z²)/(ab)
-- This is the core computation, no derivatives.
theorem f_branch_sub_eq (z a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    f_branch z a - f_branch z b = (a - b) * (a * b - z ^ 2) / (a * b) := by
  unfold f_branch
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h : (z ^ 2 / a - z ^ 2 / b) = z ^ 2 * (b - a) / (a * b) := by
    field_simp [ha, hb, hab]
  calc f_branch z a - f_branch z b = (a - b) + (z ^ 2 / a - z ^ 2 / b) := by unfold f_branch; ring
    _ = (a - b) + z ^ 2 * (b - a) / (a * b) := by rw [h]
    _ = (a - b) * (a * b - z ^ 2) / (a * b) := by field_simp [hab]; ring

-- Alternative form useful for sign analysis
theorem f_branch_sub_eq' (z a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    f_branch z a - f_branch z b = (a - b) * (1 - z ^ 2 / (a * b)) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hab : a * b ≠ 0 := mul_ne_zero ha' hb'
  have h1 := f_branch_sub_eq z a b ha' hb'
  have h2 : (a - b) * (a * b - z ^ 2) / (a * b) = (a - b) * (1 - z ^ 2 / (a * b)) := by
    field_simp [hab]
  linarith

-- Minimum value at k = z (for z > 0): f(z) = 4z
theorem f_branch_at_z (z : ℝ) (hz : 0 < z) : f_branch z z = 4 * z := by
  unfold f_branch
  have hz' : z ≠ 0 := ne_of_gt hz
  field_simp
  ring

-- Lower bound: f(k) ≥ 4z for z > 0? Let's prove f(k) ≥ 4z? Actually for z>0, minimum is 4z.
-- Check: f(k) - 4z = k + z²/k -2z = (k - z)²/k ≥ 0
theorem f_branch_ge_four_z (z k : ℝ) (_hz : 0 ≤ z) (hk : 0 < k) : 4 * z ≤ f_branch z k := by
  unfold f_branch
  have hk' : k ≠ 0 := ne_of_gt hk
  have hk_pos : 0 < k := hk
  have h_eq : k + 2 * z + z ^ 2 / k - 4 * z = (k - z) ^ 2 / k := by
    field_simp [hk']
    ring
  have h_nn : 0 ≤ (k - z) ^ 2 / k := by
    apply div_nonneg (sq_nonneg _) (le_of_lt hk_pos)
  linarith [h_eq, h_nn]

-- For z = 0, f_0(k) = k
theorem f_branch_zero (k : ℝ) (hk : k ≠ 0) : f_branch 0 k = k := by
  unfold f_branch
  simp

-- Decreasing on (0, z] : if 0 < a ≤ b ≤ z then f(b) ≤ f(a)
theorem f_branch_decreasing_on_Ioc {z a b : ℝ} (hz : 0 < z) (ha : 0 < a) (hab : a ≤ b) (hbz : b ≤ z) :
    f_branch z b ≤ f_branch z a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hab_ne : a * b ≠ 0 := mul_ne_zero ha' hb'
  have h_sub := f_branch_sub_eq z a b ha' hb'
  -- Need to show f(a) - f(b) ≥ 0
  -- f(a)-f(b) = (a-b)(ab - z²)/(ab)
  -- Since a ≤ b, a-b ≤ 0
  -- Since a ≤ b ≤ z, ab ≤ b² ≤ z² (actually ab ≤ z²)
  have h_ab_le : a * b ≤ z ^ 2 := by
    calc a * b ≤ b * b := by nlinarith
      _ ≤ z * z := by nlinarith
      _ = z ^ 2 := by ring
  have h_ab_z : a * b - z ^ 2 ≤ 0 := by linarith
  have h_a_b : a - b ≤ 0 := by linarith
  have h_ab_pos : 0 < a * b := mul_pos ha hb
  have h1 : 0 ≤ (a - b) * (a * b - z ^ 2) := by
    -- product of two nonpositives is nonnegative
    have h1 : 0 ≤ -(a - b) := by linarith
    have h2 : 0 ≤ -(a * b - z ^ 2) := by linarith
    nlinarith
  have h2 : 0 ≤ (a - b) * (a * b - z ^ 2) / (a * b) := by
    apply div_nonneg
    · exact h1
    · linarith
  have h_eq : f_branch z a - f_branch z b = (a - b) * (a * b - z ^ 2) / (a * b) := h_sub
  linarith

-- Strict version not needed, but we have non-strict.

-- Increasing on [z, ∞) : if z ≤ a ≤ b and a > 0 then f(a) ≤ f(b)
theorem f_branch_increasing_on_Ici {z a b : ℝ} (hz : 0 ≤ z) (ha : z ≤ a) (hab : a ≤ b) (ha_pos : 0 < a) :
    f_branch z a ≤ f_branch z b := by
  have hb : 0 < b := lt_of_lt_of_le ha_pos hab
  have ha' : a ≠ 0 := ne_of_gt ha_pos
  have hb' : b ≠ 0 := ne_of_gt hb
  have h_sub := f_branch_sub_eq z a b ha' hb'
  -- f(a)-f(b) = (a-b)(ab - z²)/(ab)
  -- Now a-b ≤ 0 and ab - z² ≥ 0 (since z ≤ a ≤ b => z² ≤ a² ≤ ab? need check)
  have h_ab_ge : z ^ 2 ≤ a * b := by
    calc z ^ 2 = z * z := by ring
      _ ≤ a * a := by nlinarith
      _ ≤ a * b := by nlinarith
  have h_ab_z : 0 ≤ a * b - z ^ 2 := by linarith
  have h_a_b : a - b ≤ 0 := by linarith
  have h_ab_pos : 0 < a * b := mul_pos ha_pos hb
  have h_prod_nonpos : (a - b) * (a * b - z ^ 2) ≤ 0 := by nlinarith
  have h_div_nonpos : (a - b) * (a * b - z ^ 2) / (a * b) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact h_prod_nonpos
    · linarith
  have h_eq : f_branch z a - f_branch z b = (a - b) * (a * b - z ^ 2) / (a * b) := h_sub
  linarith

-- Combined statement: decreases on (0,z] and increases on [z,∞) for z>0
theorem f_branch_monotone_decr_incr {z : ℝ} (hz : 0 < z) :
    (∀ a b, 0 < a → a ≤ b → b ≤ z → f_branch z b ≤ f_branch z a) ∧
    (∀ a b, z ≤ a → a ≤ b → f_branch z a ≤ f_branch z b) := by
  constructor
  · intro a b ha hab hbz
    exact f_branch_decreasing_on_Ioc hz ha hab hbz
  · intro a b ha hab
    have ha_pos : 0 < a := lt_of_lt_of_le hz ha
    exact f_branch_increasing_on_Ici (le_of_lt hz) ha hab ha_pos

-- z = 0 case: f_0 is strictly increasing (actually f_0(k)=k)
theorem f_branch_zero_monotone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    f_branch 0 a ≤ f_branch 0 b := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hab)
  have : f_branch 0 a = a := f_branch_zero a ha'
  have : f_branch 0 b = b := f_branch_zero b hb'
  linarith

-- Comparison lemma: if k* ≤ k and the projected value on the decreasing branch is ≤ 4c,
-- then f(k*) ≤ max{ f(k), 4c }.
-- This is exactly the branch split in Lemma w:wk:lem:branch:
--  * if k* ≤ z, hypothesis gives f(k*) ≤ 4c,
--  * else z ≤ k* ≤ k, monotonicity on increasing branch gives f(k*) ≤ f(k).
theorem f_branch_comparison_max {z k kstar c : ℝ}
    (hk : 0 < k) (hkstar : 0 < kstar) (hz : 0 ≤ z)
    (h_le : kstar ≤ k)
    (h_branch_small : kstar ≤ z → f_branch z kstar ≤ 4 * c) :
    f_branch z kstar ≤ max (f_branch z k) (4 * c) := by
  by_cases h_kstar_le_z : kstar ≤ z
  · -- Decreasing branch: hypothesis directly gives ≤ 4c
    have h1 : f_branch z kstar ≤ 4 * c := h_branch_small h_kstar_le_z
    calc f_branch z kstar ≤ 4 * c := h1
      _ ≤ max (f_branch z k) (4 * c) := le_max_right _ _
  · -- Increasing branch: z < k* ≤ k
    have hz_lt : z < kstar := not_le.mp h_kstar_le_z
    have hz_le_kstar : z ≤ kstar := le_of_lt hz_lt
    have h_mono : f_branch z kstar ≤ f_branch z k := by
      apply f_branch_increasing_on_Ici hz hz_le_kstar h_le hkstar
    calc f_branch z kstar ≤ f_branch z k := h_mono
      _ ≤ max (f_branch z k) (4 * c) := le_max_left _ _

-- Specialization to the paper's use: with k* ≤ k, either k* ≤ z (projected ≤4c) or z ≤ k* ≤ k (monotone)
theorem branch_lemma_full {z k kstar c : ℝ}
    (hk : 0 < k) (hkstar : 0 < kstar) (hz : 0 ≤ z)
    (h_le : kstar ≤ k)
    (h_small_branch : kstar ≤ z → f_branch z kstar ≤ 4 * c) :
    f_branch z kstar ≤ max (f_branch z k) (4 * c) :=
  f_branch_comparison_max hk hkstar hz h_le h_small_branch

-- z = 0 degenerate case: decreasing branch empty, only increasing applies
theorem branch_lemma_zero {k kstar c : ℝ} (hk : 0 < k) (hkstar : 0 < kstar) (h_le : kstar ≤ k) :
    f_branch 0 kstar ≤ f_branch 0 k := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hkstar' : kstar ≠ 0 := ne_of_gt hkstar
  have h1 : f_branch 0 kstar = kstar := f_branch_zero kstar hkstar'
  have h2 : f_branch 0 k = k := f_branch_zero k hk'
  linarith
