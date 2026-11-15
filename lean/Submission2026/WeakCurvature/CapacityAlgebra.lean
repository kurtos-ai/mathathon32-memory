module
public import Submission2026.WeakCurvature.Core

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

lemma tailPsi_zero_curvature {s t : ℝ} (hs : s ≠ 0) :
    tailPsi 0 1 s t = (s - t) ^ 2 / s := by
  unfold tailPsi
  field_simp [hs]
  ring

lemma tailPsi_diagonal {c a s : ℝ} (ha : a = 1 - 2 * c)
    (hs : s ≠ 0) (hden : a + c * s ≠ 0) :
    tailPsi c a s s = 4 * c * (1 - a * (1 - s) ^ 2 / (a + c * s)) := by
  have hd : a / s + c = (a + c * s) / s := by
    field_simp [hs]
  have hn : 1 - a * s / s - 2 * c * s = (s - a * s - 2 * c * s * s) / s := by
    field_simp [hs]
  unfold tailPsi
  rw [hd, hn]
  rw [ha] at hden ⊢
  ring_nf at hden
  field_simp [hs, hden]
  ring

lemma tailPsi_one_left {c a t : ℝ} (ha : a = 1 - 2 * c) (hc : 1 - c ≠ 0) :
    tailPsi c a 1 t = 4 * c + a ^ 2 * (1 - t) ^ 2 / (1 - c) := by
  unfold tailPsi
  simp only [div_one]
  rw [ha]
  rw [show 1 - 2 * c + c = 1 - c by ring]
  field_simp [hc]
  ring

/-- Multiplying the capacity inequality by `s*(a+c*s)` gives the displayed quadratic. -/
lemma tailPsi_sub_mul_capacity {c a ν s t : ℝ} (ha : a = 1 - 2 * c)
    (hs : s ≠ 0) (hden : a + c * s ≠ 0) :
    (tailPsi c a s t - ν) * (s * (a + c * s)) =
      capacityA c a ν t * s ^ 2 - a * capacityB c ν t * s + a ^ 2 * t ^ 2 := by
  have hd : a / s + c = (a + c * s) / s := by
    field_simp [hs]
  have hn : 1 - a * t / s - 2 * c * t = (s - a * t - 2 * c * s * t) / s := by
    field_simp [hs]
  unfold tailPsi capacityA capacityB
  rw [hd, hn]
  rw [ha] at hden ⊢
  ring_nf at hden
  field_simp [hs, hden]
  ring

/-- Exact discriminant expansion used to establish capacity validity. -/
lemma capacity_discriminant {c a ν t : ℝ} (ha : a = 1 - 2 * c) :
    capacityB c ν t ^ 2 - 4 * capacityA c a ν t * t ^ 2 =
      16 * c * (1 - t) ^ 2 * (c + a * t) +
        (ν - 4 * c) * (ν + 4 * c + 4 * (1 - 4 * c) * t + 4 * c * t ^ 2) := by
  unfold capacityA capacityB
  rw [ha]
  ring

/-- The explicit upper-root formula satisfies the quadratic capacity equation. -/
lemma capacityRoot_quadratic {c a ν t : ℝ}
    (hA : capacityA c a ν t ≠ 0)
    (hD : 0 ≤ capacityB c ν t ^ 2 - 4 * capacityA c a ν t * t ^ 2) :
    capacityA c a ν t * capacityRoot c a ν t ^ 2
      - a * capacityB c ν t * capacityRoot c a ν t + a ^ 2 * t ^ 2 = 0 := by
  let A := capacityA c a ν t
  let B := capacityB c ν t
  let r := Real.sqrt (B ^ 2 - 4 * A * t ^ 2)
  have hr : r ^ 2 = B ^ 2 - 4 * A * t ^ 2 := by
    dsimp [r]
    exact Real.sq_sqrt hD
  change A * (a * (B + r) / (2 * A)) ^ 2
    - a * B * (a * (B + r) / (2 * A)) + a ^ 2 * t ^ 2 = 0
  have hA' : A ≠ 0 := hA
  field_simp [hA']
  linear_combination a ^ 2 * hr

lemma tailPsi_diagonal_le {c a s : ℝ} (ha : a = 1 - 2 * c)
    (hc : 0 ≤ c) (ha0 : 0 ≤ a) (hs : s ≠ 0) (hden : 0 < a + c * s) :
    tailPsi c a s s ≤ 4 * c := by
  rw [tailPsi_diagonal ha hs (ne_of_gt hden)]
  have hfrac : 0 ≤ a * (1 - s) ^ 2 / (a + c * s) := by
    positivity
  have hle : 1 - a * (1 - s) ^ 2 / (a + c * s) ≤ 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ 4 * c by positivity)
  nlinarith

lemma four_mul_c_le_capacityUpper {c : ℝ} (hc0 : 0 ≤ c) (hc4 : c ≤ 1 / 4) :
    4 * c ≤ capacityUpper c := by
  have hden : 0 < 1 - c := by linarith
  unfold capacityUpper
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (1 - 2 * c)]

lemma capacityA_pos_of_nonneg_c {c a ν t : ℝ} (ha : a = 1 - 2 * c)
    (hc0 : 0 ≤ c) (hc4 : c ≤ 1 / 4) (ht1 : t ≤ 1)
    (hν : ν ≤ capacityUpper c) : 0 < capacityA c a ν t := by
  have h1c : 0 < 1 - c := by linarith
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hca : 0 ≤ 4 * c * a := by positivity
  have ht : 4 * c * a * t ≤ 4 * c * a := by
    simpa using mul_le_mul_of_nonneg_left ht1 hca
  have hcν : c * ν ≤ c * capacityUpper c := mul_le_mul_of_nonneg_left hν hc0
  have hid : 1 - 4 * c * a - c * capacityUpper c = a ^ 3 / (1 - c) := by
    unfold capacityUpper
    rw [ha]
    field_simp [ne_of_gt h1c]
    ring
  have hpos : 0 < a ^ 3 / (1 - c) := by
    have ha_pos : 0 < a := by rw [ha]; linarith
    positivity
  have hlower : a ^ 3 / (1 - c) ≤ capacityA c a ν t := by
    calc
      a ^ 3 / (1 - c) = 1 - 4 * c * a - c * capacityUpper c := hid.symm
      _ ≤ capacityA c a ν t := by
        unfold capacityA
        linarith
  exact lt_of_lt_of_le hpos hlower

lemma capacityRadicand_nonneg_of_nonneg_c {c a ν t : ℝ} (ha : a = 1 - 2 * c)
    (hc0 : 0 ≤ c) (hc4 : c ≤ 1 / 4) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hν0 : 4 * c ≤ ν) (hν1 : ν ≤ capacityUpper c) :
    0 ≤ capacityB c ν t ^ 2 - 4 * capacityA c a ν t * t ^ 2 := by
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hνnonneg : 0 ≤ ν := by linarith
  have h4c : 0 ≤ 1 - 4 * c := by linarith
  have hfirst : 0 ≤ 16 * c * (1 - t) ^ 2 * (c + a * t) := by positivity
  have hsecond : 0 ≤ (ν - 4 * c) *
      (ν + 4 * c + 4 * (1 - 4 * c) * t + 4 * c * t ^ 2) := by
    apply mul_nonneg (by linarith)
    positivity
  rw [capacity_discriminant ha]
  exact add_nonneg hfirst hsecond

lemma capacityRoot_apply_zero {c a ν : ℝ} (hν : 0 ≤ ν)
    (hA : capacityA c a ν 0 ≠ 0) :
    capacityRoot c a ν 0 = a * ν / (1 - c * ν) := by
  have hden : 1 - c * ν ≠ 0 := by simpa [capacityA] using hA
  unfold capacityRoot capacityA capacityB
  simp only [mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [Real.sqrt_sq hν]
  field_simp [hden]
  ring

lemma tailPsi_le_iff_quadratic_nonpos {c a ν s t : ℝ}
    (ha : a = 1 - 2 * c) (hs : 0 < s) (hden : 0 < a + c * s) :
    tailPsi c a s t ≤ ν ↔
      capacityA c a ν t * s ^ 2 - a * capacityB c ν t * s + a ^ 2 * t ^ 2 ≤ 0 := by
  have hfac : 0 < s * (a + c * s) := mul_pos hs hden
  have hid := tailPsi_sub_mul_capacity (ν := ν) (t := t) ha (ne_of_gt hs) (ne_of_gt hden)
  constructor
  · intro h
    have hnonpos : tailPsi c a s t - ν ≤ 0 := by linarith
    have hprod : (tailPsi c a s t - ν) * (s * (a + c * s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hfac.le
    rw [hid] at hprod
    exact hprod
  · intro h
    by_contra hn
    have hpos : 0 < tailPsi c a s t - ν := by linarith
    have hprod : 0 < (tailPsi c a s t - ν) * (s * (a + c * s)) := mul_pos hpos hfac
    rw [hid] at hprod
    linarith

lemma tailPsi_capacityRoot {c a ν t : ℝ}
    (ha : a = 1 - 2 * c) (hA : capacityA c a ν t ≠ 0)
    (hD : 0 ≤ capacityB c ν t ^ 2 - 4 * capacityA c a ν t * t ^ 2)
    (hR : 0 < capacityRoot c a ν t) (hden : 0 < a + c * capacityRoot c a ν t) :
    tailPsi c a (capacityRoot c a ν t) t = ν := by
  have hquad := capacityRoot_quadratic (c := c) (a := a) (ν := ν) (t := t) hA hD
  have hid := tailPsi_sub_mul_capacity (ν := ν) (t := t) ha (ne_of_gt hR) (ne_of_gt hden)
  have hfac : 0 < capacityRoot c a ν t * (a + c * capacityRoot c a ν t) :=
    mul_pos hR hden
  have hprod : (tailPsi c a (capacityRoot c a ν t) t - ν) *
      (capacityRoot c a ν t * (a + c * capacityRoot c a ν t)) = 0 := by
    rw [hid, hquad]
  have hzero : tailPsi c a (capacityRoot c a ν t) t - ν = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hfac)
  linarith

#print axioms tailPsi_zero_curvature
#print axioms tailPsi_diagonal
#print axioms tailPsi_one_left
#print axioms tailPsi_sub_mul_capacity
#print axioms capacity_discriminant
#print axioms capacityRoot_quadratic
#print axioms tailPsi_diagonal_le
#print axioms four_mul_c_le_capacityUpper
#print axioms capacityA_pos_of_nonneg_c
#print axioms capacityRadicand_nonneg_of_nonneg_c
#print axioms capacityRoot_apply_zero
#print axioms tailPsi_le_iff_quadratic_nonpos
#print axioms tailPsi_capacityRoot

end Submission2026.WeakCurvature
