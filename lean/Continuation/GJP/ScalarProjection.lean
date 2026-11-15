module
public import Continuation.GJP.Simplex

@[expose] public section
noncomputable section
namespace GJP

/-- Multiplication form of the nonterminal projection bound; no division by a pivot is needed. -/
lemma projected_square_bound (r d p q b s : ℝ) (hr : 0 < r) (hd : 0 ≤ d)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hprefix : d*b ≤ s)
    (hdiag : p^2/(2*r) ≤ d-q^2/2) : (p*b)^2 ≤ 2*r*s := by
  have hp : p^2 ≤ 2*r*d := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*r)).mp hdiag
    have hq : 0 ≤ r*q^2 := mul_nonneg hr.le (sq_nonneg q)
    nlinarith
  calc
    (p*b)^2 = p^2*b^2 := by ring
    _ ≤ (2*r*d)*b^2 := mul_le_mul_of_nonneg_right hp (sq_nonneg b)
    _ ≤ (2*r*d)*b := mul_le_mul_of_nonneg_left (by nlinarith : b^2 ≤ b) (by positivity)
    _ = (2*r)*(d*b) := by ring
    _ ≤ (2*r)*s := mul_le_mul_of_nonneg_left hprefix (by positivity)

lemma projected_fraction_bound (r d p q b s : ℝ) (hr : 0 < r) (hd : 0 ≤ d)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hs : 0 ≤ s) (hprefix : d*b ≤ s)
    (hdiag : p^2/(2*r) ≤ d-q^2/2) : (p*b)^2/(2*s) ≤ r := by
  by_cases hs0 : s = 0
  · simp [hs0, hr.le]
  · apply (div_le_iff₀ (by positivity : 0 < 2*s)).mpr
    have h := projected_square_bound r d p q b s hr hd hb hb1 hprefix hdiag
    nlinarith

lemma projected_terminal_bound (r d p b : ℝ) (hr : 0 < r) (hb : 0 ≤ b)
    (hrow : d*b = 1) (hdiag : p^2/(2*r) ≤ d-1/2) : (p*b)^2 ≤ r := by
  have hp : p^2 ≤ r*(2*d-1) := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*r)).mp hdiag
    nlinarith
  have hdb : d*b^2 = b := by
    calc d*b^2 = (d*b)*b := by ring
         _ = b := by rw [hrow]; ring
  have hsq := mul_le_mul_of_nonneg_right hp (sq_nonneg b)
  have hid : r*(2*d-1)*b^2 = r*(2*b-b^2) := by
    calc r*(2*d-1)*b^2 = r*(2*(d*b^2)-b^2) := by ring
         _ = r*(2*b-b^2) := by rw [hdb]
  rw [hid] at hsq
  have hlast : r*(2*b-b^2) ≤ r := by nlinarith [mul_nonneg hr.le (sq_nonneg (1-b))]
  nlinarith [mul_pow p b 2]

/-- Equality in the nonterminal projection fixes the pivot, border slack and mass. -/
lemma projected_fraction_equality (r d p q b s : ℝ) (hr : 0 < r) (hd : 0 ≤ d)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hs : 0 ≤ s) (hprefix : d*b ≤ s)
    (hdiag : p^2/(2*r) ≤ d-q^2/2) (heq : (p*b)^2/(2*s) = r) :
    b = 1 ∧ d = s ∧ q = 0 ∧ p^2/(2*r) = d := by
  have hspos : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := le_antisymm (le_of_not_gt hn) hs
    rw [hs0] at heq
    simp only [mul_zero, div_zero] at heq
    linarith
  have hsq : (p*b)^2 = r*(2*s) := (div_eq_iff (by positivity : 2*s ≠ 0)).mp heq
  have hp : p^2 ≤ 2*r*d := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*r)).mp hdiag
    nlinarith [mul_nonneg hr.le (sq_nonneg q)]
  have hchain : (p*b)^2 ≤ (2*r*s)*b := by
    calc
      (p*b)^2 = p^2*b^2 := by ring
      _ ≤ (2*r*d)*b^2 := mul_le_mul_of_nonneg_right hp (sq_nonneg b)
      _ = ((2*r)*(d*b))*b := by ring
      _ ≤ ((2*r)*s)*b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprefix (by positivity)) hb
  have hbge : 1 ≤ b := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2*r*s)).mp
    nlinarith
  have hbEq : b = 1 := le_antisymm hb1 hbge
  subst b
  simp only [mul_one] at hprefix hsq
  have hpe : p^2/(2*r) = s := by
    apply (div_eq_iff (by positivity : 2*r ≠ 0)).mpr
    nlinarith
  rw [hpe] at hdiag
  have hds : d = s := by nlinarith [sq_nonneg q]
  have hq : q = 0 := by nlinarith [sq_nonneg q]
  exact ⟨rfl, hds, hq, hpe.trans hds.symm⟩

/-- Equality in the terminal projection forces its last pivot and mass to be one. -/
lemma projected_terminal_equality (r d p b : ℝ) (hr : 0 < r) (hb : 0 ≤ b)
    (hrow : d*b = 1) (hdiag : p^2/(2*r) ≤ d-1/2) (heq : (p*b)^2 = r) :
    b = 1 ∧ d = 1 ∧ p^2/(2*r) = d-1/2 := by
  have hp : p^2 ≤ r*(2*d-1) := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*r)).mp hdiag
    nlinarith
  have hdb : d*b^2 = b := by
    calc d*b^2 = (d*b)*b := by ring
         _ = b := by rw [hrow]; ring
  have hsq := mul_le_mul_of_nonneg_right hp (sq_nonneg b)
  have hid : r*(2*d-1)*b^2 = r*(2*b-b^2) := by
    calc r*(2*d-1)*b^2 = r*(2*(d*b^2)-b^2) := by ring
         _ = r*(2*b-b^2) := by rw [hdb]
  rw [hid] at hsq
  have hs : (1-b)^2 ≤ 0 := by
    apply nonpos_of_mul_nonpos_left _ hr
    nlinarith [mul_pow p b 2]
  have hbEq : b = 1 := by nlinarith [sq_nonneg (1-b)]
  subst b
  simp only [mul_one] at hrow heq
  refine ⟨rfl, hrow, ?_⟩
  rw [heq, hrow]
  field_simp
  <;> ring

end GJP
