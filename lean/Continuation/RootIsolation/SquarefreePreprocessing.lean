module
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Polynomial

@[expose] public section
noncomputable section
namespace SquarefreePreprocessing


section GcdMin
variable {K : Type*} [Field K] [DecidableEq K]

theorem rootMultiplicity_gcd_eq_min {p q : K[X]} {a : K} (hp : p ≠ 0) (hq : q ≠ 0) :
    (EuclideanDomain.gcd p q).rootMultiplicity a = min (p.rootMultiplicity a) (q.rootMultiplicity a) := by
  have hgcd_ne_zero : EuclideanDomain.gcd p q ≠ 0 := by
    intro h
    have := (EuclideanDomain.gcd_eq_zero_iff (R := K[X])).mp h
    exact hp this.1
  have hle : (EuclideanDomain.gcd p q).rootMultiplicity a ≤ min (p.rootMultiplicity a) (q.rootMultiplicity a) := by
    apply Nat.le_min.mpr
    constructor
    · exact rootMultiplicity_le_rootMultiplicity_of_dvd hp (EuclideanDomain.gcd_dvd_left p q) a
    · exact rootMultiplicity_le_rootMultiplicity_of_dvd hq (EuclideanDomain.gcd_dvd_right p q) a
  have hdiv_p : (X - C a) ^ min (p.rootMultiplicity a) (q.rootMultiplicity a) ∣ p := by
    rw [← le_rootMultiplicity_iff hp]
    exact Nat.min_le_left _ _
  have hdiv_q : (X - C a) ^ min (p.rootMultiplicity a) (q.rootMultiplicity a) ∣ q := by
    rw [← le_rootMultiplicity_iff hq]
    exact Nat.min_le_right _ _
  have hdiv_gcd : (X - C a) ^ min (p.rootMultiplicity a) (q.rootMultiplicity a) ∣ EuclideanDomain.gcd p q := by
    exact EuclideanDomain.dvd_gcd hdiv_p hdiv_q
  have hge : min (p.rootMultiplicity a) (q.rootMultiplicity a) ≤ (EuclideanDomain.gcd p q).rootMultiplicity a := by
    rw [le_rootMultiplicity_iff hgcd_ne_zero]
    exact hdiv_gcd
  exact Nat.le_antisymm hle hge


end GcdMin

section SquarefreeDef
def squarefreePart (p : Polynomial ℚ) : Polynomial ℚ := p / EuclideanDomain.gcd p p.derivative

theorem gcd_ne_zero_of_p_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) : EuclideanDomain.gcd p p.derivative ≠ 0 := by
  intro h
  have := (EuclideanDomain.gcd_eq_zero_iff (R := Polynomial ℚ)).mp h
  exact hp this.1

theorem squarefreePart_mul {p : Polynomial ℚ} (hp : p ≠ 0) :
    EuclideanDomain.gcd p p.derivative * squarefreePart p = p := by
  unfold squarefreePart
  exact EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_p_ne_zero hp) (EuclideanDomain.gcd_dvd_left _ _)

theorem squarefreePart_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) : squarefreePart p ≠ 0 := by
  intro h
  have h1 : p = 0 := by
    calc p = EuclideanDomain.gcd p p.derivative * squarefreePart p := (squarefreePart_mul hp).symm
      _ = EuclideanDomain.gcd p p.derivative * 0 := by rw [h]
      _ = 0 := by simp
  exact hp h1

end SquarefreeDef

def qToR : ℚ →+* ℝ := algebraMap ℚ ℝ

theorem map_qToR_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) : p.map qToR ≠ 0 := Polynomial.map_ne_zero hp

theorem derivative_map_qToR (p : Polynomial ℚ) : (p.map qToR).derivative = p.derivative.map qToR := Polynomial.derivative_map _ _

theorem gcd_map_qToR (p q : Polynomial ℚ) : EuclideanDomain.gcd (p.map qToR) (q.map qToR) = (EuclideanDomain.gcd p q).map qToR := Polynomial.gcd_map qToR

theorem pR_eq_dR_mul_qR (p : Polynomial ℚ) (hp : p ≠ 0) :
    p.map qToR = (EuclideanDomain.gcd p p.derivative).map qToR * (squarefreePart p).map qToR := by
  have h_eq : p = EuclideanDomain.gcd p p.derivative * squarefreePart p := (squarefreePart_mul hp).symm
  have h1 : p.map qToR = (EuclideanDomain.gcd p p.derivative * squarefreePart p).map qToR := congrArg (fun t => t.map qToR) h_eq
  rw [Polynomial.map_mul] at h1
  exact h1

theorem aeval_eq_map_eval (p : Polynomial ℚ) (a : ℝ) : p.aeval a = (p.map qToR).eval a := by
  simp [qToR, Polynomial.aeval_def, Polynomial.eval_map]

theorem isRoot_map_iff_aeval (p : Polynomial ℚ) (a : ℝ) : (p.map qToR).IsRoot a ↔ p.aeval a = 0 := by
  rw [Polynomial.IsRoot.def, aeval_eq_map_eval]

theorem eq_C_of_deriv_eq_zero' {p : Polynomial ℚ} (h : p.derivative = 0) : ∃ c : ℚ, p = C c := ⟨p.coeff 0, eq_C_of_derivative_eq_zero h⟩

lemma nat_min_sub_one {m : ℕ} : min m (m - 1) = m - 1 := by
  apply Nat.min_eq_right
  exact Nat.sub_le m 1

lemma nat_sub_sub_one {m : ℕ} (hm : 1 ≤ m) : m - (m - 1) = 1 := by
  have h1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  calc m - (m - 1) = (m - 1 + 1) - (m - 1) := by rw [h1]
    _ = 1 := by rw [Nat.add_sub_cancel_left]

theorem squarefree_aeval_root_iff (p : Polynomial ℚ) (hp : p ≠ 0) (a : ℝ) :
    p.aeval a = 0 ↔ (squarefreePart p).aeval a = 0 := by
  rw [← isRoot_map_iff_aeval p a, ← isRoot_map_iff_aeval (squarefreePart p) a]
  have hpR : p.map qToR ≠ 0 := map_qToR_ne_zero hp
  have hdR : (EuclideanDomain.gcd p p.derivative).map qToR ≠ 0 := map_qToR_ne_zero (gcd_ne_zero_of_p_ne_zero hp)
  have hqR : (squarefreePart p).map qToR ≠ 0 := map_qToR_ne_zero (squarefreePart_ne_zero hp)
  have hpR_eq : p.map qToR = (EuclideanDomain.gcd p p.derivative).map qToR * (squarefreePart p).map qToR := pR_eq_dR_mul_qR p hp
  by_cases hder : p.derivative = 0
  · obtain ⟨c, hc⟩ : ∃ c : ℚ, p = C c := ⟨p.coeff 0, eq_C_of_derivative_eq_zero hder⟩
    have hc_ne_zero : c ≠ 0 := by
      intro hc0
      have : (C c : Polynomial ℚ) = 0 := by rw [hc0, C_0]
      rw [hc] at hp
      rw [this] at hp
      exact hp rfl
    have hpR_eq_C : p.map qToR = C (qToR c) := by
      calc p.map qToR = (C c).map qToR := by rw [hc]
        _ = C (qToR c) := by simp
    have hqR_eq_C : p.map qToR = C ((c : ℝ)) := by
      calc p.map qToR = C (qToR c) := hpR_eq_C
        _ = C ((c : ℝ)) := by simp [qToR]
    have h_gcd_eq : EuclideanDomain.gcd p p.derivative = p := by
      rw [hder]
      have : EuclideanDomain.gcd (C c : Polynomial ℚ) 0 = C c := by simp
      rw [hc, this]
    have h_q_eq : squarefreePart p = 1 := by
      unfold squarefreePart
      rw [h_gcd_eq, hc]
      exact EuclideanDomain.div_self (by
        intro h
        have : (C c : Polynomial ℚ).coeff 0 = c := by simp
        rw [h] at this
        simp at this
        exact hc_ne_zero this.symm)
    have hqR_eq_one : (squarefreePart p).map qToR = 1 := by
      rw [h_q_eq]
      simp
    have h_c_cast_ne_zero : (c : ℝ) ≠ 0 := by exact_mod_cast hc_ne_zero
    constructor
    · intro h_root
      have h_not_root : ¬ (p.map qToR).IsRoot a := by
        rw [hqR_eq_C]
        intro h
        rw [Polynomial.IsRoot.def, Polynomial.eval_C] at h
        exact h_c_cast_ne_zero h
      exact absurd h_root h_not_root
    · intro h_root
      have h_not_root_q : ¬ ((squarefreePart p).map qToR).IsRoot a := by
        rw [hqR_eq_one]
        intro h
        rw [Polynomial.IsRoot.def, Polynomial.eval_one] at h
        simp at h
      exact absurd h_root h_not_root_q
  · have hpR' : (p.map qToR).derivative ≠ 0 := by
      rw [derivative_map_qToR]
      exact map_qToR_ne_zero hder
    have hdR_eq_gcd : (EuclideanDomain.gcd p p.derivative).map qToR = EuclideanDomain.gcd (p.map qToR) (p.map qToR).derivative := by
      rw [derivative_map_qToR, gcd_map_qToR]
    let mp := (p.map qToR).rootMultiplicity a
    let md := ((EuclideanDomain.gcd p p.derivative).map qToR).rootMultiplicity a
    let mq := ((squarefreePart p).map qToR).rootMultiplicity a
    let mp' := (p.map qToR).derivative.rootMultiplicity a
    have h_mp_eq : mp = md + mq := by
      have h_ne_zero : (EuclideanDomain.gcd p p.derivative).map qToR * (squarefreePart p).map qToR ≠ 0 := by
        rw [← hpR_eq]
        exact hpR
      have h_mul := rootMultiplicity_mul (x := a) h_ne_zero
      have h_eq : (p.map qToR).rootMultiplicity a = (((EuclideanDomain.gcd p p.derivative).map qToR).rootMultiplicity a + ((squarefreePart p).map qToR).rootMultiplicity a) := by
        rw [← hpR_eq] at h_mul
        exact h_mul
      exact h_eq
    have h_md_eq_min : md = min mp mp' := by
      have h_eq : md = (EuclideanDomain.gcd (p.map qToR) (p.map qToR).derivative).rootMultiplicity a := by
        rw [← hdR_eq_gcd]
      rw [h_eq]
      exact rootMultiplicity_gcd_eq_min hpR hpR'
    by_cases h_root : (p.map qToR).IsRoot a
    · have h_mp_pos : 1 ≤ mp := by
        have h_pos : 0 < mp := (rootMultiplicity_pos hpR).2 h_root
        omega
      have h_mp'_eq : mp' = mp - 1 := derivative_rootMultiplicity_of_root (R := ℝ) h_root
      have h_md_eq : md = mp - 1 := by
        rw [h_md_eq_min, h_mp'_eq]
        exact nat_min_sub_one
      have h_mq_eq : mq = 1 := by
        have h_mq : mq = mp - md := by omega
        rw [h_mq, h_md_eq]
        exact nat_sub_sub_one h_mp_pos
      have h_q_root : ((squarefreePart p).map qToR).IsRoot a := by
        have h_pos : 0 < mq := by rw [h_mq_eq]; decide
        exact (rootMultiplicity_pos hqR).1 h_pos
      constructor
      · intro _
        exact h_q_root
      · intro _
        exact h_root
    · have h_mp_zero : mp = 0 := rootMultiplicity_eq_zero h_root
      have h_md_zero : md = 0 := by
        rw [h_md_eq_min, h_mp_zero]
        simp
      have h_mq_zero : mq = 0 := by omega
      have h_not_q_root : ¬ ((squarefreePart p).map qToR).IsRoot a := by
        intro h
        have h_pos : 0 < mq := (rootMultiplicity_pos hqR).2 h
        rw [h_mq_zero] at h_pos
        simp at h_pos
      have h_not_p_root : ¬ (p.map qToR).IsRoot a := h_root
      constructor
      · intro h
        exact absurd h h_not_p_root
      · intro h
        exact absurd h h_not_q_root


theorem squarefree_deriv_ne_zero (p : Polynomial ℚ) (hp : p ≠ 0) (a : ℝ)
    (hq : (squarefreePart p).aeval a = 0) : (squarefreePart p).derivative.aeval a ≠ 0 := by
  have hqR_root : ((squarefreePart p).map qToR).IsRoot a := (isRoot_map_iff_aeval _ _).mpr hq
  have hqR_ne_zero : (squarefreePart p).map qToR ≠ 0 := map_qToR_ne_zero (squarefreePart_ne_zero hp)
  by_cases hder : p.derivative = 0
  · obtain ⟨c, hc⟩ : ∃ c : ℚ, p = C c := ⟨p.coeff 0, eq_C_of_derivative_eq_zero hder⟩
    have hc_ne_zero : c ≠ 0 := by
      intro hc0
      have : (C c : Polynomial ℚ) = 0 := by rw [hc0, C_0]
      rw [hc] at hp
      rw [this] at hp
      exact hp rfl
    have h_q_eq : squarefreePart p = 1 := by
      have h_gcd_eq : EuclideanDomain.gcd p p.derivative = p := by
        rw [hder]
        have : EuclideanDomain.gcd (C c : Polynomial ℚ) 0 = C c := by simp
        rw [hc, this]
      unfold squarefreePart
      rw [h_gcd_eq, hc]
      exact EuclideanDomain.div_self (by
        intro h
        have : (C c : Polynomial ℚ).coeff 0 = c := by simp
        rw [h] at this
        simp at this
        exact hc_ne_zero this.symm)
    have hqR_eq_one : (squarefreePart p).map qToR = 1 := by
      rw [h_q_eq]
      simp
    have h_not_root : ¬ ((squarefreePart p).map qToR).IsRoot a := by
      rw [hqR_eq_one]
      intro h
      rw [Polynomial.IsRoot.def, Polynomial.eval_one] at h
      simp at h
    exact absurd hqR_root h_not_root
  · have hpR : p.map qToR ≠ 0 := map_qToR_ne_zero hp
    have hdR : (EuclideanDomain.gcd p p.derivative).map qToR ≠ 0 := map_qToR_ne_zero (gcd_ne_zero_of_p_ne_zero hp)
    have hqR : (squarefreePart p).map qToR ≠ 0 := map_qToR_ne_zero (squarefreePart_ne_zero hp)
    have hpR_eq : p.map qToR = (EuclideanDomain.gcd p p.derivative).map qToR * (squarefreePart p).map qToR := pR_eq_dR_mul_qR p hp
    have hpR' : (p.map qToR).derivative ≠ 0 := by
      rw [derivative_map_qToR]
      exact map_qToR_ne_zero hder
    have hdR_eq_gcd : (EuclideanDomain.gcd p p.derivative).map qToR = EuclideanDomain.gcd (p.map qToR) (p.map qToR).derivative := by
      rw [derivative_map_qToR, gcd_map_qToR]
    let mp := (p.map qToR).rootMultiplicity a
    let md := ((EuclideanDomain.gcd p p.derivative).map qToR).rootMultiplicity a
    let mq := ((squarefreePart p).map qToR).rootMultiplicity a
    let mp' := (p.map qToR).derivative.rootMultiplicity a
    have h_mp_eq : mp = md + mq := by
      have h_ne_zero : (EuclideanDomain.gcd p p.derivative).map qToR * (squarefreePart p).map qToR ≠ 0 := by
        rw [← hpR_eq]
        exact hpR
      have h_mul := rootMultiplicity_mul (x := a) h_ne_zero
      rw [← hpR_eq] at h_mul
      exact h_mul
    have h_md_eq_min : md = min mp mp' := by
      have h_eq : md = (EuclideanDomain.gcd (p.map qToR) (p.map qToR).derivative).rootMultiplicity a := by
        rw [← hdR_eq_gcd]
      rw [h_eq]
      exact rootMultiplicity_gcd_eq_min hpR hpR'
    have h_q_mq_one : mq = 1 := by
      have hpR_root : (p.map qToR).IsRoot a := by
        have hq_root : ((squarefreePart p).map qToR).IsRoot a := hqR_root
        have hp_root : (p.map qToR).IsRoot a := by
          rw [hpR_eq]
          exact Polynomial.root_mul_left_of_isRoot _ hq_root
        exact hp_root
      have h_mp_pos : 1 ≤ mp := by
        have h_pos : 0 < mp := (rootMultiplicity_pos hpR).2 hpR_root
        omega
      have h_mp'_eq : mp' = mp - 1 := derivative_rootMultiplicity_of_root (R := ℝ) hpR_root
      have h_md_eq : md = mp - 1 := by
        rw [h_md_eq_min, h_mp'_eq]
        exact nat_min_sub_one
      have : mq = mp - md := by omega
      rw [this, h_md_eq]
      exact nat_sub_sub_one h_mp_pos
    have h_deriv_eq : ((squarefreePart p).map qToR).derivative.rootMultiplicity a = mq - 1 := by
      exact derivative_rootMultiplicity_of_root (R := ℝ) hqR_root
    have h_deriv_zero : ((squarefreePart p).map qToR).derivative.rootMultiplicity a = 0 := by
      rw [h_deriv_eq, h_q_mq_one]
    have h_not_deriv_root : ¬ (((squarefreePart p).map qToR).derivative).IsRoot a := by
      intro h
      have h_pos : 0 < ((squarefreePart p).map qToR).derivative.rootMultiplicity a := (rootMultiplicity_pos (by
        intro h0
        have h_q_eq_C : ((squarefreePart p).map qToR) = C (((squarefreePart p).map qToR).coeff 0) := by
          exact eq_C_of_derivative_eq_zero h0
        have h_root_C : ((squarefreePart p).map qToR).IsRoot a := hqR_root
        rw [h_q_eq_C] at h_root_C
        rw [Polynomial.IsRoot.def, Polynomial.eval_C] at h_root_C
        have h_coeff_zero : (((squarefreePart p).map qToR).coeff 0) = 0 := by
          rw [← h_root_C]
        have h_poly_zero : ((squarefreePart p).map qToR) = 0 := by
          rw [h_q_eq_C, h_coeff_zero, C_0]
        exact hqR_ne_zero h_poly_zero)).2 h
      rw [h_deriv_zero] at h_pos
      simp at h_pos
    have h_deriv_aeval : ((squarefreePart p).derivative).map qToR = ((squarefreePart p).map qToR).derivative := by
      rw [derivative_map_qToR]
    intro h
    have h_root : (((squarefreePart p).derivative).map qToR).IsRoot a := (isRoot_map_iff_aeval _ _).mpr h
    rw [h_deriv_aeval] at h_root
    exact h_not_deriv_root h_root

end SquarefreePreprocessing


