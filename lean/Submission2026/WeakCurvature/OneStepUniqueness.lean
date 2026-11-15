module
public import Submission2026.WeakCurvature.OneStep
public import Submission2026.WeakCurvature.CapacityValid

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

/-- At horizon one, the scalar root in the open source interval is unique. -/
lemma isScalarRoot_one_unique {q ν : ℝ} (hq : q ∈ Set.Icc (-1 : ℝ) 0)
    (hν0 : 4 * curvatureC q < ν) (hν1 : ν < capacityUpper (curvatureC q))
    (hroot : IsScalarRoot 1 q ν) : ν = oneStepNu q := by
  have hq1 : q < 1 := by linarith [hq.2]
  have h1q : 1 - q ≠ 0 := by linarith
  have ha := curvatureA_pos hq1
  have hc : 0 ≤ curvatureC q := c_nonneg_of_mem_Icc hq
  have hν : 0 < ν := by linarith
  have hroot0 := hroot
  unfold IsScalarRoot scalarBalance at hroot0
  rw [Function.iterate_one] at hroot0
  set s := capacity (curvatureC q) (curvatureA q) ν 0 with hs_def
  change s + Real.sqrt ((ν - 4 * curvatureC q) / (2 * curvatureA q)) = 1 at hroot0
  have hs_le : s ≤ 1 := by
    dsimp [s, capacity]
    exact min_le_left _ _
  have hratio_pos : 0 < (ν - 4 * curvatureC q) / (2 * curvatureA q) := by
    positivity
  have hδpos : 0 < Real.sqrt ((ν - 4 * curvatureC q) / (2 * curvatureA q)) :=
    Real.sqrt_pos.2 hratio_pos
  have hδ : Real.sqrt ((ν - 4 * curvatureC q) / (2 * curvatureA q)) = 1 - s := by
    linarith
  have hs_lt : s < 1 := by linarith
  have hApos := curvature_capacityA_pos hq (show (0 : ℝ) ≤ 1 by norm_num) hν1.le
  have hdenpos : 0 < 1 - curvatureC q * ν := by
    simpa [capacityA] using hApos
  have hden : 1 - curvatureC q * ν ≠ 0 := ne_of_gt hdenpos
  have hA0 : capacityA (curvatureC q) (curvatureA q) ν 0 ≠ 0 := by
    simpa [capacityA] using hden
  have hRform := capacityRoot_apply_zero (c := curvatureC q) (a := curvatureA q)
    hν.le hA0
  have hRnonneg : 0 ≤ capacityRoot (curvatureC q) (curvatureA q) ν 0 := by
    rw [hRform]
    positivity
  have hRlt : capacityRoot (curvatureC q) (curvatureA q) ν 0 < 1 := by
    by_contra hn
    have h1R : 1 ≤ capacityRoot (curvatureC q) (curvatureA q) ν 0 := by linarith
    have hs1 : s = 1 := by
      dsimp [s, capacity]
      exact min_eq_left h1R
    linarith
  have hsR : s = capacityRoot (curvatureC q) (curvatureA q) ν 0 := by
    dsimp [s, capacity]
    exact min_eq_right hRlt.le
  have hcap_eq : curvatureA q * ν / (1 - curvatureC q * ν) = s := by
    calc
      curvatureA q * ν / (1 - curvatureC q * ν) =
          capacityRoot (curvatureC q) (curvatureA q) ν 0 := hRform.symm
      _ = s := hsR.symm
  have hfactor := (div_eq_iff hden).mp hcap_eq
  have hs_pos : 0 < s := by
    by_contra hn
    have hsnon : s ≤ 0 := by linarith
    have hprod : s * (1 - curvatureC q * ν) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hsnon hdenpos.le
    have hleft : 0 < curvatureA q * ν := mul_pos ha hν
    rw [hfactor] at hleft
    linarith
  have hsqrt_sq := Real.sq_sqrt hratio_pos.le
  have hzsq : (1 - s) ^ 2 = (ν - 4 * curvatureC q) / (2 * curvatureA q) := by
    calc
      (1 - s) ^ 2 = Real.sqrt ((ν - 4 * curvatureC q) / (2 * curvatureA q)) ^ 2 := by
        rw [hδ]
      _ = (ν - 4 * curvatureC q) / (2 * curvatureA q) := hsqrt_sq
  have hνzero : ν = 4 * curvatureC q +
      2 * curvatureA q * (1 - s) ^ 2 := by
    have h := (eq_div_iff (by positivity : 2 * curvatureA q ≠ 0)).mp hzsq
    nlinarith
  have hE : (2 - s) * (q * s ^ 2 - 2 * s + 1 - q) = 0 := by
    rw [hνzero] at hfactor
    unfold curvatureA curvatureC at hfactor
    field_simp [h1q] at hfactor
    nlinarith
  have hquad : q * s ^ 2 - 2 * s + 1 - q = 0 :=
    (mul_eq_zero.mp hE).resolve_left (by linarith)
  have htail : 2 * s * (curvatureA q + curvatureC q * s) = 1 := by
    unfold curvatureA curvatureC
    field_simp [h1q]
    nlinarith [hquad]
  have hs_t : s = oneStepT q := eq_oneStepT_of_tail_relation hq1 hs_pos hs_lt htail
  rw [hs_t] at hνzero
  have h_other := oneStep_zeroth_relation hq1
  linarith

/-- Existence and uniqueness of the one-step scalar root in its open interval. -/
lemma eq_oneStepNu_iff_isScalarRoot_one {q ν : ℝ}
    (hq : q ∈ Set.Icc (-1 : ℝ) 0)
    (hν0 : 4 * curvatureC q < ν) (hν1 : ν < capacityUpper (curvatureC q)) :
    ν = oneStepNu q ↔ IsScalarRoot 1 q ν := by
  constructor
  · intro h
    rw [h]
    exact isScalarRoot_one_oneStepNu (show q < 1 by linarith [hq.2])
  · exact isScalarRoot_one_unique hq hν0 hν1

#print axioms isScalarRoot_one_unique
#print axioms eq_oneStepNu_iff_isScalarRoot_one

end Submission2026.WeakCurvature
