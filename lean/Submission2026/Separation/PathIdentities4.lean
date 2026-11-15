module

public import Submission2026.ExtremalMemory

@[expose] public section
noncomputable section

/-! Actual path identities at N=4, derived from the normalized positive path
parameters, diagonal equations and adjacent stationarity. This file does not
assert existence or optimality of such parameters. -/
namespace Submission2026.Separation.PathIdentities4
open ExtremalMemory
open scoped BigOperators

/-- Sum over the actual five path coordinates. -/
def sum5 (f : ℕ → ℝ) : ℝ := f 0 + f 1 + f 2 + f 3 + f 4

def tail (ν : ℕ → ℝ) (i : ℕ) : ℝ := ∑ k ∈ Finset.Ico i 5, 1 / ν k

def weightedSquare (δ ν : ℕ → ℝ) : ℝ := sum5 (fun i => δ i ^ 2 / ν i)

theorem ratio_step (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r)
    (i : ℕ) (hi : i < 4) :
    δ i / ν i - δ (i + 1) / ν (i + 1) = r / ν i := by
  have hn := ne_of_gt (hp.slack_pos i (by omega))
  have hn' := ne_of_gt (hp.slack_pos (i + 1) (by omega))
  field_simp
  simpa [mul_comm] using hp.adjacent i hi

theorem ratio_terminal (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r)
    (i : ℕ) (hi : i ≤ 4) :
    δ i / ν i = r * (tail ν i - tail ν 4) + δ 4 / ν 4 := by
  have h0 := ratio_step δ ν r hp 0 (by omega)
  have h1 := ratio_step δ ν r hp 1 (by omega)
  have h2 := ratio_step δ ν r hp 2 (by omega)
  have h3 := ratio_step δ ν r hp 3 (by omega)
  interval_cases i <;> norm_num [tail, Finset.sum_Ico_succ_top, Finset.sum_range_succ] at * <;>
    simp only [div_eq_mul_inv] at * <;> linarith only [h0, h1, h2, h3]

theorem normalized_sum (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    sum5 δ = 1 := by simpa [sum5, D] using hp.normalized

theorem tail_pairing (δ ν : ℕ → ℝ) :
    sum5 (fun i => δ i * tail ν i) = sum5 (fun i => D δ i / ν i) := by
  norm_num [sum5, tail, D, Finset.sum_Ico_succ_top, Finset.sum_range_succ]
  ring

theorem diagonal_weighted (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    sum5 (fun i => D δ i / ν i) = sum5 ν + weightedSquare δ ν / (2 * r) + 1 / (2 * ν 4) := by
  have hr := ne_of_gt hp.rate_pos
  have hi (i : ℕ) (hi : i ≤ 4) :
      D δ i / ν i = ν i + (δ i ^ 2 / ν i) / (2 * r) +
        (if i = 4 then 1 / (2 * ν 4) else 0) := by
    have hn := ne_of_gt (hp.slack_pos i hi)
    have hd := hp.diagonal i hi
    by_cases h : i = 4
    · subst i
      norm_num at hd ⊢
      field_simp at hd ⊢
      nlinarith
    · simp only [h, ite_false] at hd ⊢
      field_simp at hd ⊢
      nlinarith
  have h0 := hi 0 (by omega)
  have h1 := hi 1 (by omega)
  have h2 := hi 2 (by omega)
  have h3 := hi 3 (by omega)
  have h4 := hi 4 (by omega)
  norm_num at h0 h1 h2 h3 h4
  unfold sum5 weightedSquare
  dsimp [sum5]
  rw [h0,h1,h2,h3,h4]
  ring

theorem weighted_stationarity (δ ν : ℕ → ℝ) (r : ℝ)
    (hp : PathConditions4 δ ν r) :
    weightedSquare δ ν = r * sum5 (fun i => D δ i / ν i) + (δ 4 - r) / ν 4 := by
  have hi (i : ℕ) (hi : i ≤ 4) : δ i ^ 2 / ν i =
      r * (δ i * tail ν i) + δ i * ((δ 4 - r) / ν 4) := by
    have hs := ratio_terminal δ ν r hp i hi
    norm_num [tail, Finset.sum_Ico_succ_top, Finset.sum_range_succ] at hs
    calc
      _ = δ i * (δ i / ν i) := by ring
      _ = r * (δ i * tail ν i) + δ i * ((δ 4 - r) / ν 4) := by
        rw [ratio_terminal δ ν r hp i hi]
        norm_num [tail, Finset.sum_Ico_succ_top, Finset.sum_range_succ]
        ring
  have hn := normalized_sum δ ν r hp
  rw [← tail_pairing]
  unfold weightedSquare sum5
  dsimp only
  rw [hi 0 (by omega), hi 1 (by omega), hi 2 (by omega), hi 3 (by omega), hi 4 (by omega)]
  unfold sum5 at hn
  linear_combination ((δ 4 - r) / ν 4) * hn

theorem weightedSquare_eq (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    weightedSquare δ ν = 2 * r * sum5 ν + (2 * δ 4 - r) / ν 4 := by
  have hr := ne_of_gt hp.rate_pos
  have hn := ne_of_gt (hp.slack_pos 4 (by omega))
  have hs := weighted_stationarity δ ν r hp
  rw [diagonal_weighted δ ν r hp] at hs
  field_simp at hs ⊢
  nlinarith

theorem sum5_congr {f g : ℕ → ℝ} (h : ∀ i ≤ 4, f i = g i) : sum5 f = sum5 g := by
  simp only [sum5, h 0 (by omega), h 1 (by omega), h 2 (by omega),
    h 3 (by omega), h 4 (by omega)]

theorem ratio_moments (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    sum5 (fun i => ν i * (δ i / ν i)) = 1 ∧
    sum5 (fun i => ν i * (δ i / ν i) ^ 2) = weightedSquare δ ν := by
  constructor
  · rw [← normalized_sum δ ν r hp]
    apply sum5_congr
    intro i hi
    field_simp [ne_of_gt (hp.slack_pos i hi)]
  · unfold weightedSquare
    apply sum5_congr
    intro i hi
    field_simp [ne_of_gt (hp.slack_pos i hi)]

theorem centered_variance (ν u : ℕ → ℝ) (a : ℝ) :
    sum5 (fun i => ν i * (u i - a) ^ 2) =
    sum5 (fun i => ν i * u i ^ 2) - 2 * a * sum5 (fun i => ν i * u i) +
      a ^ 2 * sum5 ν := by
  unfold sum5
  ring

theorem first_path_identity (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    r * ν 4 * (∑ j ∈ Finset.Ico 0 4, ν j * (tail ν j - tail ν 4) ^ 2) =
      (sum5 ν - ν 4) / ν 4 := by
  have hr := ne_of_gt hp.rate_pos
  have hn := ne_of_gt (hp.slack_pos 4 (by omega))
  have hmom := ratio_moments δ ν r hp
  have hv := centered_variance ν (fun i => δ i / ν i) (δ 4 / ν 4)
  rw [hmom.1, hmom.2, weightedSquare_eq δ ν r hp] at hv
  have hscale : sum5 (fun i => ν i * (δ i / ν i - δ 4 / ν 4) ^ 2) =
      r ^ 2 * (∑ j ∈ Finset.Ico 0 4, ν j * (tail ν j - tail ν 4) ^ 2) := by
    have hh : sum5 (fun i => ν i * (δ i / ν i - δ 4 / ν 4) ^ 2) =
        sum5 (fun i => r ^ 2 * ν i * (tail ν i - tail ν 4) ^ 2) := by
      apply sum5_congr
      intro i hi
      rw [ratio_terminal δ ν r hp i hi]
      ring
    rw [hh]
    norm_num [sum5, Finset.sum_Ico_succ_top, Finset.sum_range_succ]
    ring
  rw [hscale] at hv
  have hd := hp.diagonal 4 (by omega)
  rw [hp.normalized] at hd
  norm_num at hd
  have hd' : δ 4 ^ 2 = r - 2 * r * ν 4 ^ 2 := by
    field_simp at hd
    nlinarith
  have hv' : r ^ 2 * (∑ j ∈ Finset.Ico 0 4, ν j * (tail ν j - tail ν 4) ^ 2) =
      r * (sum5 ν - ν 4) / ν 4 ^ 2 := by
    rw [hv]
    field_simp
    linear_combination sum5 ν * hd'
  calc
    _ = (r ^ 2 * (∑ j ∈ Finset.Ico 0 4, ν j * (tail ν j - tail ν 4) ^ 2)) * ν 4 / r := by
      field_simp
    _ = (r * (sum5 ν - ν 4) / ν 4 ^ 2) * ν 4 / r := by rw [hv']
    _ = _ := by field_simp

/-- The sum is over j<k, each unordered pair exactly once. -/
def pairVariation (ν u : ℕ → ℝ) : ℝ :=
  sum5 (fun j => sum5 (fun k => if j < k then ν j * ν k * (u j - u k) ^ 2 else 0))

def pathLambda (ν : ℕ → ℝ) : ℝ := sum5 (fun k => D ν k / ν k)

theorem pair_variance (ν u : ℕ → ℝ) :
    pairVariation ν u = sum5 ν * sum5 (fun i => ν i * u i ^ 2) -
      (sum5 (fun i => ν i * u i)) ^ 2 := by
  norm_num [pairVariation, sum5]
  ring

theorem lambda_eq (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    pathLambda ν = 1 / r + sum5 ν * (1 - δ 4 / r) / ν 4 := by
  have hr := ne_of_gt hp.rate_pos
  have hn := ne_of_gt (hp.slack_pos 4 (by omega))
  have hh : sum5 δ = sum5 (fun i => r * ν i * tail ν i + ν i * ((δ 4 - r) / ν 4)) := by
    apply sum5_congr
    intro i hi
    have hs := ratio_terminal δ ν r hp i hi
    have hni := ne_of_gt (hp.slack_pos i hi)
    calc
      δ i = ν i * (δ i / ν i) := by field_simp
      _ = r * ν i * tail ν i + ν i * ((δ 4 - r) / ν 4) := by
        rw [hs]
        norm_num [tail, Finset.sum_Ico_succ_top, Finset.sum_range_succ]
        ring
  have hh' : sum5 δ = r * pathLambda ν + sum5 ν * ((δ 4 - r) / ν 4) := by
    rw [hh]
    unfold pathLambda
    rw [← tail_pairing]
    unfold sum5
    ring
  rw [normalized_sum δ ν r hp] at hh'
  field_simp at hh' ⊢
  nlinarith

theorem path_variance (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    r ^ 2 * pairVariation ν (tail ν) = sum5 ν * weightedSquare δ ν - 1 := by
  have hmom := ratio_moments δ ν r hp
  have hv := pair_variance ν (fun i => δ i / ν i)
  rw [hmom.1, hmom.2] at hv
  have hscale : pairVariation ν (fun i => δ i / ν i) =
      r ^ 2 * pairVariation ν (tail ν) := by
    have hh : pairVariation ν (fun i => δ i / ν i) =
        sum5 (fun j => sum5 (fun k => r ^ 2 *
          (if j < k then ν j * ν k * (tail ν j - tail ν k) ^ 2 else 0))) := by
      unfold pairVariation
      apply sum5_congr
      intro j hj
      apply sum5_congr
      intro k hk
      by_cases hjk : j < k
      · simp only [hjk, ite_true]
        rw [ratio_terminal δ ν r hp j hj, ratio_terminal δ ν r hp k hk]
        ring
      · simp [hjk]
    rw [hh]
    norm_num [pairVariation, sum5]
    ring
  rw [hscale] at hv
  simpa using hv

theorem second_path_identity (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    pathLambda ν + r / 2 * pairVariation ν (tail ν) - (sum5 ν - ν 4) / ν 4 / 2 =
      1 / 2 + 1 / (2 * r) + (sum5 ν) ^ 2 := by
  have hr := ne_of_gt hp.rate_pos
  have hn := ne_of_gt (hp.slack_pos 4 (by omega))
  have hv := path_variance δ ν r hp
  have hv' : pairVariation ν (tail ν) = (sum5 ν * weightedSquare δ ν - 1) / r ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hr)).2
    nlinarith [hv]
  rw [hv', weightedSquare_eq δ ν r hp, lambda_eq δ ν r hp]
  field_simp
  ring

theorem pairVariation_pos (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    0 < pairVariation ν (tail ν) := by
  have h0 := hp.slack_pos 0 (by omega)
  have h1 := hp.slack_pos 1 (by omega)
  have h2 := hp.slack_pos 2 (by omega)
  have h3 := hp.slack_pos 3 (by omega)
  have h4 := hp.slack_pos 4 (by omega)
  have hdiff : tail ν 0 - tail ν 1 = 1 / ν 0 := by
    norm_num [tail, Finset.sum_Ico_succ_top, Finset.sum_range_succ]
  have h01 : 0 < ν 0 * ν 1 * (tail ν 0 - tail ν 1) ^ 2 := by
    rw [hdiff]
    positivity
  norm_num [pairVariation, sum5]
  positivity

/-- The numerator in the paper's derivative of E_4 is strictly positive. -/
theorem weightedSquare_strict (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    1 < sum5 ν * weightedSquare δ ν := by
  have hv := path_variance δ ν r hp
  have hpos := mul_pos (sq_pos_of_pos hp.rate_pos) (pairVariation_pos δ ν r hp)
  linarith

/-- Total step of the actual map defined by the path recurrence. -/
def totalStep (δ ν : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 0 4, omegaEntry δ ν r 4 j

theorem totalStep_eq (δ ν : ℕ → ℝ) (r : ℝ) (hp : PathConditions4 δ ν r) :
    totalStep δ ν r = (1 / r - 1) / 2 + (sum5 ν) ^ 2 := by
  have hr := ne_of_gt hp.rate_pos
  have hd0 := hp.diagonal 0 (by omega)
  have hd1 := hp.diagonal 1 (by omega)
  have hd2 := hp.diagonal 2 (by omega)
  have hd3 := hp.diagonal 3 (by omega)
  have hd4 := hp.diagonal 4 (by omega)
  have hn := normalized_sum δ ν r hp
  norm_num at hd0 hd1 hd2 hd3 hd4
  field_simp at hd0 hd1 hd2 hd3 hd4
  simp only [D] at hd0 hd1 hd2 hd3 hd4
  unfold totalStep
  norm_num [omegaEntry, Finset.sum_Ico_succ_top, Finset.sum_range_succ,
    hp.normalized]
  field_simp
  simp only [D, sum5] at hn ⊢
  norm_num only [Nat.reduceAdd] at hd0 hd1 hd2 hd3 hd4 ⊢
  linear_combination -hd0 - hd1 - hd2 - hd3 - hd4 +
    (1 - δ 0 - δ 1 - δ 2 - δ 3 + δ 4 - 2 * r) * hn

#print axioms weightedSquare_eq
#print axioms first_path_identity
#print axioms second_path_identity
#print axioms weightedSquare_strict
#print axioms totalStep_eq
end Submission2026.Separation.PathIdentities4
