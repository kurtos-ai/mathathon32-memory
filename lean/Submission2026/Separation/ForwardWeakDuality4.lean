module

public import Submission2026.Separation.ForwardIdentity4
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
noncomputable section

namespace Submission2026.Separation.ForwardWeakDuality4
open Submission2026.Separation.PathIdentities4
open Submission2026.Separation.ForwardIdentity4

def pi (r : ℝ) (T : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  tau T i - (if i = 4 then 1 / 2 else 0) - mass T i ^ 2 / (2 * r)

def psi (r : ℝ) (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ) : ℝ :=
  sum5 (fun i => b i * tau T i) + sum5 (fun k => sum5 (fun j => if j < k then
    b k * (mass T k * mass T j / r + 2 * Real.sqrt (pi r T k * pi r T j)) else 0))

def weightedPsi (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ) : ℝ :=
  sum5 (fun i => b i * tau T i) + sum5 (fun k => sum5 (fun j => if j < k then
    b k * (mass T k * mass T j / r +
      (pi r T k * ν j / ν k + pi r T j * ν k / ν j)) else 0))

theorem weighted_sqrt_bound (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 < u) (hv : 0 < v) : 2 * Real.sqrt (a * b) ≤ a * v / u + b * u / v := by
  have hu0 := ne_of_gt hu
  have hv0 := ne_of_gt hv
  have hA : 0 ≤ a * v / u := div_nonneg (mul_nonneg ha (le_of_lt hv)) (le_of_lt hu)
  have hB : 0 ≤ b * u / v := div_nonneg (mul_nonneg hb (le_of_lt hu)) (le_of_lt hv)
  have hab : a * b = (a * v / u) * (b * u / v) := by field_simp
  rw [hab, Real.sqrt_mul hA]
  nlinarith [sq_nonneg (Real.sqrt (a * v / u) - Real.sqrt (b * u / v)),
    Real.sq_sqrt hA, Real.sq_sqrt hB]

theorem sum5_mono (f g : ℕ → ℝ) (h : ∀ i ≤ 4, f i ≤ g i) : sum5 f ≤ sum5 g := by
  exact add_le_add (add_le_add (add_le_add (add_le_add (h 0 (by omega))
    (h 1 (by omega))) (h 2 (by omega))) (h 3 (by omega))) (h 4 (by omega))

theorem psi_le_weightedPsi (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ)
    (hb : ∀ i ≤ 4, 0 ≤ b i) (hn : ∀ i ≤ 4, 0 < ν i)
    (hp : ∀ i ≤ 4, 0 ≤ pi r T i) : psi r T b ≤ weightedPsi r T b ν := by
  unfold psi weightedPsi
  apply add_le_add le_rfl
  apply sum5_mono
  intro k hk
  apply sum5_mono
  intro j hj
  split_ifs
  · exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (weighted_sqrt_bound _ _ _ _ (hp k hk) (hp j hj) (hn k hk) (hn j hj)))
      (hb k hk)
  · exact le_rfl

theorem weightedPsi_eq_dualValue (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ)
    (hr : r ≠ 0) (hn : ∀ i ≤ 4, ν i ≠ 0) : weightedPsi r T b ν = dualValue r T b ν := by
  have hn0 := hn 0 (by omega)
  have hn1 := hn 1 (by omega)
  have hn2 := hn 2 (by omega)
  have hn3 := hn 3 (by omega)
  have hn4 := hn 4 (by omega)
  norm_num [weightedPsi, dualValue, pi, energy, xi, prefixSum, sum5]
  field_simp
  ring

theorem psi_le_dualValue (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ)
    (hr : 0 < r) (hb : ∀ i ≤ 4, 0 ≤ b i) (hn : ∀ i ≤ 4, 0 < ν i)
    (hp : ∀ i ≤ 4, 0 ≤ pi r T i) : psi r T b ≤ dualValue r T b ν := by
  rw [← weightedPsi_eq_dualValue r T b ν (ne_of_gt hr) (fun i hi => ne_of_gt (hn i hi))]
  exact psi_le_weightedPsi r T b ν hb hn hp

/-- Actual weak duality and residual bound for five-coordinate forward data. -/
theorem psi_le_path_totalStep (δ ν : ℕ → ℝ) (r : ℝ)
    (hp : ExtremalMemory.PathConditions4 δ ν r) (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hf : ForwardData4 T b) (hpi : ∀ i ≤ 4, 0 ≤ pi r T i) :
    psi r T b ≤ 1 + totalStep δ ν r := by
  exact (psi_le_dualValue r T b ν hp.rate_pos hf.b_nonneg hp.slack_pos hpi).trans
    (dualValue_le_path_totalStep δ ν r hp T b hf)

#print axioms psi_le_path_totalStep
end Submission2026.Separation.ForwardWeakDuality4
