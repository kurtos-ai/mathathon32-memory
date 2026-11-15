module

public import Submission2026.Separation.ForwardWeakDuality4

@[expose] public section
noncomputable section

namespace Submission2026.Separation.ForwardConsequences4
open Submission2026.Separation.PathIdentities4
open Submission2026.Separation.ForwardIdentity4
open Submission2026.Separation.ForwardWeakDuality4

/-- For arbitrary positive nu, only the terminal kappa sign is a constraint. -/
theorem kappa_nonpos_of_terminal (r : ℝ) (ν : ℕ → ℝ)
    (hr : 0 < r) (hn : ∀ i ≤ 4, 0 < ν i) (hk : kappa r ν 4 ≤ 0)
    (i : ℕ) (hi : i ≤ 4) : kappa r ν i ≤ 0 := by
  by_cases h : i = 4
  · simpa [h] using hk
  · unfold kappa
    simp only [h, ite_false, zero_sub, neg_nonpos]
    apply mul_nonneg
    · exact mul_nonneg (div_nonneg (le_of_lt hr) (by norm_num)) (le_of_lt (hn i hi))
    · apply sum5_nonneg
      intro j hj
      split_ifs
      · exact mul_nonneg (le_of_lt (hn j hj)) (sq_nonneg _)
      · exact le_rfl

/-- The exact arbitrary-positive-nu consequence in the paper's master lemma. -/
theorem dualValue_le_boundary_of_terminal (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ)
    (hr : 0 < r) (hn : ∀ i ≤ 4, 0 < ν i) (hf : ForwardData4 T b)
    (hk : kappa r ν 4 ≤ 0) : dualValue r T b ν ≤ boundary r ν := by
  exact dualValue_le_boundary r T b ν hr hn hf (kappa_nonpos_of_terminal r ν hr hn hk)

theorem psi_le_boundary_of_terminal (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ)
    (hr : 0 < r) (hn : ∀ i ≤ 4, 0 < ν i) (hf : ForwardData4 T b)
    (hp : ∀ i ≤ 4, 0 ≤ pi r T i) (hk : kappa r ν 4 ≤ 0) :
    psi r T b ≤ boundary r ν := by
  exact (psi_le_dualValue r T b ν hr hf.b_nonneg hn hp).trans
    (dualValue_le_boundary_of_terminal r T b ν hr hn hf hk)

#print axioms psi_le_boundary_of_terminal
end Submission2026.Separation.ForwardConsequences4
