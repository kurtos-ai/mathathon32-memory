module
public import RealizationCore.CutPadding
@[expose] public section

/-!
# Actual scalar register realization is equivalent to the cut-rank bound

This is the substantive realization theorem, not an assertion that memory is defined
as maximum rank. `HasRealization` is the actual recursive linear machine semantics.
-/

namespace RegisterMachine

noncomputable section
open Matrix

/-- The canonical construction gives an actual s-register realization from all cut-rank bounds. -/
theorem realization_of_Hk_rank {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    {s : ℕ} (hs : 0 < s) (hrank : ∀ (k : ℕ) (hk : k ≤ N), (H_k N k hk W).rank ≤ s) :
    HasRealization N W s := by
  apply realization_of_cH_rank W hs
  intro k hk
  rw [cH_rank_eq_Hk_rank]
  exact hrank k hk

/-- The central equivalence: an actual recursive s-register linear machine exists iff
all cut matrices H_k have rank at most s. -/
theorem realization_iff_rank {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    {s : ℕ} (hs : 0 < s) :
    HasRealization N W s ↔ ∀ (k : ℕ) (hk : k ≤ N), (H_k N k hk W).rank ≤ s := by
  constructor
  · intro h k hk
    exact necessity_rank_le_unconditional N s W k hk h
  · exact realization_of_Hk_rank W hs

/-- Positivity is automatic for the actual cut rank (the H_0 column is nonzero),
so the bound already implies s≥1 and the equivalence can be stated without it. -/
theorem realization_iff_rank_all {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) :
    HasRealization N W s ↔ ∀ (k : ℕ) (hk : k ≤ N), (H_k N k hk W).rank ≤ s := by
  have hs_of_bound : (∀ (k : ℕ) (hk : k ≤ N), (H_k N k hk W).rank ≤ s) → 0 < s := by
    intro h
    have h0 := h 0 (Nat.zero_le N)
    have hpad : (cH W 0 (Nat.zero_le N)).rank ≤ s := by
      rw [cH_rank_eq_Hk_rank]
      exact h0
    rw [cH_rank_zero] at hpad
    exact hpad
  constructor
  · intro h k hk
    exact necessity_rank_le_unconditional N s W k hk h
  · intro h
    exact realization_of_Hk_rank W (hs_of_bound h) h

#print axioms realization_of_Hk_rank
#print axioms realization_iff_rank
#print axioms realization_iff_rank_all

end
end RegisterMachine
