module
public import Continuation.Smooth.DroriOracle
@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace
namespace SmoothDrori

lemma hardX_mem_prefix (N : ℕ) (R : ℝ) (i : ℕ) : hardX N R i ∈ prefixSpace N i := by
  intro j hj
  rw [hardX_apply,ite_eq_right (by omega)]

lemma hardG_mem_prefix (N : ℕ) (L R : ℝ) (i : ℕ) : hardG N L R i ∈ prefixSpace N (i+1) := by
  intro j hj
  rw [hardG_apply,ite_eq_right (by omega)]

lemma eq_zero_of_mem_prefix_zero (N : ℕ) (p : Space N) (hp : p ∈ prefixSpace N 0) : p = 0 := by
  ext j
  exact hp j (Nat.zero_le j.val)

lemma hardGradient_prefix_zero (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (p : Space N) (hp : p ∈ prefixSpace N 0) :
    hardGradient N L R hN hL hR p ∈ prefixSpace N 1 := by
  rw [eq_zero_of_mem_prefix_zero N p hp,← hardX_zero N R,
    hardGradient_at_data N L R hN hL hR 0 (by omega)]
  exact hardG_mem_prefix N L R 0

lemma hardFunction_minimum_zero (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    hardFunction N L R hN hL hR (hardX N R (N+1)) = 0 := by
  rw [hardFunction_at_data N L R hN hL hR (N+1) le_rfl]
  simp [hardF]

lemma hardFunction_terminal_lower (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (p : Space N) (hp : p ∈ prefixSpace N N) :
    L*R^2/(2*(SmoothBenchmark.theta N N)^2) ≤
      hardFunction N L R hN hL hR p-hardFunction N L R hN hL hR (hardX N R (N+1)) := by
  rw [hardFunction_minimum_zero N L R hN hL hR,sub_zero,
    ← hardF_value N L R hN hL hR]
  exact hardFunction_lower_on_prefix N L R hN hL hR N le_rfl p hp

end SmoothDrori
