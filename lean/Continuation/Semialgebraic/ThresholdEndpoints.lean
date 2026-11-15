module
public import Continuation.Semialgebraic.Endpoints
public import Decision.ExactThresholds
/-! Algebraicity after a rational quantifier-free description of the threshold
set has been supplied and proved exact. This does not construct that description
or implement real quantifier elimination. -/
@[expose] public section
namespace MemorySemialgebraic

theorem ray_endpoint_algebraic (φ : QFFormula 1) (v : ℝ)
    (hφ : φ.solutionSet1 = Set.Ioi v) : IsAlgebraic (R := ℚ) v := by
  apply qf_endpoint_algebraic φ v
  rw [hφ, frontier_Ioi]
  exact Set.mem_singleton v

/-- The value is independently defined as an infimum of worst-case losses.
An exact rational QF description of its strict threshold set implies algebraicity
of every finite value. Neither that description nor its effective computation
is assumed to be an already-known minimax value. -/
theorem finite_value_algebraic_of_qf_thresholds {D T Z : Type*}
    (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ) (φ : QFFormula 1)
    (hφ : φ.solutionSet1 = MemoryDecision.thresholds feasible loss memory m)
    (v : ℝ) (hv : MemoryDecision.value feasible loss memory m = (v : EReal)) :
    IsAlgebraic (R := ℚ) v := by
  apply ray_endpoint_algebraic φ v
  exact hφ.trans (MemoryDecision.thresholds_eq_ray_of_value_eq
    feasible loss memory m v hv)

end MemorySemialgebraic
