module
public import Continuation.Smooth.Operational
public import Continuation.Smooth.Attain.Attainment
@[expose] public section

namespace SmoothOperational
variable {N : ℕ} {L R : ℝ}

/-- The actual operational one-register infimum is attained by a coefficient map. -/
theorem exists_optimal_one_register (hL : 0 < L) (hR : 0 < R) :
    ∃ d : Fin N → ℝ,
      RegisterMachine.HasRealization N (RealizationCore.W_of N d 0) 1 ∧
      MemoryDecision.risk (feasible N L R) (loss N) d (zeroIncrement N) =
        MemoryDecision.value (feasible N L R) (loss N) (memory N) 0 := by
  obtain ⟨α,hα,_⟩ := SmoothAttain.isMinOn_attains_iInf (N:=N) hL hR
  refine ⟨fun j => -α j,?_,?_⟩
  · exact (mem_memory_iff_realization N 0 (zeroIncrement N) _).mp (zeroIncrement_mem N 0)
  · rw [zero_increment_risk,value_zero_eq_inf_risk0,hα]

theorem value_zero_bounds (hL : 0 < L) (hR : 0 < R) :
    0 ≤ MemoryDecision.value (feasible N L R) (loss N) (memory N) 0 ∧
    MemoryDecision.value (feasible N L R) (loss N) (memory N) 0 ≤
      ((L*R^2/2 : ℝ) : EReal) := by
  rw [value_zero_eq_inf_risk0]
  constructor
  · exact le_iInf (fun α => SmoothAttain.risk0_nonneg L R hL hR.le α)
  · apply (iInf_le (SmoothAttain.risk0 L R) (0 : Fin N → ℝ)).trans
    exact SmoothAttain.risk0_at_zero_le hL hR

end SmoothOperational
