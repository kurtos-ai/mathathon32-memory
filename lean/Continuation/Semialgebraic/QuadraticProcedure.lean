module
public import Continuation.Semialgebraic.QuadraticInput
public import Continuation.Semialgebraic.EffectiveProcedure
public import Continuation.Quadratic.Operational
@[expose] public section
namespace MemorySemialgebraic.QuadraticProcedure
open SymbolicQE QuadraticLossSyntax

/-- The general algorithm's output denotes the exact quadratic benchmark value. -/
theorem endpoint_correct (N m : ℕ) (L R : ℚ) (hL : 0 < L) :
    (EffectiveProcedure.methodEndpoint N m (input N L R)).Denotes
      (((L:ℝ)*(R:ℝ)^2/(2*(2*(N:ℝ)+1)^2) : ℝ) : EReal) := by
  have h := EffectiveProcedure.methodEndpoint_correct N m (input N L R)
    (QuadraticOperational.feasible N L R) (input_correct N L R hL.le)
  change (EffectiveProcedure.methodEndpoint N m (input N L R)).Denotes
    (MemoryDecision.value (QuadraticOperational.feasible N L R) (QuadraticOperational.loss N)
      (QuadraticOperational.memory N) m) at h
  rwa [QuadraticOperational.value_eq N m L R (by exact_mod_cast hL)] at h

/-- The complete procedure decides no strict memory gain for any quadratic horizon or budget. -/
theorem strictGain_false (N m : ℕ) (L R : ℚ) (hL : 0 < L) :
    EffectiveProcedure.strictGain N m (input N L R) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hb := (EffectiveProcedure.strictGain_correct N m (input N L R)
    (QuadraticOperational.feasible N L R) (input_correct N L R hL.le)).mp h
  exact QuadraticOperational.no_memory_gain N m L R (by exact_mod_cast hL) hb

/-- Its returned least auxiliary memory is zero, for every query horizon. -/
theorem leastSufficientMemory_zero (N : ℕ) (L R : ℚ) (hL : 0 < L) :
    EffectiveProcedure.leastSufficientMemory N (input N L R) = some 0 := by
  obtain ⟨m,_,hout,hmin⟩ := EffectiveProcedure.leastSufficientMemory_correct N (input N L R)
    (QuadraticOperational.feasible N L R) (input_correct N L R hL.le)
  have he : MemoryDecision.value (QuadraticOperational.feasible N L R)
      (fun _ _ z => z) (MemorySelection.memory N) 0 =
      MemorySelection.unrestrictedValue (QuadraticOperational.feasible N L R) (fun _ _ z => z) := by
    calc
      _ = MemoryDecision.value (QuadraticOperational.feasible N L R)
          (fun _ _ z => z) (MemorySelection.memory N) (N/2) := by
          change MemoryDecision.value _ (QuadraticOperational.loss N) (QuadraticOperational.memory N) 0 =
            MemoryDecision.value _ (QuadraticOperational.loss N) (QuadraticOperational.memory N) (N/2)
          rw [QuadraticOperational.value_eq N 0 L R (by exact_mod_cast hL),
            QuadraticOperational.value_eq N (N/2) L R (by exact_mod_cast hL)]
      _ = _ := MemorySelection.value_eq_unrestricted _ _ (N/2) le_rfl
  have hm0 : m = 0 := Nat.eq_zero_of_le_zero (hmin.2 he)
  simpa only [hm0] using hout

end MemorySemialgebraic.QuadraticProcedure
