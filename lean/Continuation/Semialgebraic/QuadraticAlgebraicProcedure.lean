module
public import Continuation.Semialgebraic.QuadraticInput
public import Continuation.Semialgebraic.AlgebraicSpecialization
public import Continuation.Semialgebraic.EffectiveProcedure
public import Continuation.Quadratic.Operational
public meta import Continuation.Semialgebraic.QuadraticInput
public meta import Continuation.Semialgebraic.AlgebraicSpecialization
public meta import Continuation.Semialgebraic.EffectiveProcedure

@[expose] public section
namespace MemorySemialgebraic.QuadraticAlgebraicProcedure
open SymbolicQE AlgebraicParameters

/-- Concrete quadratic loss syntax with finitely specified algebraic parameters. -/
def algebraicInput (N : ℕ) (L R : Code) : FirstOrder ((N+N*N)+1) :=
  specializeTwoParameters L R (QuadraticLossSyntax.parametricInput N)

theorem algebraicInput_correct (N : ℕ) (L R : Code) (hL : 0 ≤ L.value)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (l : ℝ) :
    (algebraicInput N L R).evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      QuadraticOperational.feasible N L.value R.value d T l := by
  rw [algebraicInput,specializeTwoParameters_correct]
  exact QuadraticLossSyntax.parametricInput_correct N L.value R.value hL d T l

/-- The algorithm receives rational syntax and algebraic codes, with no real-value oracle. -/
def endpoint (N m : ℕ) (L R : Code) : EndpointSelection.Output :=
  EffectiveProcedure.methodEndpoint N m (algebraicInput N L R)

def strictGain (N m : ℕ) (L R : Code) : Bool :=
  EffectiveProcedure.strictGain N m (algebraicInput N L R)

def leastSufficientMemory (N : ℕ) (L R : Code) : Option ℕ :=
  EffectiveProcedure.leastSufficientMemory N (algebraicInput N L R)

/-- Every horizon and memory budget yields the sharp quadratic benchmark endpoint. -/
theorem endpoint_correct (N m : ℕ) (L R : Code) (hL : 0 < L.value) :
    (endpoint N m L R).Denotes
      ((L.value*R.value^2/(2*(2*(N:ℝ)+1)^2) : ℝ) : EReal) := by
  have h := EffectiveProcedure.methodEndpoint_correct N m (algebraicInput N L R)
    (QuadraticOperational.feasible N L.value R.value) (algebraicInput_correct N L R hL.le)
  change (endpoint N m L R).Denotes
    (MemoryDecision.value (QuadraticOperational.feasible N L.value R.value)
      (QuadraticOperational.loss N) (QuadraticOperational.memory N) m) at h
  rwa [QuadraticOperational.value_eq N m L.value R.value hL] at h

/-- Extra memory never strictly improves the quadratic optimum. -/
theorem strictGain_false (N m : ℕ) (L R : Code) (hL : 0 < L.value) :
    strictGain N m L R = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hb := (EffectiveProcedure.strictGain_correct N m (algebraicInput N L R)
    (QuadraticOperational.feasible N L.value R.value) (algebraicInput_correct N L R hL.le)).mp h
  exact QuadraticOperational.no_memory_gain N m L.value R.value hL hb

/-- The finite budget scan returns zero additional registers, for every horizon. -/
theorem leastSufficientMemory_zero (N : ℕ) (L R : Code) (hL : 0 < L.value) :
    leastSufficientMemory N L R = some 0 := by
  obtain ⟨m,_,hout,hmin⟩ := EffectiveProcedure.leastSufficientMemory_correct N
    (algebraicInput N L R) (QuadraticOperational.feasible N L.value R.value)
    (algebraicInput_correct N L R hL.le)
  have he : MemoryDecision.value (QuadraticOperational.feasible N L.value R.value)
      (fun _ _ z => z) (MemorySelection.memory N) 0 =
      MemorySelection.unrestrictedValue (QuadraticOperational.feasible N L.value R.value)
        (fun _ _ z => z) := by
    calc
      _ = MemoryDecision.value (QuadraticOperational.feasible N L.value R.value)
          (fun _ _ z => z) (MemorySelection.memory N) (N/2) := by
          change MemoryDecision.value _ (QuadraticOperational.loss N) (QuadraticOperational.memory N) 0 =
            MemoryDecision.value _ (QuadraticOperational.loss N) (QuadraticOperational.memory N) (N/2)
          rw [QuadraticOperational.value_eq N 0 L.value R.value hL,
            QuadraticOperational.value_eq N (N/2) L.value R.value hL]
      _ = _ := MemorySelection.value_eq_unrestricted _ _ (N/2) le_rfl
  have hm0 : m = 0 := Nat.eq_zero_of_le_zero (hmin.2 he)
  simpa only [leastSufficientMemory,hm0] using hout

end MemorySemialgebraic.QuadraticAlgebraicProcedure
