module
public import Continuation.Semialgebraic.SmoothProcedure
public import Continuation.Semialgebraic.AlgebraicSpecialization
@[expose] public section
namespace MemorySemialgebraic.SmoothAlgebraicInput
open SymbolicQE AlgebraicParameters

/-- Concrete smooth loss syntax over specified algebraic smoothness and radius codes. -/
def input (N : ℕ) (L R : Code) : FirstOrder ((N+N*N)+1) :=
  specializeTwoParameters L R (SmoothProcedureInput.parametricInput N)

theorem input_correct (N : ℕ) (L R : Code) (hL : 0 < L.value) (hR : 0 ≤ R.value)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (l : ℝ) :
    (input N L R).evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      SmoothOperational.feasible N L.value R.value d T l := by
  rw [input,specializeTwoParameters_correct]
  exact SmoothProcedureInput.parametricInput_correct N L.value R.value hL hR d T l

/-- Algebraic codes enter only as rational defining polynomials and isolating intervals. -/
@[irreducible] def endpoint (N m : ℕ) (L R : Code) : EndpointSelection.Output :=
  EffectiveProcedure.methodEndpoint N m (input N L R)

def strictGain (N m : ℕ) (L R : Code) : Bool :=
  EffectiveProcedure.strictGain N m (input N L R)

def leastSufficientMemory (N : ℕ) (L R : Code) : Option ℕ :=
  EffectiveProcedure.leastSufficientMemory N (input N L R)

theorem endpoint_correct (N m : ℕ) (L R : Code) (hL : 0 < L.value) (hR : 0 ≤ R.value) :
    (endpoint N m L R).Denotes
      (MemoryDecision.value (SmoothOperational.feasible N L.value R.value) (SmoothOperational.loss N)
        (SmoothOperational.memory N) m) := by
  unfold endpoint
  exact EffectiveProcedure.methodEndpoint_correct N m _ _ (input_correct N L R hL hR)

theorem endpoint_sharp (N m : ℕ) (L R : Code)
    (hL : 0 < L.value) (hR : 0 < R.value) (hm : 1 ≤ m) :
    (endpoint N m L R).Denotes
      ((L.value*R.value^2/(2*(SmoothBenchmark.theta N N)^2) : ℝ) : EReal) := by
  have h := endpoint_correct N m L R hL hR.le
  rwa [SmoothDrori.operational_value_eq_all_queries N m L.value R.value hL hR hm] at h

theorem strictGain_correct (N m : ℕ) (L R : Code) (hL : 0 < L.value) (hR : 0 < R.value) :
    strictGain N m L R = true ↔ m=0 ∧ 2 ≤ N := by
  have h := EffectiveProcedure.strictGain_correct N m (input N L R)
    (SmoothOperational.feasible N L.value R.value) (input_correct N L R hL hR.le)
  exact h.trans (GJP.operational_strict_gain_iff m L.value R.value hL hR)

theorem leastSufficientMemory_correct (N : ℕ) (L R : Code) (hL : 0 < L.value) (hR : 0 < R.value) :
    leastSufficientMemory N L R = if N ≤ 1 then some 0 else some 1 := by
  obtain ⟨m,hm,hout,hmin⟩ := EffectiveProcedure.leastSufficientMemory_correct N
    (input N L R) (SmoothOperational.feasible N L.value R.value) (input_correct N L R hL hR.le)
  have hleast := SmoothProcedure.least_budget N L.value R.value hL hR
  have heq : m=(if N ≤ 1 then 0 else 1) := le_antisymm (hmin.2 hleast.1) (hleast.2 hmin.1)
  change EffectiveProcedure.leastSufficientMemory N (input N L R) = _
  rw [hout,heq]
  split <;> rfl

end MemorySemialgebraic.SmoothAlgebraicInput
