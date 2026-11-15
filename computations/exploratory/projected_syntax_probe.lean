module
public import Continuation.Semialgebraic.ProjectedBoundedInput
public meta import Continuation.Semialgebraic.ProjectedBoundedInput
open MemorySemialgebraic MemorySemialgebraic.SymbolicQE
open MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput

@[expose] def binderTreeSize : {n : ℕ} → FirstOrder n → ℕ
  | _, .atom _ => 1
  | _, .conj f g => 1 + binderTreeSize f + binderTreeSize g
  | _, .disj f g => 1 + binderTreeSize f + binderTreeSize g
  | _, .neg f => 1 + binderTreeSize f
  | _, .ex f => 1 + binderTreeSize f
  | _, .all f => 1 + binderTreeSize f

-- Generate actual projected syntax, including projection's universal test-point binder.
#eval binderTreeSize (input 1 (d := 1) (k := 0) Fin.elim0 .tru
  (slopeBall 1 (.constant 1)) (.constant 1))
#print axioms ProjectedLossSyntax.lossFormula_correct
#print axioms ProjectedProcedureInput.endpoint_correct
#print axioms ProjectedProcedureInput.strictGain_correct
#print axioms ProjectedProcedureInput.leastSufficientMemory_correct
#print axioms ProjectedProcedureInput.boundedEndpoint_finite
