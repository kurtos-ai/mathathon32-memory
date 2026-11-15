module
public import Continuation.Semialgebraic.NonlinearElimination
public meta import Continuation.Semialgebraic.NonlinearElimination

/-! # Runtime checks of general nonlinear elimination

These execute the symbolic elimination program and evaluate its generated rational
quantifier-free formula. General correctness is proved in `NonlinearElimination`.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE

/-- info: true -/
#guard_msgs in
#eval FirstOrder.decideSentence (.ex (.atom (.eqZero (.variable 0))))

/-- info: false -/
#guard_msgs in
#eval FirstOrder.decideSentence (.ex (.atom (.eqZero
  (.add (.mul (.variable 0) (.variable 0)) (.constant 1)))))

/-- info: true -/
#guard_msgs in
#eval FirstOrder.decideSentence (.ex (.atom (.eqZero
  (.add (.mul (.variable 0) (.variable 0)) (.constant (-2))))))

/-- info: true -/
#guard_msgs in
#eval FirstOrder.decideSentence (.all (.atom (.nonnegative
  (.mul (.variable 0) (.variable 0)))))

end MemorySemialgebraic.SymbolicQE
