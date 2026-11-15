module
public import Continuation.Semialgebraic.MemorySelection
public import Continuation.Semialgebraic.NonlinearElimination
public meta import Continuation.Semialgebraic.MemorySelection
public meta import Continuation.Semialgebraic.NonlinearElimination

/-!
# Complete effective minimax and memory procedure

These public algorithms instantiate the proved rational QE engine. Inputs are finite
rational formulas, or finite algebraic coefficient codes together with formula syntax.
No minimax value, endpoint oracle, elimination oracle, or proof of an unknown optimum
is an algorithm input. Semantic exactness of the supplied finite loss model is used
only in correctness theorems relating the computed output to actual oracle risk.
-/

@[expose] public section
namespace MemorySemialgebraic.EffectiveProcedure
open SymbolicQE AlgebraicParameters EndpointSelection

/-- Effective QE for arbitrary formulas over finitely specified real algebraic coefficients. -/
def eliminateAlgebraic {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k n) : Formula n :=
  eliminateFirstOrder Formula.eliminateExists cs f

theorem eliminateAlgebraic_correct {k n : ℕ} (cs : Fin k → Code)
    (f : AlgebraicFirstOrder k n) (v : Fin n → ℝ) :
    (eliminateAlgebraic cs f).evalReal v ↔ f.evalReal (fun i => (cs i).value) v :=
  eliminateFirstOrder_correct Formula.eliminateExists Formula.eliminateExists_correct cs f v

/-- Compute an exact extended endpoint from a rational first-order threshold description. -/
def endpoint (f : FirstOrder 1) : Output := select f.quantifierEliminate

theorem endpoint_correct {D T Z : Type*}
    (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ) (f : FirstOrder 1)
    (hf : ∀ γ : ℝ, f.evalReal (fun _ => γ) ↔ γ ∈ MemoryDecision.thresholds feasible loss memory m) :
    (endpoint f).Denotes (MemoryDecision.value feasible loss memory m) := by
  apply select_minimax feasible loss memory m
  ext γ
  change f.quantifierEliminate.toQF.eval (fun _ => γ) ↔ _
  rw [FirstOrder.quantifierEliminate_toQF]
  exact hf γ

/-- Compute an exact endpoint from an algebraic-coefficient first-order threshold description. -/
def algebraicEndpoint {k : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k 1) : Output :=
  AlgebraicParameters.minimaxOutput Formula.eliminateExists cs f

theorem algebraicEndpoint_correct {D T Z : Type*} {k : ℕ} (cs : Fin k → Code)
    (f : AlgebraicFirstOrder k 1) (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ)
    (hf : ∀ γ : ℝ, f.evalReal (fun i => (cs i).value) (fun _ => γ) ↔
      γ ∈ MemoryDecision.thresholds feasible loss memory m) :
    (algebraicEndpoint cs f).Denotes (MemoryDecision.value feasible loss memory m) :=
  AlgebraicParameters.minimaxOutput_correct Formula.eliminateExists Formula.eliminateExists_correct
    cs f feasible loss memory m hf

/-- Compare certified algebraic or infinite endpoints with no real-number comparison oracle. -/
def compareEndpoints (a b : Output) : Option Ordering := compareOutputs Formula.eliminateExists a b

theorem compareEndpoints_correct (a b : Output) (u v : EReal) (ha : a.Denotes u) (hb : b.Denotes v) :
    compareEndpoints a b = some (valueOrdering u v) :=
  compareOutputs_correct Formula.eliminateExists Formula.eliminateExists_correct a b u v ha hb

lemma compareEndpoints_none_iff (a b : Output) :
    compareEndpoints a b = none ↔ a = .invalid ∨ b = .invalid :=
  compareOutputs_none_iff Formula.eliminateExists a b

/-- Compute the minimax endpoint directly from the finite actual loss formula and memory minors. -/
def methodEndpoint (N m : ℕ) (input : FirstOrder ((N+N*N)+1)) : Output :=
  select (MemorySelection.methodThresholds Formula.eliminateExists N input m)

theorem methodEndpoint_correct (N m : ℕ) (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) :
    (methodEndpoint N m input).Denotes
      (MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) m) :=
  select_minimax actualLoss (fun _ _ l => l) (MemorySelection.memory N) m _
    (MemorySelection.methodThresholds_correct Formula.eliminateExists Formula.eliminateExists_correct
      N m input actualLoss hinput)

lemma methodEndpoint_ne_invalid (N m : ℕ) (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) : methodEndpoint N m input ≠ .invalid :=
  MemorySelection.methodThresholdOutput_ne_invalid Formula.eliminateExists Formula.eliminateExists_correct
    N m input actualLoss hinput

/-- Decide strict improvement from one additional register. -/
def strictGain (N m : ℕ) (input : FirstOrder ((N+N*N)+1)) : Bool :=
  MemorySelection.methodStrictGain Formula.eliminateExists N m input

theorem strictGain_correct (N m : ℕ) (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) :
    strictGain N m input = true ↔
      MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) (m+1) <
        MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) m :=
  MemorySelection.methodStrictGain_correct Formula.eliminateExists Formula.eliminateExists_correct
    N m input actualLoss hinput

/-- Compute the least sufficient additional-memory budget by a finite scan through N/2. -/
def leastSufficientMemory (N : ℕ) (input : FirstOrder ((N+N*N)+1)) : Option ℕ :=
  MemorySelection.methodLeastBudget Formula.eliminateExists N input

theorem leastSufficientMemory_correct (N : ℕ) (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) :
    ∃ m ≤ N/2, leastSufficientMemory N input = some m ∧
      IsLeast {j : ℕ | MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) j =
        MemorySelection.unrestrictedValue actualLoss (fun _ _ l => l)} m :=
  MemorySelection.methodLeastBudget_correct Formula.eliminateExists Formula.eliminateExists_correct
    N input actualLoss hinput

/-- Algebraic input coefficients are rationalized inside the displayed complete procedure. -/
def algebraicMethodEndpoint (N m : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1)) : Output :=
  methodEndpoint N m (rationalizeFirstOrder cs input)

theorem algebraicMethodEndpoint_correct (N m : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (fun i => (cs i).value)
      (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔ actualLoss d T l) :
    (algebraicMethodEndpoint N m cs input).Denotes
      (MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) m) := by
  apply methodEndpoint_correct N m (rationalizeFirstOrder cs input) actualLoss
  intro d T l
  exact (rationalizeFirstOrder_exact cs input _).trans (hinput d T l)

def algebraicStrictGain (N m : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1)) : Bool :=
  MemorySelection.algebraicMethodStrictGain Formula.eliminateExists N m cs input

theorem algebraicStrictGain_correct (N m : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (fun i => (cs i).value)
      (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔ actualLoss d T l) :
    algebraicStrictGain N m cs input = true ↔
      MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) (m+1) <
        MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) m :=
  MemorySelection.algebraicMethodStrictGain_correct Formula.eliminateExists Formula.eliminateExists_correct
    N m cs input actualLoss hinput

def algebraicLeastSufficientMemory (N : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1)) : Option ℕ :=
  MemorySelection.algebraicMethodLeastBudget Formula.eliminateExists N cs input

theorem algebraicLeastSufficientMemory_correct (N : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (fun i => (cs i).value)
      (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔ actualLoss d T l) :
    ∃ m ≤ N/2, algebraicLeastSufficientMemory N cs input = some m ∧
      IsLeast {j : ℕ | MemoryDecision.value actualLoss (fun _ _ l => l) (MemorySelection.memory N) j =
        MemorySelection.unrestrictedValue actualLoss (fun _ _ l => l)} m :=
  MemorySelection.algebraicMethodLeastBudget_correct Formula.eliminateExists Formula.eliminateExists_correct
    N cs input actualLoss hinput

end MemorySemialgebraic.EffectiveProcedure
