module
public import Continuation.Semialgebraic.ProjectedLossSyntax
public import Continuation.Semialgebraic.SmoothProcedureInput
public import Continuation.Semialgebraic.EffectiveProcedure
public import Continuation.Semialgebraic.AlgebraicSpecialization
public import Continuation.Projected.OperationalThresholds

/-! # Effective projected procedure from the supplied domain formula

The input consists only of finite rational formula syntax and finitely specified
algebraic coefficients. All trajectory coordinates, projection test points and
coefficient witnesses are bound by the generated first-order formula.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput
open ProjectedLossSyntax AlgebraicParameters ProcedureSyntax

/-- Insert a domain formula's parameter coordinates into a larger free-variable context. -/
def extendDomain {d k n : ℕ} (κ : Formula (d+k)) (ρ : Fin k → Fin n) : Formula (d+n) :=
  κ.renameVariables (Fin.addCases (Fin.castAdd n) (fun i => Fin.natAdd d (ρ i)))

@[simp] theorem domain_extendDomain {d k n : ℕ} (κ : Formula (d+k))
    (ρ : Fin k → Fin n) (v : Fin n → ℝ) :
    domain (extendDomain κ ρ) v = domain κ (v ∘ ρ) := by
  ext x
  simp only [domain, Set.mem_ofPred_eq, extendDomain, Formula.renameVariables_correct]
  have h : (fun i => Fin.addCases (fun j => x j) v
      (Fin.addCases (Fin.castAdd n) (fun j => Fin.natAdd d (ρ j)) i)) =
      Fin.addCases (fun j => x j) (v ∘ ρ) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left]
    · intro j
      simp only [Fin.addCases_right, Function.comp_apply]
  simp only [Function.comp_def, h]

/-- Coordinates are the fixed algebraic parameters, followed by loss and method coefficients. -/
def parameterInput (N : ℕ) {d k : ℕ} (κ β : Formula (d+k)) (R : Expr k) :
    FirstOrder (k+((N+N*N)+1)) :=
  lossFormula
    (extendDomain κ (Fin.castAdd ((N+N*N)+1)))
    (extendDomain β (Fin.castAdd ((N+N*N)+1)))
    (R.renameVariables (Fin.castAdd ((N+N*N)+1))) (.variable (Fin.natAdd k 0))
    (SmoothProcedureInput.coefficientHistory N (fun i => Fin.natAdd k i.succ))

theorem parameterInput_model (N : ℕ) {d k : ℕ} (κ β : Formula (d+k)) (R : Expr k)
    (a : Fin k → ℝ) (s : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (l : ℝ) :
    (parameterInput N κ β R).evalReal (Fin.addCases a (Fin.cons l (packCoefficients N s T.val))) ↔
      l ∈ ProjectedLossModel.modelLossSet (RealizationCore.W_of N s T.val)
        (domain κ a) (domain β a) (R.evalReal a) := by
  rw [parameterInput, lossFormula_model, SmoothProcedureInput.coefficientHistory_correct]
  simp only [domain_extendDomain, Expr.renameVariables_correct, Expr.evalReal,
    Function.comp_def, Fin.addCases_left, Fin.addCases_right, Fin.cons_zero, Fin.cons_succ,
    unpackStep_pack, unpackIncrement_pack]

/-- Concrete projected loss input, directly consumable by the complete effective procedure. -/
def input (N : ℕ) {d k : ℕ} (cs : Fin k → Code) (κ β : Formula (d+k)) (R : Expr k) :
    FirstOrder ((N+N*N)+1) := specializePrefix cs (parameterInput N κ β R)

theorem input_model (N : ℕ) {d k : ℕ} (cs : Fin k → Code) (κ β : Formula (d+k)) (R : Expr k)
    (s : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (l : ℝ) :
    (input N cs κ β R).evalReal (Fin.cons l (packCoefficients N s T.val)) ↔
      l ∈ ProjectedLossModel.modelLossSet (RealizationCore.W_of N s T.val)
        (domain κ (fun i => (cs i).value)) (domain β (fun i => (cs i).value))
        (R.evalReal (fun i => (cs i).value)) := by
  rw [input, specializePrefix_correct]
  exact parameterInput_model N κ β R _ s T l

theorem input_correct (N : ℕ) {d k : ℕ} (cs : Fin k → Code) (κ β : Formula (d+k)) (R : Expr k)
    (hK : Convex ℝ (domain κ (fun i => (cs i).value)))
    (hcK : IsClosed (domain κ (fun i => (cs i).value)))
    (hneK : (domain κ (fun i => (cs i).value)).Nonempty)
    (hB0 : (0 : Space d) ∈ domain β (fun i => (cs i).value))
    (hR : 0 ≤ R.evalReal (fun i => (cs i).value))
    (s : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (l : ℝ) :
    (input N cs κ β R).evalReal (Fin.cons l (packCoefficients N s T.val)) ↔
      ProjectedOperational.feasible hK hcK hneK N (domain β (fun i => (cs i).value))
        (R.evalReal (fun i => (cs i).value)) s T l := by
  change _ ↔ l ∈ ProjectedLossModel.actualLossSet hK hcK hneK _ _
  rw [ProjectedLossModel.lossSet_eq hK hcK hneK hB0 hR]
  exact input_model N cs κ β R s T l

/-- Compute the exact projected minimax endpoint from domain and slope-set syntax. -/
def endpoint (N m : ℕ) {d k : ℕ} (cs : Fin k → Code) (κ β : Formula (d+k)) (R : Expr k) :
    EndpointSelection.Output := EffectiveProcedure.methodEndpoint N m (input N cs κ β R)

def strictGain (N m : ℕ) {d k : ℕ} (cs : Fin k → Code) (κ β : Formula (d+k)) (R : Expr k) : Bool :=
  EffectiveProcedure.strictGain N m (input N cs κ β R)

def leastSufficientMemory (N : ℕ) {d k : ℕ} (cs : Fin k → Code) (κ β : Formula (d+k))
    (R : Expr k) : Option ℕ := EffectiveProcedure.leastSufficientMemory N (input N cs κ β R)

section Correctness
variable (N : ℕ) {d k : ℕ} (cs : Fin k → Code) (κ β : Formula (d+k)) (R : Expr k)
variable (hK : Convex ℝ (domain κ (fun i => (cs i).value)))
  (hcK : IsClosed (domain κ (fun i => (cs i).value)))
  (hneK : (domain κ (fun i => (cs i).value)).Nonempty)
  (hB0 : (0 : Space d) ∈ domain β (fun i => (cs i).value))
  (hR : 0 ≤ R.evalReal (fun i => (cs i).value))

include hB0 hR

theorem endpoint_correct (m : ℕ) :
    (endpoint N m cs κ β R).Denotes
      (MemoryDecision.value
        (ProjectedOperational.feasible hK hcK hneK N (domain β (fun i => (cs i).value))
          (R.evalReal (fun i => (cs i).value)))
        (ProjectedOperational.loss N) (ProjectedOperational.memory N) m) :=
  EffectiveProcedure.methodEndpoint_correct N m (input N cs κ β R) _
    (input_correct N cs κ β R hK hcK hneK hB0 hR)

theorem strictGain_correct (m : ℕ) :
    strictGain N m cs κ β R = true ↔
      MemoryDecision.value
        (ProjectedOperational.feasible hK hcK hneK N (domain β (fun i => (cs i).value))
          (R.evalReal (fun i => (cs i).value)))
        (ProjectedOperational.loss N) (ProjectedOperational.memory N) (m+1) <
      MemoryDecision.value
        (ProjectedOperational.feasible hK hcK hneK N (domain β (fun i => (cs i).value))
          (R.evalReal (fun i => (cs i).value)))
        (ProjectedOperational.loss N) (ProjectedOperational.memory N) m :=
  EffectiveProcedure.strictGain_correct N m (input N cs κ β R) _
    (input_correct N cs κ β R hK hcK hneK hB0 hR)

theorem leastSufficientMemory_correct :
    ∃ m ≤ N/2, leastSufficientMemory N cs κ β R = some m ∧
      IsLeast {j : ℕ | MemoryDecision.value
        (ProjectedOperational.feasible hK hcK hneK N (domain β (fun i => (cs i).value))
          (R.evalReal (fun i => (cs i).value)))
        (ProjectedOperational.loss N) (ProjectedOperational.memory N) j =
        ProjectedOperational.unrestrictedValue hK hcK hneK N
          (domain β (fun i => (cs i).value)) (R.evalReal (fun i => (cs i).value))} m :=
  EffectiveProcedure.leastSufficientMemory_correct N (input N cs κ β R) _
    (input_correct N cs κ β R hK hcK hneK hB0 hR)

end Correctness
end MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput
