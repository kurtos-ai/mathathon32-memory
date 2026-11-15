module
public import Continuation.Semialgebraic.ProcedureSyntax
public import Continuation.Semialgebraic.ExecutableMemory
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.ProcedureSyntax
open Matrix

/-- The step vector precedes the flattened increment matrix. -/
def packCoefficients (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) :
    Fin (N+N*N) → ℝ := Fin.addCases d (matrixAssignment N T)

def unpackStep (N : ℕ) (a : Fin (N+N*N) → ℝ) : Fin N → ℝ :=
  fun i => a (Fin.castAdd (N*N) i)

def unpackIncrement (N : ℕ) (a : Fin (N+N*N) → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => a (Fin.natAdd N (finProdFinEquiv (i,j)))

@[simp] theorem unpackStep_pack (N : ℕ) (d : Fin N → ℝ)
    (T : Matrix (Fin N) (Fin N) ℝ) : unpackStep N (packCoefficients N d T)=d := by
  funext i
  simp [unpackStep,packCoefficients]

@[simp] theorem unpackIncrement_pack (N : ℕ) (d : Fin N → ℝ)
    (T : Matrix (Fin N) (Fin N) ℝ) : unpackIncrement N (packCoefficients N d T)=T := by
  ext i j
  simp [unpackIncrement,packCoefficients,matrixAssignment]

@[simp] theorem packCoefficients_unpack (N : ℕ) (a : Fin (N+N*N) → ℝ) :
    packCoefficients N (unpackStep N a) (unpackIncrement N a)=a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [packCoefficients,unpackStep]
  · simp only [packCoefficients,Fin.addCases_right,matrixAssignment,unpackIncrement]
    change a (Fin.natAdd N (finProdFinEquiv (finProdFinEquiv.symm j))) = _
    rw [Equiv.apply_symm_apply]

/-- An explicit bijection between all method coefficients and one finite real vector. -/
def coefficientEquiv (N : ℕ) : (Fin (N+N*N) → ℝ) ≃
    (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ where
  toFun a := (unpackStep N a,unpackIncrement N a)
  invFun a := packCoefficients N a.1 a.2
  left_inv := packCoefficients_unpack N
  right_inv a := by simp

/-- The increment entries are selected directly from the packed variable coordinates. -/
def incrementEntries (N : ℕ) : Matrix (Fin N) (Fin N) (Expr (N+N*N)) :=
  fun i j => .variable (Fin.natAdd N (finProdFinEquiv (i,j)))

lemma incrementEntries_eval (N : ℕ) (a : Fin (N+N*N) → ℝ) :
    (incrementEntries N).map (Expr.evalReal a)=unpackIncrement N a := rfl

/-- The computed memory condition, now on the full coefficient vector. -/
def methodMemoryFormula (N m : ℕ) : Formula (N+N*N) :=
  memoryFormula N m (incrementEntries N)

theorem methodMemoryFormula_correct (N m : ℕ) (a : Fin (N+N*N) → ℝ) :
    (methodMemoryFormula N m).evalReal a ↔
      (∀ i j,i.val ≤ j.val → unpackIncrement N a i j=0) ∧
      MemoryRank.Incremental.Q N m (unpackIncrement N a) := by
  rw [methodMemoryFormula,memoryFormula_correct,incrementEntries_eval]
  rfl

/-- A concrete threshold formula over all step and increment coefficients. -/
def methodThresholdFormula (N m : ℕ) (input : FirstOrder ((N+N*N)+1)) : FirstOrder 1 :=
  thresholdFormula input (methodMemoryFormula N m)

/-- Any exact finite loss formula yields the actual operational threshold set.
The syntax is built independently of this semantic exactness premise. -/
theorem methodThresholdFormula_correct (N m : ℕ)
    (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (packCoefficients N d T.val)) ↔ actualLoss d T l)
    (γ : ℝ) :
    (methodThresholdFormula N m input).evalReal (fun _ => γ) ↔
      γ ∈ MemoryDecision.thresholds actualLoss (fun _ _ l => l)
        (fun k => {T | MemoryRank.Incremental.Q N k T.val}) m := by
  rw [methodThresholdFormula,thresholdFormula_correct]
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    obtain ⟨hstrict,hQ⟩ := (methodMemoryFormula_correct N m a).mp ha
    let T : RealizationCore.StrictIncrement N := ⟨unpackIncrement N a,hstrict⟩
    refine ⟨T,⟨unpackStep N a,b,hb,?_⟩,hQ⟩
    intro l hl
    apply h l
    have he := (hinput (unpackStep N a) T l).mpr hl
    simpa only [T,packCoefficients_unpack] using he
  · rintro ⟨T,⟨d,b,hb,h⟩,hQ⟩
    refine ⟨packCoefficients N d T.val,?_,b,hb,?_⟩
    · rw [methodMemoryFormula_correct,unpackIncrement_pack]
      exact ⟨T.property,hQ⟩
    · intro l hl
      exact h l ((hinput d T l).mp hl)

/-- The constructed formula detects strict inequality for the independent actual minimax value. -/
theorem methodThresholdFormula_value (N m : ℕ)
    (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (packCoefficients N d T.val)) ↔ actualLoss d T l)
    (γ : ℝ) :
    (methodThresholdFormula N m input).evalReal (fun _ => γ) ↔
      MemoryDecision.value actualLoss (fun _ _ l => l)
        (fun k => {T | MemoryRank.Incremental.Q N k T.val}) m < (γ : EReal) := by
  rw [methodThresholdFormula_correct N m input actualLoss hinput,
    MemoryDecision.threshold_iff_value_lt]

end MemorySemialgebraic.SymbolicQE.ProcedureSyntax
