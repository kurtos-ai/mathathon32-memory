module
public import Continuation.Semialgebraic.SmoothLossSyntax
public import Continuation.Semialgebraic.ProcedureCoefficients
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.SmoothProcedureInput
open Matrix SmoothGramModel ProcedureSyntax

def extendedIncrement {N n : ℕ} (T : Matrix (Fin N) (Fin N) (Expr n)) (i j : ℕ) : Expr n :=
  if h : i < N ∧ j < N then T ⟨i,h.1⟩ ⟨j,h.2⟩ else .constant 0

@[simp] theorem extendedIncrement_correct {N n : ℕ} (T : Matrix (Fin N) (Fin N) (Expr n))
    (a : Fin n → ℝ) (i j : ℕ) :
    (extendedIncrement T i j).evalReal a =
      RealizationCore.extendedIncrement (T.map (Expr.evalReal a)) i j := by
  by_cases h : i < N ∧ j < N <;>
    simp [-Expr.evalReal_refines,extendedIncrement,RealizationCore.extendedIncrement,h,
      Expr.evalReal,Matrix.map_apply]


/-- Explicit inverse coefficient conversion, using finite lists for the telescoping sums. -/
def history {N n : ℕ} (d : Fin N → Expr n) (T : Matrix (Fin N) (Fin N) (Expr n)) :
    Matrix (Fin (N+1)) (Fin (N+1)) (Expr n) := fun i j =>
  if h : j.val < i.val then .add (d ⟨j.val,by omega⟩)
    (Expr.sumList (List.ofFn fun k : Fin (i.val-(j.val+1)) =>
      extendedIncrement T (j.val+1+k.val) j.val))
  else .constant 0

theorem history_correct {N n : ℕ} (d : Fin N → Expr n)
    (T : Matrix (Fin N) (Fin N) (Expr n)) (a : Fin n → ℝ) :
    (history d T).map (Expr.evalReal a) =
      RealizationCore.W_of N (fun i => (d i).evalReal a) (T.map (Expr.evalReal a)) := by
  ext i j
  by_cases h : j.val < i.val
  · simp only [history,Matrix.map_apply,RealizationCore.W_of,h,dite_true,Expr.evalReal,
      Expr.eval_sumList_ofFn,extendedIncrement_correct]
    rw [Finset.sum_Ico_eq_sum_range]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun k =>
      RealizationCore.extendedIncrement (T.map (Expr.evalReal a)) (j.val+1+k) j.val) _
  · simp only [history,Matrix.map_apply,RealizationCore.W_of,h,dite_false,Expr.evalReal,Rat.cast_zero]

def coefficientHistory {n : ℕ} (N : ℕ) (ρ : Fin (N+N*N) → Fin n) :
    Matrix (Fin (N+1)) (Fin (N+1)) (Expr n) :=
  history (fun i => .variable (ρ (Fin.castAdd (N*N) i)))
    (fun i j => .variable (ρ (Fin.natAdd N (finProdFinEquiv (i,j)))))

theorem coefficientHistory_correct {n : ℕ} (N : ℕ) (ρ : Fin (N+N*N) → Fin n)
    (a : Fin n → ℝ) :
    (coefficientHistory N ρ).map (Expr.evalReal a) =
      RealizationCore.W_of N (unpackStep N (a ∘ ρ)) (unpackIncrement N (a ∘ ρ)) := by
  exact history_correct (fun i => .variable (ρ (Fin.castAdd (N*N) i)))
    (fun i j => .variable (ρ (Fin.natAdd N (finProdFinEquiv (i,j))))) a

/-- Concrete rational-parameter smooth loss syntax with the exact ProcedureCoefficients interface. -/
def input (N : ℕ) (L R : ℚ) : FirstOrder ((N+N*N)+1) :=
  SmoothLossSyntax.lossFormula (.constant L) (.constant R) (.variable 0)
    (coefficientHistory N Fin.succ)

theorem input_correct (N : ℕ) (L R : ℚ) (hL : 0<(L:ℝ)) (hR : 0≤(R:ℝ))
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (l : ℝ) :
    (input N L R).evalReal (Fin.cons l (packCoefficients N d T.val)) ↔
      l ∈ actualLossSet N (RealizationCore.W_of N d T.val) L R := by
  have h := SmoothLossSyntax.lossFormula_correct (.constant L) (.constant R) (.variable 0)
    (coefficientHistory N Fin.succ) (Fin.cons l (packCoefficients N d T.val)) hL hR
  rw [coefficientHistory_correct] at h
  simpa only [input,Expr.evalReal,Fin.cons_zero,Function.comp_def,Fin.cons_succ,
    unpackStep_pack,unpackIncrement_pack] using h


/-- Free parameter version: coordinates are loss, smoothness, radius, then all method coefficients. -/
def parametricInput (N : ℕ) : FirstOrder ((N+N*N)+3) :=
  SmoothLossSyntax.lossFormula (.variable (0 : Fin ((N+N*N)+2)).succ)
    (.variable (0 : Fin ((N+N*N)+1)).succ.succ) (.variable 0)
    (coefficientHistory N (fun i => i.succ.succ.succ))

theorem parametricInput_correct (N : ℕ) (L R : ℝ) (hL : 0<L) (hR : 0≤R)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (l : ℝ) :
    (parametricInput N).evalReal
      (Fin.cons l (Fin.cons L (Fin.cons R (packCoefficients N d T.val)))) ↔
      l ∈ actualLossSet N (RealizationCore.W_of N d T.val) L R := by
  have h := SmoothLossSyntax.lossFormula_correct
    (.variable (0 : Fin ((N+N*N)+2)).succ) (.variable (0 : Fin ((N+N*N)+1)).succ.succ)
    (.variable 0) (coefficientHistory N (fun i => i.succ.succ.succ))
    (Fin.cons l (Fin.cons L (Fin.cons R (packCoefficients N d T.val)))) hL hR
  rw [coefficientHistory_correct] at h
  simpa only [parametricInput,Expr.evalReal,Fin.cons_zero,Function.comp_def,Fin.cons_succ,
    unpackStep_pack,unpackIncrement_pack] using h


/-- The concrete rational smooth input instantiates the executable operational threshold construction. -/
theorem threshold_correct (N m : ℕ) (L R : ℚ) (hL : 0<(L:ℝ)) (hR : 0≤(R:ℝ)) (γ : ℝ) :
    (methodThresholdFormula N m (input N L R)).evalReal (fun _ => γ) ↔
      MemoryDecision.value
        (fun (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) l => l ∈ actualLossSet N (RealizationCore.W_of N d T.val) L R)
        (fun _ _ l => l) (fun k => {T : RealizationCore.StrictIncrement N | MemoryRank.Incremental.Q N k T.val}) m < (γ:EReal) :=
  methodThresholdFormula_value N m (input N L R) _ (input_correct N L R hL hR) γ

end MemorySemialgebraic.SymbolicQE.SmoothProcedureInput
