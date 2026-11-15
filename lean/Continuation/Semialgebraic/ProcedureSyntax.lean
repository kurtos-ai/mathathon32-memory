module
public import Continuation.Semialgebraic.FirstOrderRename
public import Decision.ExactThresholds
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.ProcedureSyntax

/-- Coordinates of the coefficient vector before the final, free threshold coordinate. -/
def coefficientIndex {c : ℕ} (i : Fin c) : Fin (c+1) := Fin.castAdd 1 i

def thresholdIndex (c : ℕ) : Fin (c+1) := Fin.natAdd c 0

/-- In the universally quantified body the coordinates are loss, bound, coefficients, threshold. -/
def lossRenaming (c : ℕ) : Fin (c+1) → Fin ((c+1)+1+1) :=
  Fin.cases 0 (fun i => (coefficientIndex i).succ.succ)

lemma memory_assignment {c : ℕ} (a : Fin c → ℝ) (v : Fin 1 → ℝ) :
    Fin.addCases a v ∘ coefficientIndex = a := by
  funext i
  simp [coefficientIndex]

lemma loss_assignment {c : ℕ} (a : Fin c → ℝ) (v : Fin 1 → ℝ) (b l : ℝ) :
    Fin.cons l (Fin.cons b (Fin.addCases a v)) ∘ lossRenaming c = Fin.cons l a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [lossRenaming,coefficientIndex]

/-- A uniform loss bound strictly below the free threshold, expressed only from the input loss syntax. -/
def boundFormula {c : ℕ} (input : FirstOrder (c+1)) : FirstOrder ((c+1)+1) :=
  .conj
    (.atom (.positive (Expr.sub (.variable (thresholdIndex c).succ) (.variable 0))))
    (.all (.disj (.neg (input.renameVariables (lossRenaming c)))
      (.atom (.nonnegative (Expr.sub (.variable (0 : Fin ((c+1)+1)).succ) (.variable 0))))))

lemma boundFormula_correct {c : ℕ} (input : FirstOrder (c+1))
    (a : Fin c → ℝ) (v : Fin 1 → ℝ) (b : ℝ) :
    (boundFormula input).evalReal (Fin.cons b (Fin.addCases a v)) ↔
      b < v 0 ∧ ∀ l : ℝ,input.evalReal (Fin.cons l a) → l ≤ b := by
  simp only [boundFormula,FirstOrder.evalReal,Formula.evalReal,Expr.sub,Expr.evalReal,
    Fin.cons_zero,Fin.cons_succ,thresholdIndex,Fin.addCases_right,
    FirstOrder.renameVariables_correct,loss_assignment]
  simp only [← sub_eq_add_neg,sub_pos,sub_nonneg]
  exact and_congr Iff.rfl (forall_congr' fun l => by tauto)

/-- The actual three-step threshold construction: choose coefficients in memory, then a strict uniform bound. -/
def thresholdFormula {c : ℕ} (input : FirstOrder (c+1)) (memory : Formula c) : FirstOrder 1 :=
  FirstOrder.existsBlock c 1 (.conj (.atom (memory.renameVariables coefficientIndex))
    (.ex (boundFormula input)))

/-- Exact semantics of the constructed syntax, with no reference to an unknown optimal value. -/
theorem thresholdFormula_correct {c : ℕ} (input : FirstOrder (c+1)) (memory : Formula c)
    (v : Fin 1 → ℝ) :
    (thresholdFormula input memory).evalReal v ↔
      ∃ a : Fin c → ℝ,memory.evalReal a ∧
        ∃ b : ℝ,b < v 0 ∧ ∀ l : ℝ,input.evalReal (Fin.cons l a) → l ≤ b := by
  rw [thresholdFormula,FirstOrder.existsBlock_correct]
  simp only [FirstOrder.evalReal,Formula.renameVariables_correct,memory_assignment,
    boundFormula_correct]

/-- Independent attainable-loss model supplied by the finite input formula. -/
noncomputable def feasible {c : ℕ} (input : FirstOrder (c+1)) (_ : Unit)
    (a : Fin c → ℝ) (l : ℝ) : Prop := input.evalReal (Fin.cons l a)

def loss {c : ℕ} (_ : Unit) (_ : Fin c → ℝ) (l : ℝ) : ℝ := l

noncomputable def memory {c : ℕ} (memorySyntax : ℕ → Formula c) (m : ℕ) : Set (Fin c → ℝ) :=
  {a | (memorySyntax m).evalReal a}

/-- The executable first-order construction defines exactly the independently defined threshold set. -/
theorem thresholdFormula_mem {c : ℕ} (input : FirstOrder (c+1))
    (memorySyntax : ℕ → Formula c) (m : ℕ) (γ : ℝ) :
    (thresholdFormula input (memorySyntax m)).evalReal (fun _ => γ) ↔
      γ ∈ MemoryDecision.thresholds (feasible input) loss (memory memorySyntax) m := by
  rw [thresholdFormula_correct]
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    exact ⟨a,⟨(),b,hb,h⟩,ha⟩
  · rintro ⟨a,⟨u,b,hb,h⟩,ha⟩
    exact ⟨a,ha,b,hb,h⟩

/-- Correctness against the independent extended-real minimax value, including infinite risk. -/
theorem thresholdFormula_value {c : ℕ} (input : FirstOrder (c+1))
    (memorySyntax : ℕ → Formula c) (m : ℕ) (γ : ℝ) :
    (thresholdFormula input (memorySyntax m)).evalReal (fun _ => γ) ↔
      MemoryDecision.value (feasible input) loss (memory memorySyntax) m < (γ : EReal) := by
  rw [thresholdFormula_mem,MemoryDecision.threshold_iff_value_lt]

end MemorySemialgebraic.SymbolicQE.ProcedureSyntax
