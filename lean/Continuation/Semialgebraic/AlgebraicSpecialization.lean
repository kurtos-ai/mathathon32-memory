module
public import Continuation.Semialgebraic.AlgebraicParameters
public import Continuation.Semialgebraic.FirstOrderRename
public meta import Continuation.Semialgebraic.AlgebraicParameters
public meta import Continuation.Semialgebraic.FirstOrderRename

@[expose] public section
namespace MemorySemialgebraic.AlgebraicParameters
open SymbolicQE

/-- Bind finitely specified algebraic parameters at the front of a rational formula.
The executable construction uses only rational code constraints and existential syntax. -/
def specializePrefix {k n : ℕ} (cs : Fin k → Code) (f : FirstOrder (k+n)) : FirstOrder n :=
  FirstOrder.existsBlock k n (.conj (.atom (constraints cs)) f)

theorem specializePrefix_correct {k n : ℕ} (cs : Fin k → Code)
    (f : FirstOrder (k+n)) (v : Fin n → ℝ) :
    (specializePrefix cs f).evalReal v ↔
      f.evalReal (Fin.addCases (fun i => (cs i).value) v) := by
  rw [specializePrefix,FirstOrder.existsBlock_correct]
  change (∃ a : Fin k → ℝ,
    Formula.evalReal (Fin.addCases a v) (constraints cs) ∧ f.evalReal (Fin.addCases a v)) ↔ _
  simp only [constraints_exact,Fin.addCases_left]
  constructor
  · rintro ⟨a,ha,hf⟩
    have he : a = fun i => (cs i).value := funext ha
    simpa only [he] using hf
  · intro hf
    exact ⟨fun i => (cs i).value,fun _ => rfl,hf⟩

/-- Move the two parameters in `[loss,L,R,a]` to the front, giving `[L,R,loss,a]`. -/
def twoParameterOrder {c : ℕ} : Fin (c+3) → Fin (2+(c+1)) :=
  Fin.cases (Fin.natAdd 2 (0 : Fin (c+1)))
    (Fin.cases (Fin.castAdd (c+1) (0 : Fin 2))
      (Fin.cases (Fin.castAdd (c+1) (1 : Fin 2)) (fun i => Fin.natAdd 2 i.succ)))

lemma twoParameterOrder_assignment {c : ℕ} (b : Fin 2 → ℝ) (l : ℝ) (a : Fin c → ℝ) :
    (Fin.addCases b (Fin.cons l a)) ∘ twoParameterOrder =
      Fin.cons l (Fin.cons (b 0) (Fin.cons (b 1) a)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply,twoParameterOrder,Fin.cases_zero,
        Fin.addCases_right,Fin.cons_zero]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply,twoParameterOrder,Fin.cases_zero,Fin.cases_succ,
        Fin.addCases_left,Fin.cons_zero,Fin.cons_succ]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Function.comp_apply,twoParameterOrder,Fin.cases_zero,Fin.cases_succ,
        Fin.addCases_left,Fin.cons_zero,Fin.cons_succ]
      · simp only [Function.comp_apply,twoParameterOrder,Fin.cases_succ,
        Fin.addCases_right,Fin.cons_succ]

def twoCodes (L R : Code) : Fin 2 → Code := Fin.cons L (Fin.cons R Fin.elim0)

/-- Specialize `[loss,L,R,a]` to two finite algebraic input codes, retaining `[loss,a]`. -/
def specializeTwoParameters {c : ℕ} (L R : Code) (f : FirstOrder (c+3)) : FirstOrder (c+1) :=
  specializePrefix (twoCodes L R) (f.renameVariables twoParameterOrder)

theorem specializeTwoParameters_correct {c : ℕ} (L R : Code)
    (f : FirstOrder (c+3)) (l : ℝ) (a : Fin c → ℝ) :
    (specializeTwoParameters L R f).evalReal (Fin.cons l a) ↔
      f.evalReal (Fin.cons l (Fin.cons L.value (Fin.cons R.value a))) := by
  rw [specializeTwoParameters,specializePrefix_correct,FirstOrder.renameVariables_correct,
    twoParameterOrder_assignment]
  rfl

end MemorySemialgebraic.AlgebraicParameters
