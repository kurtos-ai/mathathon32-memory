module
public import Continuation.Semialgebraic.SymbolicSignElimination
public import Continuation.Semialgebraic.SymbolicSignDNF
public import Continuation.Semialgebraic.FirstOrder
public meta import Continuation.Semialgebraic.SymbolicSignElimination
public meta import Continuation.Semialgebraic.SymbolicSignDNF
public meta import Continuation.Semialgebraic.FirstOrder

/-!
# Effective real quantifier elimination

The one-variable step expands arbitrary Boolean polynomial conditions into sign
clauses, compiles the head variable to symbolic coefficient lists, and eliminates
each sign clause using finite Tarski queries and BKR inversion. Structural lifting
then handles arbitrary first-order quantifier alternation. Every runtime output
is explicit rational quantifier-free syntax; all real interpretations occur only
in specifications and erased proofs.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Polynomial SignType

namespace Formula

def eliminateClause {n : ℕ} (c : List (Expr (n+1) × SignType)) : Formula n :=
  SymbolicPoly.eliminateSignCondition
    (fun j : Fin c.length => (c.get j).1.compileHead)
    (fun j : Fin c.length => (c.get j).2)

theorem eliminateClause_correct {n : ℕ} (c : List (Expr (n+1) × SignType))
    (v : Fin n → ℝ) :
    (eliminateClause c).evalReal v ↔
      ∃ x : ℝ, ∀ es ∈ c, sign (es.1.evalReal (Fin.cons x v)) = es.2 := by
  rw [eliminateClause, SymbolicPoly.eliminateSignCondition_correct]
  apply exists_congr
  intro x
  have he (e : Expr (n+1)) : (SymbolicPoly.denote v e.compileHead).eval x =
      e.evalReal (Fin.cons x v) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using Expr.compileHead_correct e v x
  simp only [he]
  exact (List.forall_mem_iff_get (l := c)
    (p := fun es => sign (es.1.evalReal (Fin.cons x v)) = es.2)).symm

/-- Eliminate one existential head variable from an arbitrary rational polynomial formula. -/
def eliminateExists {n : ℕ} (f : Formula (n+1)) : Formula n :=
  Formula.any (f.toSignDNF.map eliminateClause)

theorem eliminateExists_correct {n : ℕ} (f : Formula (n+1)) (v : Fin n → ℝ) :
    (eliminateExists f).evalReal v ↔ ∃ x : ℝ, f.evalReal (Fin.cons x v) := by
  rw [eliminateExists, Formula.any_eval]
  simp only [List.mem_map, exists_exists_and_eq_and]
  simp_rw [eliminateClause_correct]
  simp_rw [Formula.toSignDNF_correct]
  constructor
  · rintro ⟨c, hc, x, hx⟩
    exact ⟨x, c, hc, hx⟩
  · rintro ⟨x, c, hc, hx⟩
    exact ⟨c, hc, x, hx⟩

end Formula

namespace FirstOrder

/-- Executable quantifier elimination for arbitrary rational first-order formulas over ℝ. -/
def quantifierEliminate {n : ℕ} (f : FirstOrder n) : Formula n :=
  eliminate Formula.eliminateExists f

theorem quantifierEliminate_correct {n : ℕ} (f : FirstOrder n) (v : Fin n → ℝ) :
    (quantifierEliminate f).evalReal v ↔ f.evalReal v :=
  eliminate_correct Formula.eliminateExists Formula.eliminateExists_correct f v

theorem quantifierEliminate_toQF {n : ℕ} (f : FirstOrder n) (v : Fin n → ℝ) :
    (quantifierEliminate f).toQF.eval v ↔ f.evalReal v := by
  rw [Formula.toQF_refines, quantifierEliminate_correct]

/-- Closed sentences are decided by evaluating the generated rational formula. -/
def decideSentence (f : FirstOrder 0) : Bool :=
  (quantifierEliminate f).evalRat Fin.elim0

theorem decideSentence_correct (f : FirstOrder 0) :
    decideSentence f = true ↔ f.evalReal Fin.elim0 := by
  rw [decideSentence, Formula.evalRat_refines, quantifierEliminate_correct]
  have hv : (fun i : Fin 0 => ((Fin.elim0 i : ℚ) : ℝ)) = (Fin.elim0 : Fin 0 → ℝ) := by
    funext i
    exact Fin.elim0 i
  rw [hv]

end FirstOrder
end MemorySemialgebraic.SymbolicQE
