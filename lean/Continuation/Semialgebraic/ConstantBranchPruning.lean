module
public import Continuation.Semialgebraic.SignBranching
public meta import Continuation.Semialgebraic.SignBranching

/-! # Verified constant-branch pruning

Before combining independent symbolic sign trees, branches whose polynomial
expression is syntactically constant are evaluated. This preserves every real
parameter specialization and avoids multiplying irrelevant constant cases.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
variable {n : ℕ}

namespace Expr
def constantValue : Expr n → Option ℚ
  | .constant c => some c
  | .variable _ => none
  | .add p q => do return (← constantValue p) + (← constantValue q)
  | .neg p => do return -(← constantValue p)
  | .mul p q => do return (← constantValue p) * (← constantValue q)

theorem constantValue_correct (v : Fin n → ℝ) (e : Expr n) (c : ℚ)
    (h : e.constantValue = some c) : e.evalReal v = (c : ℝ) := by
  induction e generalizing c with
  | constant a =>
    have he : a = c := Option.some.inj h
    subst c
    rfl
  | «variable» i => simp [constantValue] at h
  | add p q hp hq =>
    cases hc : p.constantValue <;> cases hd : q.constantValue <;>
      simp_all [-evalReal_refines, constantValue, evalReal]
    exact_mod_cast h
  | neg p hp =>
    cases hc : p.constantValue <;> simp_all [-evalReal_refines, constantValue, evalReal]
    exact_mod_cast h
  | mul p q hp hq =>
    cases hc : p.constantValue <;> cases hd : q.constantValue <;>
      simp_all [-evalReal_refines, constantValue, evalReal]
    exact_mod_cast h
end Expr

namespace SignTree
def pruneConstants {α : Type} : SignTree n α → SignTree n α
  | .leaf a => .leaf a
  | .branch e lo eq hi =>
    match e.constantValue with
    | none => .branch e (pruneConstants lo) (pruneConstants eq) (pruneConstants hi)
    | some c => if c < 0 then pruneConstants lo else if c = 0 then pruneConstants eq else pruneConstants hi

@[simp] theorem pruneConstants_correct {α : Type} (v : Fin n → ℝ) (t : SignTree n α) :
    (pruneConstants t).evalReal v = t.evalReal v := by
  induction t with
  | leaf a => rfl
  | branch e lo eq hi hlo heq hhi =>
    cases hc : e.constantValue with
    | none => simp only [pruneConstants, hc, evalReal, hlo, heq, hhi]
    | some c =>
      have he := Expr.constantValue_correct v e c hc
      simp only [pruneConstants, hc, evalReal, he, Rat.cast_lt_zero, Rat.cast_eq_zero]
      split <;> simp_all
      split <;> simp_all

end SignTree
end MemorySemialgebraic.SymbolicQE
