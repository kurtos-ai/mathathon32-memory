module
public import Continuation.Semialgebraic.SymbolicAffineQE
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE

/-- First-order formulas over rational polynomial atoms. A binder introduces the
head coordinate; old coordinates are shifted by `Fin.succ`. -/
inductive FirstOrder : ℕ → Type where
  | atom {n : ℕ} : Formula n → FirstOrder n
  | conj {n : ℕ} : FirstOrder n → FirstOrder n → FirstOrder n
  | disj {n : ℕ} : FirstOrder n → FirstOrder n → FirstOrder n
  | neg {n : ℕ} : FirstOrder n → FirstOrder n
  | ex {n : ℕ} : FirstOrder (n+1) → FirstOrder n
  | all {n : ℕ} : FirstOrder (n+1) → FirstOrder n
  deriving Repr

namespace FirstOrder

noncomputable def evalReal {n : ℕ} (v : Fin n → ℝ) : FirstOrder n → Prop
  | .atom f => f.evalReal v
  | .conj f g => evalReal v f ∧ evalReal v g
  | .disj f g => evalReal v f ∨ evalReal v g
  | .neg f => ¬ evalReal v f
  | .ex f => ∃ x : ℝ, evalReal (Fin.cons x v) f
  | .all f => ∀ x : ℝ, evalReal (Fin.cons x v) f

/-- Structural lifting of one-variable elimination. The supplied step is an
explicit algorithm, whose correctness is required separately below. -/
def eliminate (step : {n : ℕ} → Formula (n+1) → Formula n) :
    {n : ℕ} → FirstOrder n → Formula n
  | _, .atom f => f
  | _, .conj f g => .conj (eliminate step f) (eliminate step g)
  | _, .disj f g => .disj (eliminate step f) (eliminate step g)
  | _, .neg f => .neg (eliminate step f)
  | _, .ex f => step (eliminate step f)
  | _, .all f => .neg (step (.neg (eliminate step f)))

/-- A correct one-variable elimination algorithm handles arbitrary quantifier
alternation by the displayed structural recursion. -/
theorem eliminate_correct
    (step : {n : ℕ} → Formula (n+1) → Formula n)
    (hstep : ∀ {n : ℕ} (f : Formula (n+1)) (v : Fin n → ℝ),
      (step f).evalReal v ↔ ∃ x : ℝ, f.evalReal (Fin.cons x v))
    {n : ℕ} (f : FirstOrder n) (v : Fin n → ℝ) :
    (eliminate step f).evalReal v ↔ evalReal v f := by
  induction f with
  | atom f => rfl
  | conj f g ihf ihg => exact and_congr (ihf v) (ihg v)
  | disj f g ihf ihg => exact or_congr (ihf v) (ihg v)
  | neg f ih => exact not_congr (ih v)
  | ex f ih =>
    change (step (eliminate step f)).evalReal v ↔ ∃ x, evalReal (Fin.cons x v) f
    rw [hstep]
    exact exists_congr (fun x => ih (Fin.cons x v))
  | all f ih =>
    change (¬ (step (.neg (eliminate step f))).evalReal v) ↔ ∀ x, evalReal (Fin.cons x v) f
    rw [hstep]
    simp only [Formula.evalReal,not_exists,not_not]
    exact forall_congr' (fun x => ih (Fin.cons x v))

end FirstOrder
end MemorySemialgebraic.SymbolicQE
