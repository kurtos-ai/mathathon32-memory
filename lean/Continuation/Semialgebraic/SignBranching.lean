module
public import Continuation.Semialgebraic.SymbolicAffineQE
public meta import Continuation.Semialgebraic.SymbolicAffineQE

/-!
# Finite symbolic sign branching

A finite decision tree branches on signs of rational polynomial expressions in the
parameters. Its leaves may contain arbitrary executable data. Compiling a Boolean
predicate on the leaves produces an explicit quantifier-free formula, with exact
semantics over every real parameter tuple. This is infrastructure for parameterized
pseudo-remainder computations, not an assumption of quantifier elimination.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE

inductive SignTree (n : ℕ) (α : Type) where
  | leaf : α → SignTree n α
  | branch : Expr n → SignTree n α → SignTree n α → SignTree n α → SignTree n α
  deriving Repr

namespace SignTree
variable {n : ℕ} {α β : Type}

def evalRat (v : Fin n → ℚ) : SignTree n α → α
  | .leaf a => a
  | .branch p lo eq hi =>
    if p.evalRat v < 0 then evalRat v lo
    else if p.evalRat v = 0 then evalRat v eq else evalRat v hi

noncomputable def evalReal (v : Fin n → ℝ) : SignTree n α → α
  | .leaf a => a
  | .branch p lo eq hi =>
    if p.evalReal v < 0 then evalReal v lo
    else if p.evalReal v = 0 then evalReal v eq else evalReal v hi

@[simp] theorem evalReal_cast (v : Fin n → ℚ) (t : SignTree n α) :
    evalReal (fun i => (v i : ℝ)) t = evalRat v t := by
  induction t <;> simp_all only [evalReal, evalRat, Expr.evalReal_cast,
    Rat.cast_lt_zero, Rat.cast_eq_zero]

def bind : SignTree n α → (α → SignTree n β) → SignTree n β
  | .leaf a, f => f a
  | .branch p lo eq hi, f => .branch p (bind lo f) (bind eq f) (bind hi f)

def map (f : α → β) (t : SignTree n α) : SignTree n β := bind t (.leaf ∘ f)

@[simp] theorem evalReal_bind (v : Fin n → ℝ) (t : SignTree n α)
    (f : α → SignTree n β) : evalReal v (bind t f) = evalReal v (f (evalReal v t)) := by
  induction t <;> simp_all only [bind, evalReal]
  split <;> simp_all
  split <;> simp_all

@[simp] theorem evalReal_map (v : Fin n → ℝ) (f : α → β) (t : SignTree n α) :
    evalReal v (map f t) = f (evalReal v t) := by simp [map, Function.comp_def, evalReal]

/-- Compile an arbitrary leaf predicate to rational quantifier-free syntax. -/
def toFormula (test : α → Bool) : SignTree n α → Formula n
  | .leaf a => if test a then .tru else .fls
  | .branch p lo eq hi =>
    .disj (.conj (.positive (.neg p)) (toFormula test lo))
      (.disj (.conj (.eqZero p) (toFormula test eq))
        (.conj (.positive p) (toFormula test hi)))

theorem toFormula_correct (v : Fin n → ℝ) (test : α → Bool) (t : SignTree n α) :
    (toFormula test t).evalReal v ↔ test (evalReal v t) = true := by
  induction t with
  | leaf a => cases h : test a <;> simp [toFormula, h, Formula.evalReal, evalReal]
  | branch p lo eq hi hlo heq hhi =>
    simp only [toFormula, Formula.evalReal, Expr.evalReal, hlo, heq, hhi, evalReal,
      neg_pos]
    rcases lt_trichotomy (p.evalReal v) 0 with h | h | h
    · simp [-Expr.evalReal_refines, h, ne_of_lt h, not_lt_of_gt h]
    · simp [-Expr.evalReal_refines, h]
    · simp [-Expr.evalReal_refines, h, ne_of_gt h, not_lt_of_gt h]

end SignTree

/-- Branch on the first nonzero coefficient; the zero branch removes one coefficient. -/
def normalizeCoeffs {n : ℕ} : List (Expr n) → SignTree n (List (Expr n))
  | [] => .leaf []
  | a :: p => .branch a (.leaf (a :: p)) (normalizeCoeffs p) (.leaf (a :: p))

theorem normalizeCoeffs_length {n : ℕ} (v : Fin n → ℝ) (p : List (Expr n)) :
    ((normalizeCoeffs p).evalReal v).length ≤ p.length := by
  induction p with
  | nil => simp [normalizeCoeffs, SignTree.evalReal]
  | cons a p ih =>
    simp only [normalizeCoeffs, SignTree.evalReal]
    split
    · simp
    · split
      · exact ih.trans (Nat.le_succ _)
      · simp

theorem normalizeCoeffs_head_ne_zero {n : ℕ} (v : Fin n → ℝ) (p : List (Expr n)) :
    ∀ a q, (normalizeCoeffs p).evalReal v = a :: q → a.evalReal v ≠ 0 := by
  induction p with
  | nil => simp [normalizeCoeffs, SignTree.evalReal]
  | cons b p ih =>
    simp only [normalizeCoeffs, SignTree.evalReal]
    split
    · rename_i hb
      intro a q h
      cases h
      exact ne_of_lt hb
    · split
      · exact ih
      · rename_i hb
        intro a q h
        cases h
        exact hb

/-- info: [1, 0, 1] -/
#guard_msgs in
#eval ([-2, 0, 3] : List ℚ).map fun y =>
  ((normalizeCoeffs [Expr.variable (0 : Fin 1)]).evalRat (fun _ => y)).length

/-- info: [true, false, true] -/
#guard_msgs in
#eval ([-2, 0, 3] : List ℚ).map fun y =>
  ((normalizeCoeffs [Expr.variable (0 : Fin 1)]).toFormula
    (fun p => !p.isEmpty)).evalRat (fun _ => y)

end MemorySemialgebraic.SymbolicQE
