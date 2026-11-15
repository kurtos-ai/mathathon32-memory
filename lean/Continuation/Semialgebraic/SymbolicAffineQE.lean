module
public import Continuation.Semialgebraic.AffineElimination
public import Continuation.Semialgebraic.Endpoints

/-!
# Executable symbolic elimination of one affine variable

The input coefficients are arbitrary rational polynomial expressions in the remaining variables.
The output is an explicit quantifier-free formula built by finite list and syntax operations.
Its interpretation is proved equivalent to the quantified input for every real parameter tuple.
This is restricted to inputs affine in the eliminated variable; it is not general nonlinear QE.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open AffineElimination

/-- A computable syntax covering arbitrary rational multivariate polynomials. -/
inductive Expr (n : ℕ) where
  | constant : ℚ → Expr n
  | variable : Fin n → Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

namespace Expr

def sub {n : ℕ} (p q : Expr n) : Expr n := .add p (.neg q)

noncomputable def denote {n : ℕ} : Expr n → MvPolynomial (Fin n) ℚ
  | .constant q => MvPolynomial.C q
  | .variable i => MvPolynomial.X i
  | .add p q => denote p + denote q
  | .neg p => -denote p
  | .mul p q => denote p * denote q

noncomputable def evalReal {n : ℕ} (v : Fin n → ℝ) : Expr n → ℝ
  | .constant q => (q : ℝ)
  | .variable i => v i
  | .add p q => evalReal v p + evalReal v q
  | .neg p => -evalReal v p
  | .mul p q => evalReal v p * evalReal v q

def evalRat {n : ℕ} (v : Fin n → ℚ) : Expr n → ℚ
  | .constant q => q
  | .variable i => v i
  | .add p q => evalRat v p + evalRat v q
  | .neg p => -evalRat v p
  | .mul p q => evalRat v p * evalRat v q

@[simp] theorem evalReal_refines {n : ℕ} (v : Fin n → ℝ) (p : Expr n) :
    evalReal v p = evalPolyQ (denote p) v := by
  induction p <;> simp_all [evalReal, denote, evalPolyQ]

@[simp] theorem evalReal_cast {n : ℕ} (v : Fin n → ℚ) (p : Expr n) :
    evalReal (fun i => (v i : ℝ)) p = (evalRat v p : ℝ) := by
  induction p <;> simp_all [evalReal, evalRat]

/-- Every rational multivariate polynomial is represented by the runtime syntax. -/
theorem denote_surjective (n : ℕ) : Function.Surjective (denote (n := n)) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨.constant c, rfl⟩
  | add p q hp hq =>
    obtain ⟨ep, rfl⟩ := hp
    obtain ⟨eq, rfl⟩ := hq
    exact ⟨.add ep eq, rfl⟩
  | mul_X p i hp =>
    obtain ⟨ep, rfl⟩ := hp
    exact ⟨.mul ep (.variable i), rfl⟩

end Expr

/-- Executable quantifier-free formula syntax, with positive-facing atomic comparisons. -/
inductive Formula (n : ℕ) where
  | eqZero : Expr n → Formula n
  | positive : Expr n → Formula n
  | nonnegative : Expr n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n
  | neg : Formula n → Formula n
  | tru : Formula n
  | fls : Formula n
  deriving DecidableEq, Repr

namespace Formula

noncomputable def evalReal {n : ℕ} (v : Fin n → ℝ) : Formula n → Prop
  | .eqZero p => Expr.evalReal v p = 0
  | .positive p => 0 < Expr.evalReal v p
  | .nonnegative p => 0 ≤ Expr.evalReal v p
  | .conj f g => evalReal v f ∧ evalReal v g
  | .disj f g => evalReal v f ∨ evalReal v g
  | .neg f => ¬evalReal v f
  | .tru => True
  | .fls => False

def evalRat {n : ℕ} (v : Fin n → ℚ) : Formula n → Bool
  | .eqZero p => decide (Expr.evalRat v p = 0)
  | .positive p => decide (0 < Expr.evalRat v p)
  | .nonnegative p => decide (0 ≤ Expr.evalRat v p)
  | .conj f g => evalRat v f && evalRat v g
  | .disj f g => evalRat v f || evalRat v g
  | .neg f => !evalRat v f
  | .tru => true
  | .fls => false

/-- Interpret the runtime output in the existing semialgebraic formula language. -/
noncomputable def toQF {n : ℕ} : Formula n → QFFormula n
  | .eqZero p => .atomEq p.denote
  | .positive p => .atomLt (-p.denote)
  | .nonnegative p => .atomLe (-p.denote)
  | .conj f g => .and (toQF f) (toQF g)
  | .disj f g => .or (toQF f) (toQF g)
  | .neg f => .not (toQF f)
  | .tru => .tru
  | .fls => .fls

@[simp] theorem toQF_refines {n : ℕ} (v : Fin n → ℝ) (f : Formula n) :
    (toQF f).eval v ↔ evalReal v f := by
  induction f <;> simp_all [toQF, QFFormula.eval, evalReal, evalPolyQ]

@[simp] theorem evalRat_refines {n : ℕ} (v : Fin n → ℚ) (f : Formula n) :
    evalRat v f = true ↔ evalReal (fun i => (v i : ℝ)) f := by
  induction f <;> simp_all [-Expr.evalReal_refines, evalRat, evalReal, Bool.eq_false_iff]

def relation {n : ℕ} (strict : Bool) (p : Expr n) : Formula n :=
  if strict then .positive p else .nonnegative p

@[simp] theorem relation_eval {n : ℕ} (v : Fin n → ℝ) (strict : Bool) (p : Expr n) :
    evalReal v (relation strict p) ↔ Rel strict 0 (Expr.evalReal v p) := by
  cases strict <;> rfl

def all {n : ℕ} : List (Formula n) → Formula n
  | [] => .tru
  | f :: fs => .conj f (all fs)

@[simp] theorem all_eval {n : ℕ} (v : Fin n → ℝ) (fs : List (Formula n)) :
    evalReal v (all fs) ↔ ∀ f ∈ fs, evalReal v f := by
  induction fs <;> simp_all [all, evalReal]

def any {n : ℕ} : List (Formula n) → Formula n
  | [] => .fls
  | f :: fs => .disj f (any fs)

@[simp] theorem any_eval {n : ℕ} (v : Fin n → ℝ) (fs : List (Formula n)) :
    evalReal v (any fs) ↔ ∃ f ∈ fs, evalReal v f := by
  induction fs <;> simp_all [any, evalReal]

end Formula

/-- The atom is `a(parameters) * x + b(parameters) ≥ 0`, or `> 0` when strict. -/
structure Constraint (n : ℕ) where
  a : Expr n
  b : Expr n
  strict : Bool
  deriving DecidableEq, Repr

namespace Constraint

noncomputable def holds {n : ℕ} (v : Fin n → ℝ) (x : ℝ) (c : Constraint n) : Prop :=
  Rel c.strict 0 (Expr.evalReal v c.a * x + Expr.evalReal v c.b)

/-- When the eliminated variable's coefficient vanishes, the constant constraint must hold. -/
def constantCondition {n : ℕ} (c : Constraint n) : Formula n :=
  .disj (.neg (.eqZero c.a)) (Formula.relation c.strict c.b)

/-- Opposing constraints produce a polynomial comparison in the remaining parameters. -/
def pairCondition {n : ℕ} (c d : Constraint n) : Formula n :=
  .disj (.neg (.conj (.positive c.a) (.positive (.neg d.a))))
    (Formula.relation (c.strict || d.strict) (.sub (.mul d.b c.a) (.mul c.b d.a)))

@[simp] theorem constantCondition_eval {n : ℕ} (v : Fin n → ℝ) (c : Constraint n) :
    Formula.evalReal v (constantCondition c) ↔
      (Expr.evalReal v c.a = 0 → Rel c.strict 0 (Expr.evalReal v c.b)) := by
  classical
  simp [constantCondition, Formula.evalReal, ← imp_iff_not_or]

@[simp] theorem pairCondition_eval {n : ℕ} (v : Fin n → ℝ) (c d : Constraint n) :
    Formula.evalReal v (pairCondition c d) ↔
      (0 < Expr.evalReal v c.a → Expr.evalReal v d.a < 0 →
        Rel (c.strict || d.strict)
          (Expr.evalReal v c.b * Expr.evalReal v d.a)
          (Expr.evalReal v d.b * Expr.evalReal v c.a)) := by
  classical
  simp only [pairCondition, Formula.evalReal, Formula.relation_eval, Expr.sub,
    Expr.evalReal, neg_pos, ← imp_iff_not_or, and_imp, ← sub_eq_add_neg]
  rw [← rel_sub]

end Constraint

/-- Actual symbolic elimination: all constant conditions and all opposing pairs. -/
def eliminateConjunction {n : ℕ} (cs : List (Constraint n)) : Formula n :=
  .conj (Formula.all (cs.map Constraint.constantCondition))
    (Formula.all (cs.flatMap (fun c => cs.map (Constraint.pairCondition c))))

/-- No sign information about the parameters is assumed: the output formula itself expresses
all coefficient-sign branches and cross-multiplied pair inequalities. -/
theorem eliminateConjunction_correct {n : ℕ} (v : Fin n → ℝ) (cs : List (Constraint n)) :
    Formula.evalReal v (eliminateConjunction cs) ↔ ∃ x : ℝ, ∀ c ∈ cs, c.holds v x := by
  have h := AffineElimination.feasible_iff cs.toFinset
    (fun c => Expr.evalReal v c.a) (fun c => Expr.evalReal v c.b) Constraint.strict
  simp only [List.mem_toFinset] at h
  refine Iff.trans ?_ h.symm
  simp only [eliminateConjunction, Formula.evalReal, Formula.all_eval,
    List.forall_mem_map, List.forall_mem_flatMap, Constraint.constantCondition_eval,
    Constraint.pairCondition_eval]

/-- A bridge directly to the existing quantifier-free semialgebraic development. -/
theorem eliminateConjunction_toQF {n : ℕ} (v : Fin n → ℝ) (cs : List (Constraint n)) :
    (Formula.toQF (eliminateConjunction cs)).eval v ↔ ∃ x : ℝ, ∀ c ∈ cs, c.holds v x := by
  rw [Formula.toQF_refines]
  exact eliminateConjunction_correct v cs

/-- Elimination of a disjunction of affine conjunctions, with arbitrary Boolean branching
represented by its explicit disjunctive normal form. -/
def eliminateDNF {n : ℕ} (clauses : List (List (Constraint n))) : Formula n :=
  Formula.any (clauses.map eliminateConjunction)

theorem eliminateDNF_correct {n : ℕ} (v : Fin n → ℝ) (clauses : List (List (Constraint n))) :
    Formula.evalReal v (eliminateDNF clauses) ↔
      ∃ x : ℝ, ∃ cs ∈ clauses, ∀ c ∈ cs, c.holds v x := by
  simp only [eliminateDNF, Formula.any_eval, List.mem_map, exists_exists_and_eq_and,
    eliminateConjunction_correct]
  constructor
  · rintro ⟨cs, hcs, x, hx⟩
    exact ⟨x, cs, hcs, hx⟩
  · rintro ⟨x, cs, hcs, hx⟩
    exact ⟨cs, hcs, x, hx⟩

/-- Negating an affine inequality swaps strictness and negates its coefficients. -/
def negateConstraint {n : ℕ} (c : Constraint n) : Constraint n :=
  ⟨.neg c.a, .neg c.b, !c.strict⟩

@[simp] theorem negateConstraint_holds {n : ℕ} (v : Fin n → ℝ) (x : ℝ)
    (c : Constraint n) : (negateConstraint c).holds v x ↔ ¬c.holds v x := by
  cases hs : c.strict with
  | false =>
    simp only [Constraint.holds, negateConstraint, hs, Expr.evalReal]
    change (0 < -Expr.evalReal v c.a * x + -Expr.evalReal v c.b) ↔
      ¬(0 ≤ Expr.evalReal v c.a * x + Expr.evalReal v c.b)
    constructor <;> intro h <;> linarith
  | true =>
    simp only [Constraint.holds, negateConstraint, hs, Expr.evalReal]
    change (0 ≤ -Expr.evalReal v c.a * x + -Expr.evalReal v c.b) ↔
      ¬(0 < Expr.evalReal v c.a * x + Expr.evalReal v c.b)
    constructor <;> intro h <;> linarith

/-- An arbitrary Boolean combination of inequalities affine in the eliminated variable. -/
inductive AffineFormula (n : ℕ) where
  | atom : Constraint n → AffineFormula n
  | conj : AffineFormula n → AffineFormula n → AffineFormula n
  | disj : AffineFormula n → AffineFormula n → AffineFormula n
  | neg : AffineFormula n → AffineFormula n
  | tru : AffineFormula n
  | fls : AffineFormula n
  deriving DecidableEq, Repr

namespace AffineFormula

noncomputable def evalReal {n : ℕ} (v : Fin n → ℝ) (x : ℝ) : AffineFormula n → Prop
  | .atom c => c.holds v x
  | .conj f g => evalReal v x f ∧ evalReal v x g
  | .disj f g => evalReal v x f ∨ evalReal v x g
  | .neg f => ¬evalReal v x f
  | .tru => True
  | .fls => False

/-- Equality is the conjunction of two weak inequalities. -/
def equalZero {n : ℕ} (a b : Expr n) : AffineFormula n :=
  .conj (.atom ⟨a, b, false⟩) (.atom ⟨.neg a, .neg b, false⟩)

@[simp] theorem equalZero_eval {n : ℕ} (v : Fin n → ℝ) (x : ℝ) (a b : Expr n) :
    evalReal v x (equalZero a b) ↔ Expr.evalReal v a * x + Expr.evalReal v b = 0 := by
  simp only [equalZero, evalReal, Constraint.holds, AffineElimination.Rel, Bool.false_eq_true, ↓reduceIte,
    Expr.evalReal]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · intro h
    constructor <;> linarith

end AffineFormula

/-- Semantics of an explicit disjunctive normal form. -/
noncomputable def clausesHold {n : ℕ} (v : Fin n → ℝ) (x : ℝ)
    (clauses : List (List (Constraint n))) : Prop :=
  ∃ cs ∈ clauses, ∀ c ∈ cs, c.holds v x

@[simp] theorem clausesHold_nil {n : ℕ} (v : Fin n → ℝ) (x : ℝ) :
    ¬clausesHold v x ([] : List (List (Constraint n))) := by
  simp [clausesHold]

@[simp] theorem clausesHold_singleton {n : ℕ} (v : Fin n → ℝ) (x : ℝ)
    (cs : List (Constraint n)) : clausesHold v x [cs] ↔ ∀ c ∈ cs, c.holds v x := by
  simp [clausesHold]

@[simp] theorem clausesHold_append {n : ℕ} (v : Fin n → ℝ) (x : ℝ)
    (a b : List (List (Constraint n))) :
    clausesHold v x (a ++ b) ↔ clausesHold v x a ∨ clausesHold v x b := by
  simp [clausesHold, or_and_right, exists_or]

/-- Distributive product of DNF clauses. -/
def meetClauses {n : ℕ} (a b : List (List (Constraint n))) : List (List (Constraint n)) :=
  a.flatMap (fun ca => b.map (ca ++ ·))

@[simp] theorem meetClauses_correct {n : ℕ} (v : Fin n → ℝ) (x : ℝ)
    (a b : List (List (Constraint n))) :
    clausesHold v x (meetClauses a b) ↔ clausesHold v x a ∧ clausesHold v x b := by
  constructor
  · rintro ⟨cs, hcs, h⟩
    obtain ⟨ca, hca, hcs⟩ := List.mem_flatMap.mp hcs
    obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hcs
    exact ⟨⟨ca, hca, fun c hc => h c (List.mem_append_left cb hc)⟩,
      ⟨cb, hcb, fun c hc => h c (List.mem_append_right ca hc)⟩⟩
  · rintro ⟨⟨ca, hca, ha⟩, ⟨cb, hcb, hb⟩⟩
    refine ⟨ca ++ cb, List.mem_flatMap.mpr ⟨ca, hca, List.mem_map.mpr ⟨cb, hcb, rfl⟩⟩, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ha c hc
    · exact hb c hc

/-- Polarity-passing Boolean normalization. Negation is eliminated constructively from syntax;
the runtime procedure does not inspect real numbers. -/
def toDNF {n : ℕ} (polarity : Bool) : AffineFormula n → List (List (Constraint n))
  | .atom c => [[if polarity then c else negateConstraint c]]
  | .conj f g => if polarity then meetClauses (toDNF true f) (toDNF true g)
      else toDNF false f ++ toDNF false g
  | .disj f g => if polarity then toDNF true f ++ toDNF true g
      else meetClauses (toDNF false f) (toDNF false g)
  | .neg f => toDNF (!polarity) f
  | .tru => if polarity then [[]] else []
  | .fls => if polarity then [] else [[]]

theorem toDNF_correct {n : ℕ} (v : Fin n → ℝ) (x : ℝ) (polarity : Bool)
    (f : AffineFormula n) : clausesHold v x (toDNF polarity f) ↔
      if polarity then AffineFormula.evalReal v x f else ¬AffineFormula.evalReal v x f := by
  classical
  induction f generalizing polarity <;> cases polarity <;>
    simp_all [toDNF, AffineFormula.evalReal, ← imp_iff_not_or]

/-- Executable symbolic existential elimination for arbitrary Boolean affine formulas. -/
def eliminate {n : ℕ} (f : AffineFormula n) : Formula n := eliminateDNF (toDNF true f)

/-- Exact quantifier elimination for this restricted input class, with no hypotheses on the
values or degrees of the polynomial coefficient expressions in the remaining parameters. -/
theorem eliminate_correct {n : ℕ} (v : Fin n → ℝ) (f : AffineFormula n) :
    Formula.evalReal v (eliminate f) ↔ ∃ x : ℝ, AffineFormula.evalReal v x f := by
  rw [eliminate, eliminateDNF_correct]
  exact exists_congr (fun x => toDNF_correct v x true f)

theorem eliminate_toQF {n : ℕ} (v : Fin n → ℝ) (f : AffineFormula n) :
    (Formula.toQF (eliminate f)).eval v ↔ ∃ x : ℝ, AffineFormula.evalReal v x f := by
  rw [Formula.toQF_refines]
  exact eliminate_correct v f

-- Execution checks cover changing coefficient signs and weak/strict projection boundaries.
/-- info: [false, false, true] -/
#guard_msgs in
#eval
  let y : Expr 1 := .variable 0
  let cs : List (Constraint 1) := [⟨.constant 1, .constant 0, true⟩,
    ⟨y, .constant (-1), false⟩]
  ([-2, 0, 2] : List ℚ).map (fun t => Formula.evalRat (fun _ => t) (eliminateConjunction cs))

/-- info: [false, true, true, true, false] -/
#guard_msgs in
#eval
  let y : Expr 1 := .variable 0
  let cs : List (Constraint 1) := [⟨.constant 1, .neg (.mul y y), false⟩,
    ⟨.constant (-1), .constant 1, false⟩]
  ([-2, -1, 0, 1, 2] : List ℚ).map
    (fun t => Formula.evalRat (fun _ => t) (eliminateConjunction cs))

/-- info: [false, false, true, false, false] -/
#guard_msgs in
#eval
  let y : Expr 1 := .variable 0
  let cs : List (Constraint 1) := [⟨.constant 1, .neg (.mul y y), true⟩,
    ⟨.constant (-1), .constant 1, false⟩]
  ([-2, -1, 0, 1, 2] : List ℚ).map
    (fun t => Formula.evalRat (fun _ => t) (eliminateConjunction cs))

/-- info: [true, false, true] -/
#guard_msgs in
#eval
  let y : Expr 1 := .variable 0
  let f := AffineFormula.neg (AffineFormula.equalZero y (.constant 0))
  ([-1, 0, 1] : List ℚ).map (fun t => Formula.evalRat (fun _ => t) (eliminate f))

end MemorySemialgebraic.SymbolicQE
