module
public import Continuation.Semialgebraic.AlgebraicParameters
public meta import Continuation.Semialgebraic.AlgebraicParameters

@[expose] public section
namespace MemorySemialgebraic.AlgebraicParameters
open SymbolicQE

/-- Polynomial expressions over a finite specified coefficient table. -/
inductive AlgebraicExpr (k n : ℕ) where
  | rational : ℚ → AlgebraicExpr k n
  | coefficient : Fin k → AlgebraicExpr k n
  | variable : Fin n → AlgebraicExpr k n
  | add : AlgebraicExpr k n → AlgebraicExpr k n → AlgebraicExpr k n
  | neg : AlgebraicExpr k n → AlgebraicExpr k n
  | mul : AlgebraicExpr k n → AlgebraicExpr k n → AlgebraicExpr k n
  deriving DecidableEq, Repr

namespace AlgebraicExpr
noncomputable def evalReal {k n : ℕ} (a : Fin k → ℝ) (v : Fin n → ℝ) : AlgebraicExpr k n → ℝ
  | .rational q => q
  | .coefficient i => a i
  | .variable j => v j
  | .add p q => evalReal a v p + evalReal a v q
  | .neg p => -evalReal a v p
  | .mul p q => evalReal a v p * evalReal a v q

/-- Replace algebraic constants by fresh variables; every remaining coefficient is rational. -/
def compile {k n : ℕ} : AlgebraicExpr k n → Expr (k+n)
  | .rational q => .constant q
  | .coefficient i => .variable (Fin.castAdd n i)
  | .variable j => .variable (Fin.natAdd k j)
  | .add p q => .add (compile p) (compile q)
  | .neg p => .neg (compile p)
  | .mul p q => .mul (compile p) (compile q)

@[simp] theorem compile_eval {k n : ℕ} (a : Fin k → ℝ) (v : Fin n → ℝ) (p : AlgebraicExpr k n) :
    Expr.evalReal (assignment a v) (compile p) = evalReal a v p := by
  induction p <;> simp_all [-Expr.evalReal_refines,compile,evalReal,Expr.evalReal]
end AlgebraicExpr

inductive AlgebraicFormula (k n : ℕ) where
  | eqZero : AlgebraicExpr k n → AlgebraicFormula k n
  | positive : AlgebraicExpr k n → AlgebraicFormula k n
  | nonnegative : AlgebraicExpr k n → AlgebraicFormula k n
  | conj : AlgebraicFormula k n → AlgebraicFormula k n → AlgebraicFormula k n
  | disj : AlgebraicFormula k n → AlgebraicFormula k n → AlgebraicFormula k n
  | neg : AlgebraicFormula k n → AlgebraicFormula k n
  | tru : AlgebraicFormula k n
  | fls : AlgebraicFormula k n
  deriving DecidableEq, Repr

namespace AlgebraicFormula
noncomputable def evalReal {k n : ℕ} (a : Fin k → ℝ) (v : Fin n → ℝ) : AlgebraicFormula k n → Prop
  | .eqZero p => AlgebraicExpr.evalReal a v p = 0
  | .positive p => 0 < AlgebraicExpr.evalReal a v p
  | .nonnegative p => 0 ≤ AlgebraicExpr.evalReal a v p
  | .conj f g => evalReal a v f ∧ evalReal a v g
  | .disj f g => evalReal a v f ∨ evalReal a v g
  | .neg f => ¬evalReal a v f
  | .tru => True
  | .fls => False

def compile {k n : ℕ} : AlgebraicFormula k n → Formula (k+n)
  | .eqZero p => .eqZero p.compile
  | .positive p => .positive p.compile
  | .nonnegative p => .nonnegative p.compile
  | .conj f g => .conj (compile f) (compile g)
  | .disj f g => .disj (compile f) (compile g)
  | .neg f => .neg (compile f)
  | .tru => .tru
  | .fls => .fls

@[simp] theorem compile_eval {k n : ℕ} (a : Fin k → ℝ) (v : Fin n → ℝ)
    (f : AlgebraicFormula k n) :
    Formula.evalReal (assignment a v) (compile f) ↔ evalReal a v f := by
  induction f <;> simp_all [-Expr.evalReal_refines,compile,evalReal,Formula.evalReal]

/-- A rational QF body with all coefficient specifications adjoined. -/
def rationalBody {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFormula k n) : Formula (k+n) :=
  .conj (constraints cs) (compile f)

/-- Rationalization introduces exactly the uniquely specified coefficient variables. -/
theorem rationalBody_exact {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFormula k n)
    (v : Fin n → ℝ) :
    (∃ a : Fin k → ℝ, Formula.evalReal (assignment a v) (rationalBody cs f)) ↔
      evalReal (fun i => (cs i).value) v f := by
  constructor
  · rintro ⟨a,ha,hf⟩
    have heq : a = fun i => (cs i).value := by
      apply funext
      simpa only [constraints_exact,assignment_left] using ha
    subst a
    exact (compile_eval _ _ _).mp hf
  · intro hf
    refine ⟨fun i => (cs i).value,?_,(compile_eval _ _ _).mpr hf⟩
    simp [constraints_exact]

theorem rationalBody_toQF_exact {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFormula k n)
    (v : Fin n → ℝ) :
    (∃ a : Fin k → ℝ, (Formula.toQF (rationalBody cs f)).eval (assignment a v)) ↔
      evalReal (fun i => (cs i).value) v f := by
  simp only [Formula.toQF_refines]
  exact rationalBody_exact cs f v
end AlgebraicFormula

/-- A finite existential block over a rational polynomial formula. -/
structure RationalExistential (n : ℕ) where
  parameters : ℕ
  body : Formula (parameters+n)

noncomputable def RationalExistential.eval {n : ℕ} (F : RationalExistential n) (v : Fin n → ℝ) : Prop :=
  ∃ a : Fin F.parameters → ℝ, Formula.evalReal (assignment a v) F.body

def rationalize {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFormula k n) : RationalExistential n :=
  ⟨k,f.rationalBody cs⟩

/-- The reduction is a finite syntax transformation, with no algebraic oracle or real-valued
computation in the generated rational formula. -/
theorem rationalize_exact {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFormula k n)
    (v : Fin n → ℝ) :
    (rationalize cs f).eval v ↔ f.evalReal (fun i => (cs i).value) v :=
  f.rationalBody_exact cs v

/-- Arbitrary finitely specified real algebraic coefficients admit the exact rational reduction,
with their own minimal-polynomial equations and rational isolating cells. -/
theorem algebraic_coefficients_rational_reduction {k n : ℕ}
    (a : Fin k → ℝ) (ha : ∀ i, IsAlgebraic ℚ (a i)) (f : AlgebraicFormula k n) :
    ∃ cs : Fin k → Code,
      (∀ i, RootIsolation.Executable.denote (cs i).poly = minpoly ℚ (a i)) ∧
      ∀ v : Fin n → ℝ, (rationalize cs f).eval v ↔ f.evalReal a v := by
  obtain ⟨cs,hv,hp⟩ := exists_minpoly_codes a ha
  refine ⟨cs,hp,?_⟩
  intro v
  simpa only [hv] using rationalize_exact cs f v

end MemorySemialgebraic.AlgebraicParameters
