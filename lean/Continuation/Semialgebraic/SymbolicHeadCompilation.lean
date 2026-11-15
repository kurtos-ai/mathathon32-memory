module
public import Continuation.Semialgebraic.SymbolicPolynomial
public import Mathlib.Algebra.Polynomial.Derivative
public meta import Continuation.Semialgebraic.SymbolicPolynomial
public meta import Continuation.Semialgebraic.SymbolicAffineQE
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Polynomial

namespace Expr
/-- Compile the head coordinate as a univariate indeterminate; all tail variables remain parameters. -/
def compileHead {n : ℕ} : Expr (n+1) → SymbolicPoly n
  | .constant q => [.constant q]
  | .variable i => Fin.cases [.constant 1,.constant 0] (fun j => [.variable j]) i
  | .add p q => SymbolicPoly.add (compileHead p) (compileHead q)
  | .neg p => SymbolicPoly.neg (compileHead p)
  | .mul p q => SymbolicPoly.mul (compileHead p) (compileHead q)

/-- Exact specialization of the head-variable compiler at arbitrary real parameters. -/
@[simp] theorem compileHead_correct {n : ℕ} (e : Expr (n+1)) (v : Fin n → ℝ) (x : ℝ) :
    (SymbolicPoly.denote v (compileHead e)).aeval x = Expr.evalReal (Fin.cons x v) e := by
  induction e with
  | constant q => simp [-evalReal_refines,compileHead,evalReal]
  | «variable» i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [-evalReal_refines,compileHead,evalReal]
    · simp [-evalReal_refines,compileHead,evalReal]
  | add p q hp hq => simp only [compileHead,SymbolicPoly.denote_add,map_add,evalReal,hp,hq]
  | neg p hp => simp [-evalReal_refines,compileHead,evalReal,hp]
  | mul p q hp hq => simp only [compileHead,SymbolicPoly.denote_mul,map_mul,evalReal,hp,hq]
end Expr

namespace SymbolicPoly
variable {n : ℕ}

/-- Differentiate the highest-coefficient-first executable symbolic list. -/
def derivative : SymbolicPoly n → SymbolicPoly n
  | [] => []
  | [_] => []
  | a :: b :: p => Expr.mul (.constant (p.length+1)) a :: derivative (b :: p)

@[simp] theorem length_derivative (p : SymbolicPoly n) :
    (derivative p).length = p.length-1 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => rfl
    | cons b p => simpa only [derivative,List.length_cons,Nat.add_sub_cancel] using congrArg (·+1) ih

/-- Symbolic differentiation commutes with specialization, including identically zero polynomials. -/
@[simp] theorem denote_derivative (v : Fin n → ℝ) (p : SymbolicPoly n) :
    denote v (derivative p) = (denote v p).derivative := by
  induction p with
  | nil => simp [derivative]
  | cons a p ih =>
    cases p with
    | nil => simp [derivative]
    | cons b p =>
      simp only [derivative,denote_cons,List.length_cons,Expr.evalReal,
        Rat.cast_add,Rat.cast_natCast,Rat.cast_one,length_derivative,
        Nat.add_sub_cancel,Polynomial.derivative_add,Polynomial.derivative_C_mul_X_pow] at *
      rw [ih]
      congr 1
      simp [mul_comm]

/-- The compiled derivative is the derivative of the input polynomial in its head variable. -/
theorem compileHead_derivative_correct (e : Expr (n+1)) (v : Fin n → ℝ) (x : ℝ) :
    (denote v (derivative e.compileHead)).aeval x =
      ((denote v e.compileHead).derivative).aeval x := by rw [denote_derivative]

end SymbolicPoly
end MemorySemialgebraic.SymbolicQE
