module
public import Continuation.Semialgebraic.SymbolicPolynomial
public import TauCeti.Algebra.Polynomial.Sturm.SignedRemainders
public meta import Continuation.Semialgebraic.SymbolicPolynomial

/-!
# Positive symbolic pseudo-division

Each cancellation multiplies by the square of the divisor's leading coefficient.
Thus the coefficients remain rational polynomial expressions in the parameters,
and every specialization with nonzero leading coefficient has positive scaling.
The runtime recursion decreases list length without deciding polynomial equality.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.SymbolicPoly
open Polynomial
variable {n : ℕ}

def cancel (a : Expr n) (p : SymbolicPoly n) (b : Expr n) (q : SymbolicPoly n) :
    SymbolicPoly n :=
  sub (scale (.mul b b) p) (scale (.mul b a) (shift q (p.length - q.length)))

theorem length_cancel (a : Expr n) (p : SymbolicPoly n) (b : Expr n) (q : SymbolicPoly n)
    (h : q.length ≤ p.length) : (cancel a p b q).length = p.length := by
  simp only [cancel, length_sub, length_scale, length_shift]
  omega

theorem cancel_identity (v : Fin n → ℝ) (a : Expr n) (p : SymbolicPoly n)
    (b : Expr n) (q : SymbolicPoly n) (h : q.length ≤ p.length) :
    C (b.evalReal v * b.evalReal v) * denote v (a :: p) =
      (C (b.evalReal v * a.evalReal v) * X ^ (p.length - q.length)) *
        denote v (b :: q) + denote v (cancel a p b q) := by
  simp only [cancel, denote_sub, denote_scale, denote_shift, denote_cons, Expr.evalReal,
    map_mul]
  have he : (X : ℝ[X]) ^ p.length = X ^ (p.length - q.length) * X ^ q.length := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  ring

/-- Positive pseudo-remainder; an empty divisor is returned unchanged. -/
def pseudoRemainder : SymbolicPoly n → SymbolicPoly n → SymbolicPoly n
  | p, [] => p
  | [], _ :: _ => []
  | a :: p, b :: q =>
    if _h : p.length < q.length then a :: p
    else pseudoRemainder (cancel a p b q) (b :: q)
termination_by p _ => p.length
decreasing_by
  rw [length_cancel _ _ _ _ (by omega)]
  simp

theorem pseudoRemainder_length (p : SymbolicPoly n) (b : Expr n) (q : SymbolicPoly n) :
    (pseudoRemainder p (b :: q)).length < (b :: q).length := by
  cases p with
  | nil => simp [pseudoRemainder]
  | cons a p =>
    rw [pseudoRemainder]
    split
    · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using ‹p.length < q.length›
    · exact pseudoRemainder_length (cancel a p b q) b q
termination_by p.length
decreasing_by
  rw [length_cancel _ _ _ _ (by omega)]
  simp

/-- The remainder comes with a positive scaling and an exact division identity. -/
theorem pseudoRemainder_identity (v : Fin n → ℝ) (p : SymbolicPoly n)
    (b : Expr n) (q : SymbolicPoly n) (hb : b.evalReal v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ u : ℝ[X],
      C c * denote v p = u * denote v (b :: q) + denote v (pseudoRemainder p (b :: q)) := by
  cases p with
  | nil => exact ⟨1, zero_lt_one, 0, by simp [pseudoRemainder]⟩
  | cons a p =>
    rw [pseudoRemainder]
    split
    · exact ⟨1, zero_lt_one, 0, by simp⟩
    · have hlen : q.length ≤ p.length := by omega
      obtain ⟨c, hc, u, hu⟩ := pseudoRemainder_identity v (cancel a p b q) b q hb
      refine ⟨c * (b.evalReal v * b.evalReal v), mul_pos hc (mul_self_pos.mpr hb),
        C c * (C (b.evalReal v * a.evalReal v) * X ^ (p.length - q.length)) + u, ?_⟩
      calc
        C (c * (b.evalReal v * b.evalReal v)) * denote v (a :: p) =
            C c * (C (b.evalReal v * b.evalReal v) * denote v (a :: p)) := by
              rw [map_mul, mul_assoc]
        _ = C c * ((C (b.evalReal v * a.evalReal v) * X ^ (p.length - q.length)) *
            denote v (b :: q) + denote v (cancel a p b q)) := by rw [cancel_identity v a p b q hlen]
        _ = _ := by rw [mul_add, hu]; ring
termination_by p.length
decreasing_by
  rw [length_cancel _ _ _ _ (by omega)]
  simp

/-- Negating a positive pseudo-remainder gives the exact upstream signed-chain relation. -/
theorem pseudoRemainder_signed (v : Fin n → ℝ) (p : SymbolicPoly n)
    (b : Expr n) (q : SymbolicPoly n) (hb : b.evalReal v ≠ 0) :
    TauCeti.Sturm.IsRemainder (denote v p) (denote v (b :: q))
      (denote v (neg (pseudoRemainder p (b :: q)))) := by
  obtain ⟨c, hc, u, hu⟩ := pseudoRemainder_identity v p b q hb
  refine TauCeti.Sturm.IsRemainder.of_identity c 1 u hc zero_lt_one ?_
  simpa only [denote_neg, map_one, one_mul, sub_neg_eq_add] using hu

/-- info: [32] -/
#guard_msgs in
#eval (pseudoRemainder
  ([.constant 1, .constant 0, .constant 1] : SymbolicPoly 0)
  [.constant 2, .constant 2]).map (Expr.evalRat Fin.elim0)

/-- info: [20, 16, 20] -/
#guard_msgs in
#eval ([-1, 0, 1] : List ℚ).map fun y =>
  ((pseudoRemainder ([.constant 1, .constant 0, .constant 1] : SymbolicPoly 1)
    [.constant 2, .variable 0]).map (Expr.evalRat (fun _ => y))).headD 0

end MemorySemialgebraic.SymbolicQE.SymbolicPoly
