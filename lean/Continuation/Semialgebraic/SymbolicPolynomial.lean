module
public import Continuation.Semialgebraic.SignBranching
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Data.List.GetD
public meta import Continuation.Semialgebraic.SymbolicAffineQE

/-!
# Polynomial lists with symbolic rational coefficients

Coefficients are executable rational polynomial expressions in the parameters.
The distinguished univariate coordinate is stored with its highest coefficient
first. No polynomial equality decision is used during arithmetic.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Polynomial

abbrev SymbolicPoly (n : ℕ) := List (Expr n)

namespace SymbolicPoly
variable {n : ℕ}

noncomputable def denote (v : Fin n → ℝ) (p : SymbolicPoly n) : ℝ[X] :=
  ofCoeffList ((p.map (Expr.evalReal v)).reverse)

@[simp] theorem denote_nil (v : Fin n → ℝ) : denote v [] = 0 := by simp [denote]

private theorem ofCoeffList_append (p q : List ℝ) :
    ofCoeffList (p ++ q) = ofCoeffList p + X ^ p.length * ofCoeffList q := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.cons_append, ofCoeffList_cons, List.length_cons, ih, pow_succ]
    ring

@[simp] theorem denote_cons (v : Fin n → ℝ) (a : Expr n) (p : SymbolicPoly n) :
    denote v (a :: p) = C (a.evalReal v) * X ^ p.length + denote v p := by
  simp only [denote, List.map_cons, List.reverse_cons, ofCoeffList_append,
    List.length_reverse, List.length_map, ofCoeffList_cons, ofCoeffList_nil,
    mul_zero, add_zero]
  ring

theorem degree_lt_length (v : Fin n → ℝ) (p : SymbolicPoly n) :
    (denote v p).degree < (p.length : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  simp only [denote, coeff_ofCoeffList]
  exact List.getD_eq_default _ 0 (by simpa using hk)

theorem degree_cons (v : Fin n → ℝ) (a : Expr n) (p : SymbolicPoly n)
    (ha : a.evalReal v ≠ 0) : (denote v (a :: p)).degree = (p.length : WithBot ℕ) := by
  rw [denote_cons, degree_add_eq_left_of_degree_lt]
  · exact degree_C_mul_X_pow _ ha
  · rw [degree_C_mul_X_pow _ ha]
    exact degree_lt_length v p

theorem leadingCoeff_cons (v : Fin n → ℝ) (a : Expr n) (p : SymbolicPoly n)
    (ha : a.evalReal v ≠ 0) : (denote v (a :: p)).leadingCoeff = a.evalReal v := by
  rw [denote_cons, leadingCoeff_add_of_degree_lt']
  · simp
  · rw [degree_C_mul_X_pow _ ha]
    exact degree_lt_length v p

theorem denote_normalize (v : Fin n → ℝ) (p : SymbolicPoly n) :
    denote v ((normalizeCoeffs p).evalReal v) = denote v p := by
  induction p with
  | nil => simp [normalizeCoeffs, SignTree.evalReal]
  | cons a p ih =>
    simp only [normalizeCoeffs, SignTree.evalReal]
    split
    · rfl
    · split
      · rename_i ha
        simpa only [denote_cons, ha, map_zero, zero_mul, zero_add] using ih
      · rfl

def addLow : SymbolicPoly n → SymbolicPoly n → SymbolicPoly n
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => Expr.add a b :: addLow p q

def add (p q : SymbolicPoly n) : SymbolicPoly n := (addLow p.reverse q.reverse).reverse
def neg (p : SymbolicPoly n) : SymbolicPoly n := p.map Expr.neg
def sub (p q : SymbolicPoly n) : SymbolicPoly n := add p (neg q)
def scale (a : Expr n) (p : SymbolicPoly n) : SymbolicPoly n := p.map (Expr.mul a)
def shift (p : SymbolicPoly n) (k : ℕ) : SymbolicPoly n :=
  p ++ List.replicate k (Expr.constant 0)

private theorem ofCoeffList_addLow (v : Fin n → ℝ) (p q : SymbolicPoly n) :
    ofCoeffList ((addLow p q).map (Expr.evalReal v)) =
      ofCoeffList (p.map (Expr.evalReal v)) + ofCoeffList (q.map (Expr.evalReal v)) := by
  induction p generalizing q with
  | nil => simp [addLow]
  | cons a p ih =>
    cases q with
    | nil => simp [addLow]
    | cons b q =>
      simp only [addLow, List.map_cons, Expr.evalReal, ofCoeffList_cons, ih, map_add]
      ring

@[simp] theorem denote_add (v : Fin n → ℝ) (p q : SymbolicPoly n) :
    denote v (add p q) = denote v p + denote v q := by
  simp only [denote, add, List.map_reverse, List.reverse_reverse]
  simpa only [List.map_reverse] using ofCoeffList_addLow v p.reverse q.reverse

@[simp] theorem denote_neg (v : Fin n → ℝ) (p : SymbolicPoly n) :
    denote v (neg p) = -denote v p := by
  simp only [denote, neg, List.map_map, Function.comp_def, Expr.evalReal,
    ← List.map_reverse]
  simpa only [List.map_map, Function.comp_def] using
    ofCoeffList_map_neg (p.reverse.map (Expr.evalReal v))

@[simp] theorem denote_sub (v : Fin n → ℝ) (p q : SymbolicPoly n) :
    denote v (sub p q) = denote v p - denote v q := by simp [sub, sub_eq_add_neg]

@[simp] theorem denote_scale (v : Fin n → ℝ) (a : Expr n) (p : SymbolicPoly n) :
    denote v (scale a p) = C (a.evalReal v) * denote v p := by
  simp only [denote, scale, List.map_map, Function.comp_def, Expr.evalReal,
    ← List.map_reverse]
  simpa only [List.map_map, Function.comp_def] using
    ofCoeffList_map_mul (a.evalReal v) (p.reverse.map (Expr.evalReal v))

@[simp] theorem denote_replicate_zero (v : Fin n → ℝ) (k : ℕ) :
    denote v (List.replicate k (Expr.constant 0)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, denote_cons, Expr.evalReal, Rat.cast_zero,
      map_zero, zero_mul, zero_add, ih]

@[simp] theorem denote_shift (v : Fin n → ℝ) (p : SymbolicPoly n) (k : ℕ) :
    denote v (shift p k) = denote v p * X ^ k := by
  induction p with
  | nil => simp [shift]
  | cons a p ih =>
    simp only [shift, List.cons_append, denote_cons, List.length_append,
      List.length_replicate] at *
    rw [ih, pow_add]
    ring

def mul : SymbolicPoly n → SymbolicPoly n → SymbolicPoly n
  | [], _ => []
  | a :: p, q => add (shift (scale a q) p.length) (mul p q)

@[simp] theorem denote_mul (v : Fin n → ℝ) (p q : SymbolicPoly n) :
    denote v (mul p q) = denote v p * denote v q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul, denote_add, denote_shift, denote_scale, ih, denote_cons]
    ring

@[simp] theorem length_addLow (p q : SymbolicPoly n) :
    (addLow p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [addLow]
  | cons a p ih => cases q <;> simp [addLow, ih]

@[simp] theorem length_add (p q : SymbolicPoly n) :
    (add p q).length = max p.length q.length := by simp [add]
@[simp] theorem length_neg (p : SymbolicPoly n) : (neg p).length = p.length := by simp [neg]
@[simp] theorem length_sub (p q : SymbolicPoly n) :
    (sub p q).length = max p.length q.length := by simp [sub]
@[simp] theorem length_scale (a : Expr n) (p : SymbolicPoly n) :
    (scale a p).length = p.length := by simp [scale]
@[simp] theorem length_shift (p : SymbolicPoly n) (k : ℕ) :
    (shift p k).length = p.length + k := by simp [shift]

end SymbolicPoly
end MemorySemialgebraic.SymbolicQE
