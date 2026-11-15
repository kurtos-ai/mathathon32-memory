module
public import Continuation.Semialgebraic.SymbolicSturm
public meta import Continuation.Semialgebraic.SignBranching
public meta import Mathlib.Data.List.SignVariations

/-! # Symbolic signs and infinity variations

Finite trees compute the exact signs at both infinities, including parameter
specializations that lower the degree or make the polynomial identically zero.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Polynomial SignType TauCeti.Sturm
variable {n : ℕ}

def expressionSign (e : Expr n) : SignTree n SignType := .branch e (.leaf (-1)) (.leaf 0) (.leaf 1)

theorem expressionSign_correct (v : Fin n → ℝ) (e : Expr n) :
    (expressionSign e).evalReal v = sign (e.evalReal v) := by
  simp only [expressionSign, SignTree.evalReal]
  rcases lt_trichotomy (e.evalReal v) 0 with h | h | h
  · simp [-Expr.evalReal_refines, h, sign_eq_neg_one_iff.mpr h]
  · simp [-Expr.evalReal_refines, h]
  · simp [-Expr.evalReal_refines, not_lt_of_gt h, ne_of_gt h, sign_eq_one_iff.mpr h]

namespace SignTree
def sequence {α : Type} : List (SignTree n α) → SignTree n (List α)
  | [] => .leaf []
  | t :: ts => t.bind fun a => (sequence ts).map (a :: ·)

theorem sequence_correct {α : Type} (v : Fin n → ℝ) (ts : List (SignTree n α)) :
    (sequence ts).evalReal v = ts.map (evalReal v) := by
  induction ts <;> simp_all only [sequence, evalReal_bind, evalReal_map, evalReal, List.map_cons,
    List.map_nil]
end SignTree

namespace SymbolicPoly

/-- The first sign is at negative infinity and the second at positive infinity. -/
def infinitySigns (p : SymbolicPoly n) : SignTree n (SignType × SignType) :=
  (normalizeCoeffs p).bind fun q => match q with
  | [] => .leaf (0, 0)
  | a :: as => (expressionSign a).map fun s => (s * (-1) ^ as.length, s)

theorem infinitySigns_correct (v : Fin n → ℝ) (p : SymbolicPoly n) :
    (infinitySigns p).evalReal v =
      (sign ((denote v p).leadingCoeff * (-1) ^ (denote v p).natDegree),
        sign (denote v p).leadingCoeff) := by
  simp only [infinitySigns, SignTree.evalReal_bind]
  have hnorm := denote_normalize v p
  cases hq : (normalizeCoeffs p).evalReal v with
  | nil =>
    have hp : denote v p = 0 := by simpa only [hq, denote_nil] using hnorm.symm
    simp [SignTree.evalReal, hp]
  | cons a as =>
    have ha := normalizeCoeffs_head_ne_zero v p a as hq
    rw [hq] at hnorm
    have hdeg : (denote v p).natDegree = as.length := by
      rw [← hnorm]
      exact natDegree_eq_of_degree_eq_some (degree_cons v a as ha)
    have hlc : (denote v p).leadingCoeff = a.evalReal v := by
      rw [← hnorm]
      exact leadingCoeff_cons v a as ha
    have hm : sign (-1 : ℝ) = -1 := sign_eq_neg_one_iff.mpr neg_one_lt_zero
    simp only [SignTree.evalReal_map, expressionSign_correct, hdeg, hlc, sign_mul, sign_pow, hm]

def infinityVariations (ps : List (SymbolicPoly n)) : SignTree n ℤ :=
  (SignTree.sequence (ps.map infinitySigns)).map fun ss =>
    (List.signVariations (ss.map Prod.fst) : ℤ) - List.signVariations (ss.map Prod.snd)

theorem infinityVariations_correct (v : Fin n → ℝ) (ps : List (SymbolicPoly n)) :
    (infinityVariations ps).evalReal v =
      (signVariationsAtBot (ps.map (denote v)) : ℤ) - signVariationsAtTop (ps.map (denote v)) := by
  simp only [infinityVariations, SignTree.evalReal_map, SignTree.sequence_correct,
    List.map_map, Function.comp_def, infinitySigns_correct, signVariationsAtBot_def,
    signVariationsAtTop_def]
  have hbot : List.signVariations
      (ps.map fun p => sign ((denote v p).leadingCoeff * (-1) ^ (denote v p).natDegree)) =
      List.signVariations (ps.map fun p => (denote v p).leadingCoeff * (-1) ^ (denote v p).natDegree) := by
    simpa only [List.map_map, Function.comp_def] using List.signVariations_map_sign
      (ps.map fun p => (denote v p).leadingCoeff * (-1) ^ (denote v p).natDegree)
  have htop : List.signVariations (ps.map fun p => sign (denote v p).leadingCoeff) =
      List.signVariations (ps.map fun p => (denote v p).leadingCoeff) := by
    simpa only [List.map_map, Function.comp_def] using List.signVariations_map_sign
      (ps.map fun p => (denote v p).leadingCoeff)
  exact congrArg₂ (fun a b : ℕ => (a : ℤ) - b) hbot htop

/-- info: [(1, -1), (1, 1), (-1, 1)] -/
#guard_msgs in
#eval ([-1, 0, 1] : List ℚ).map fun y =>
  let s := (infinitySigns ([.variable 0, .constant 1] : SymbolicPoly 1)).evalRat (fun _ => y)
  ((s.1 : ℤ), (s.2 : ℤ))

end SymbolicPoly
end MemorySemialgebraic.SymbolicQE
