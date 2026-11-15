module
public import Continuation.Semialgebraic.SymbolicTarski
public import Continuation.Semialgebraic.InfinitySamples
public import Continuation.Semialgebraic.ConstantBranchPruning
public meta import Continuation.Semialgebraic.SymbolicTarski
public meta import TauCeti.Geometry.RealAlgebraic.SignDetermination.Moments

/-! # Symbolic BKR sign counts

All coefficients of the finite ternary moment inverse are rational constants.
Combining the symbolic integer Tarski-query trees therefore produces an executable
finite rational-valued sign tree, exactly equal to the number of distinct roots
realizing a specified family of polynomial signs.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Polynomial SignType TauCeti.SignDetermination
open scoped Matrix
variable {n m : ℕ}

namespace SignTree
def sumRational (ts : List (SignTree n ℚ)) : SignTree n ℚ := (sequence ts).map List.sum

theorem sumRational_correct (v : Fin n → ℝ) (ts : List (SignTree n ℚ)) :
    (sumRational ts).evalReal v = (ts.map (evalReal v)).sum := by
  simp only [sumRational, evalReal_map, sequence_correct]
end SignTree

namespace SymbolicPoly
def power (p : SymbolicPoly n) : ℕ → SymbolicPoly n
  | 0 => [.constant 1]
  | k+1 => mul (power p k) p

@[simp] theorem denote_power (v : Fin n → ℝ) (p : SymbolicPoly n) (k : ℕ) :
    denote v (power p k) = (denote v p)^k := by
  induction k with
  | zero => simp [power, Expr.evalReal]
  | succ k ih => simp only [power, denote_mul, ih, pow_succ]

def product : List (SymbolicPoly n) → SymbolicPoly n
  | [] => [.constant 1]
  | p :: ps => mul p (product ps)

@[simp] theorem denote_product (v : Fin n → ℝ) (ps : List (SymbolicPoly n)) :
    denote v (product ps) = (ps.map (denote v)).prod := by
  induction ps with
  | nil => simp [product, Expr.evalReal]
  | cons p ps ih => simp only [product, denote_mul, ih, List.map_cons, List.prod_cons]

def powerProduct (Q : Fin m → SymbolicPoly n) (e : Fin m → Fin 3) : SymbolicPoly n :=
  product (List.ofFn fun j => power (Q j) (e j).val)

@[simp] theorem denote_powerProduct (v : Fin n → ℝ) (Q : Fin m → SymbolicPoly n)
    (e : Fin m → Fin 3) :
    denote v (powerProduct Q e) = ∏ j, (denote v (Q j)) ^ (e j).val := by
  simp only [powerProduct, denote_product, List.map_ofFn, Function.comp_def,
    denote_power, List.prod_ofFn]

/-- Explicit enumeration, avoiding the noncomputable ordering in `Finset.toList`. -/
def ternaryWords : (k : ℕ) → List (Fin k → Fin 3)
  | 0 => [Fin.elim0]
  | k+1 => (List.ofFn fun a : Fin 3 => (ternaryWords k).map (Fin.cons a)).flatten

theorem sum_ternaryWords (k : ℕ) (f : (Fin k → Fin 3) → ℚ) :
    ((ternaryWords k).map f).sum = ∑ e, f e := by
  induction k with
  | zero =>
    simp only [ternaryWords, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Fintype.sum_unique]
    congr 1
  | succ k ih =>
    simp only [ternaryWords, List.map_flatten, List.sum_flatten, List.map_map,
      List.map_ofFn, Function.comp_def, List.sum_ofFn]
    simp_rw [ih]
    calc
      _ = ∑ a : Fin 3 × (Fin k → Fin 3), f (Fin.cons a.1 a.2) :=
        (Fintype.sum_prod_type (fun a : Fin 3 × (Fin k → Fin 3) => f (Fin.cons a.1 a.2))).symm
      _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => Fin 3)) _ _ (fun _ => rfl)

def count (p : SymbolicPoly n) (Q : Fin m → SymbolicPoly n)
    (σ : Fin m → SignType) : SignTree n ℚ :=
  SignTree.sumRational ((ternaryWords m).map fun e =>
    (query p (powerProduct Q e)).pruneConstants.map fun z : ℤ =>
      (∏ j, SignType.lagrangeCoeff (σ j) (e j)) * (z : ℚ))

theorem count_correct (v : Fin n → ℝ) (p : SymbolicPoly n) (Q : Fin m → SymbolicPoly n)
    (σ : Fin m → SignType) :
    (count p Q σ).evalReal v =
      (Finset.signCount (denote v p).roots.toFinset (fun j => denote v (Q j)) σ : ℚ) := by
  have h := congrFun (Polynomial.fullInverse_mulVec_tarskiQuery
    (denote v p) (fun j => denote v (Q j))) σ
  rw [← h]
  simp only [count, SignTree.sumRational_correct, List.map_map, Function.comp_def,
    SignTree.evalReal_map, SignTree.pruneConstants_correct, query_correct, denote_powerProduct, Matrix.mulVec, dotProduct,
    fullInverse_apply]
  exact sum_ternaryWords m _

theorem normalize_eq_nil_iff (v : Fin n → ℝ) (p : SymbolicPoly n) :
    (normalizeCoeffs p).evalReal v = [] ↔ denote v p = 0 := by
  constructor
  · intro h
    rw [← denote_normalize v p, h, denote_nil]
  · intro h
    cases hn : (normalizeCoeffs p).evalReal v with
    | nil => rfl
    | cons a as =>
      have ha := normalizeCoeffs_head_ne_zero v p a as hn
      have hd := degree_cons v a as ha
      have hz : denote v (a :: as) = 0 := by simpa only [hn, h] using denote_normalize v p
      rw [hz, degree_zero] at hd
      exact False.elim (WithBot.bot_ne_coe hd)

def nonzeroFactor (p : SymbolicPoly n) : SignTree n (SymbolicPoly n) :=
  (normalizeCoeffs p).map fun q => if q.isEmpty then [.constant 1] else q

theorem nonzeroFactor_correct (v : Fin n → ℝ) (p : SymbolicPoly n) :
    denote v ((nonzeroFactor p).evalReal v) = if denote v p = 0 then 1 else denote v p := by
  simp only [nonzeroFactor, SignTree.evalReal_map]
  by_cases h : (normalizeCoeffs p).evalReal v = []
  · simp [h, (normalize_eq_nil_iff v p).mp h, Expr.evalReal]
  · have hz := mt (normalize_eq_nil_iff v p).mpr h
    have he : ((normalizeCoeffs p).evalReal v).isEmpty = false := by
      cases hq : (normalizeCoeffs p).evalReal v <;> simp_all
    simp only [he, Bool.false_eq_true, ↓reduceIte, hz, denote_normalize]

def familyProduct (Q : Fin m → SymbolicPoly n) : SignTree n (SymbolicPoly n) :=
  (SignTree.sequence (List.ofFn fun j => nonzeroFactor (Q j))).map product

theorem familyProduct_correct (v : Fin n → ℝ) (Q : Fin m → SymbolicPoly n) :
    denote v ((familyProduct Q).evalReal v) = sampleProduct (fun j => denote v (Q j)) := by
  classical
  simp only [familyProduct, SignTree.evalReal_map, SignTree.sequence_correct,
    denote_product, List.map_ofFn, Function.comp_def, nonzeroFactor_correct,
    List.prod_ofFn, sampleProduct_def, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : denote v (Q j) = 0 <;> simp [h]

end SymbolicPoly
end MemorySemialgebraic.SymbolicQE
