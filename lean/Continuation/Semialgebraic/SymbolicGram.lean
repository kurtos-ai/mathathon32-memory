module
public import Continuation.Semialgebraic.ExecutableMinors
public import Continuation.Semialgebraic.FirstOrderRename
public import Mathlib.LinearAlgebra.Matrix.PosDef
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Matrix
namespace FirstOrder

/-- Universally bind a finite head block using executable first-order syntax. -/
def allBlock (k n : ℕ) (f : FirstOrder (k+n)) : FirstOrder n :=
  .neg (existsBlock k n (.neg f))

theorem allBlock_correct (k n : ℕ) (f : FirstOrder (k+n)) (v : Fin n → ℝ) :
    (allBlock k n f).evalReal v ↔ ∀ a : Fin k → ℝ,f.evalReal (Fin.addCases a v) := by
  simp [allBlock,evalReal,existsBlock_correct]

end FirstOrder
namespace GramSyntax

/-- The ordinary matrix bilinear form, as a rational expression tree. -/
def pair {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n)) (u v : Fin q → Expr n) : Expr n :=
  Expr.sumList (List.ofFn fun i => .mul (u i)
    (Expr.sumList (List.ofFn fun j => .mul (M i j) (v j))))

@[simp] theorem pair_correct {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n))
    (u v : Fin q → Expr n) (a : Fin n → ℝ) :
    (pair M u v).evalReal a = (fun i => (u i).evalReal a) ⬝ᵥ
      ((M.map (Expr.evalReal a)) *ᵥ (fun i => (v i).evalReal a)) := by
  simp only [pair,Expr.eval_sumList_ofFn,Expr.evalReal,dotProduct,mulVec,Matrix.map_apply]

/-- Exact symmetry conditions, enumerated without a finite-set choice operation. -/
def symmetricFormula {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n)) : Formula n :=
  Formula.all (List.ofFn fun i => Formula.all (List.ofFn fun j =>
    .eqZero (Expr.sub (M i j) (M j i))))

theorem symmetricFormula_correct {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n))
    (a : Fin n → ℝ) :
    (symmetricFormula M).evalReal a ↔ (M.map (Expr.evalReal a)).IsHermitian := by
  simp only [symmetricFormula,Formula.all_ofFn_eval,Formula.evalReal,Expr.sub,Expr.evalReal,
    ← sub_eq_add_neg,sub_eq_zero]
  constructor
  · intro h
    ext i j
    simpa only [Matrix.conjTranspose_apply,Matrix.map_apply,star_trivial] using h j i
  · intro h i j
    have he := congrArg (fun A => A j i) h
    simpa only [Matrix.conjTranspose_apply,Matrix.map_apply,star_trivial] using he

/-- The universally tested quadratic form, with its vector bound before all external parameters. -/
def quadraticBody {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n)) : Formula (q+n) :=
  .nonnegative (pair (fun i j => (M i j).renameVariables (Fin.natAdd q))
    (fun i => .variable (Fin.castAdd n i)) (fun i => .variable (Fin.castAdd n i)))

theorem quadraticBody_correct {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n))
    (a : Fin n → ℝ) (x : Fin q → ℝ) :
    (quadraticBody M).evalReal (Fin.addCases x a) ↔
      0 ≤ x ⬝ᵥ ((M.map (Expr.evalReal a)) *ᵥ x) := by
  simp only [quadraticBody,Formula.evalReal,pair,Expr.eval_sumList_ofFn,Expr.evalReal,
    Fin.addCases_left,Expr.renameVariables_correct]
  have he : Fin.addCases x a ∘ Fin.natAdd q = a := by
    funext i
    simp
  rw [he]
  rfl

/-- Positive semidefiniteness is a finite first-order formula with rational polynomial atoms. -/
def psdFormula {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n)) : FirstOrder n :=
  .conj (.atom (symmetricFormula M)) (FirstOrder.allBlock q n (.atom (quadraticBody M)))

theorem psdFormula_correct {q n : ℕ} (M : Matrix (Fin q) (Fin q) (Expr n))
    (a : Fin n → ℝ) :
    (psdFormula M).evalReal a ↔ (M.map (Expr.evalReal a)).PosSemidef := by
  simp only [psdFormula,FirstOrder.evalReal,symmetricFormula_correct,FirstOrder.allBlock_correct,
    quadraticBody_correct,Matrix.posSemidef_iff_dotProduct_mulVec,star_trivial]

end GramSyntax
end MemorySemialgebraic.SymbolicQE
