module
public import Continuation.Semialgebraic.SymbolicGram
public import Continuation.Smooth.GramExact
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.SmoothGramSyntax
open Matrix SmoothGramModel

/-- Explicit finite conjunction over the minimizer datum and all query data. -/
def allIndex {N n : ℕ} (f : Index N → Formula n) : Formula n :=
  .conj (f none) (Formula.all (List.ofFn fun i => f (some i)))

@[simp] theorem allIndex_correct {N n : ℕ} (f : Index N → Formula n) (a : Fin n → ℝ) :
    (allIndex f).evalReal a ↔ ∀ i,(f i).evalReal a := by
  simp only [allIndex,Formula.evalReal,Formula.all_ofFn_eval]
  exact ⟨fun h i => Option.casesOn i h.1 h.2,fun h => ⟨h none,fun i => h (some i)⟩⟩

def sumIndex {N n : ℕ} (f : Index N → Expr n) : Expr n :=
  .add (f none) (Expr.sumList (List.ofFn fun i => f (some i)))

@[simp] theorem sumIndex_correct {N n : ℕ} (f : Index N → Expr n) (a : Fin n → ℝ) :
    (sumIndex f).evalReal a = ∑ i,(f i).evalReal a := by
  simp only [sumIndex,Expr.evalReal,Expr.eval_sumList_ofFn,Fintype.sum_option]

def pair {N n : ℕ} (M : Matrix (Index N) (Index N) (Expr n))
    (u v : Index N → Expr n) : Expr n :=
  sumIndex fun i => .mul (u i) (sumIndex fun j => .mul (M i j) (v j))

@[simp] theorem pair_correct {N n : ℕ} (M : Matrix (Index N) (Index N) (Expr n))
    (u v : Index N → Expr n) (a : Fin n → ℝ) :
    (pair M u v).evalReal a = (fun i => (u i).evalReal a) ⬝ᵥ
      ((M.map (Expr.evalReal a)) *ᵥ (fun i => (v i).evalReal a)) := by
  simp only [pair,sumIndex_correct,Expr.evalReal,dotProduct,mulVec,Matrix.map_apply]

def valueExpr {N n : ℕ} (φ : Fin (N+1) → Expr n) : Index N → Expr n
  | none => .constant 0
  | some i => φ i

@[simp] theorem valueExpr_correct {N n : ℕ} (φ : Fin (N+1) → Expr n)
    (a : Fin n → ℝ) (i : Index N) :
    (valueExpr φ i).evalReal a = value (fun j => (φ j).evalReal a) i := by
  cases i <;> simp only [valueExpr,value,Expr.evalReal,Rat.cast_zero]

def gradientExpr {N n : ℕ} : Index N → Index N → Expr n
  | none,_ => .constant 0
  | some i,j => if j=some i then .constant 1 else .constant 0

@[simp] theorem gradientExpr_correct {N n : ℕ} (a : Fin n → ℝ) (i j : Index N) :
    (gradientExpr i j).evalReal a = w i j := by
  cases i <;> simp [gradientExpr,w,Pi.single_apply,Expr.evalReal,apply_ite,-Expr.evalReal_refines]

def queryExpr {N n : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) :
    Index N → Index N → Expr n
  | none,_ => .constant 0
  | some i,j => .add (if j=none then .constant 1 else .constant 0)
      (Expr.sumList (List.ofFn fun k : Fin i.val =>
        .mul (W i ⟨k.val,by omega⟩)
          (if j=some ⟨k.val,by omega⟩ then .constant 1 else .constant 0)))

@[simp] theorem queryExpr_correct {N n : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) (a : Fin n → ℝ) (i j : Index N) :
    (queryExpr W i j).evalReal a = v (W.map (Expr.evalReal a)) i j := by
  cases i <;> simp [-Expr.evalReal_refines,queryExpr,Expr.evalReal,
    v,Pi.single_apply,Finset.sum_apply,Matrix.map_apply,apply_ite,
    List.map_ofFn,List.sum_ofFn,Function.comp_apply]

def difference {N n : ℕ} (u v : Index N → Expr n) : Index N → Expr n :=
  fun i => Expr.sub (u i) (v i)

theorem difference_correct {N n : ℕ} (u v : Index N → Expr n) (a : Fin n → ℝ) :
    (fun i => (difference u v i).evalReal a) =
      (fun i => (u i).evalReal a) - (fun i => (v i).evalReal a) := rfl

def psdFormula {N n : ℕ} (M : Matrix (Index N) (Index N) (Expr n)) : FirstOrder n :=
  GramSyntax.psdFormula (M.submatrix (finSuccEquiv (N+1)) (finSuccEquiv (N+1)))

@[simp] theorem psdFormula_correct {N n : ℕ} (M : Matrix (Index N) (Index N) (Expr n))
    (a : Fin n → ℝ) :
    (psdFormula M).evalReal a ↔ (M.map (Expr.evalReal a)).PosSemidef := by
  rw [psdFormula,GramSyntax.psdFormula_correct]
  exact Matrix.posSemidef_submatrix_equiv (M:=M.map (Expr.evalReal a)) (finSuccEquiv (N+1))

/-- Multiplication by the positive smoothness denominator keeps every atom polynomial. -/
lemma scaled_nonneg_iff (L A B : ℝ) (hL : 0<L) :
    0 ≤ (2*L)*A-B ↔ 0 ≤ A-1/(2*L)*B := by
  have hp : 0<2*L := by positivity
  have he : (2*L)*(A-1/(2*L)*B) = (2*L)*A-B := by field_simp
  rw [← he,mul_nonneg_iff_of_pos_left hp]

def interpolationFormula {N n : ℕ} (L : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n))
    (M : Matrix (Index N) (Index N) (Expr n)) (φ : Fin (N+1) → Expr n) : Formula n :=
  allIndex fun i => allIndex fun j => .nonnegative (Expr.sub
    (.mul (.mul (.constant 2) L)
      (Expr.sub (Expr.sub (valueExpr φ i) (valueExpr φ j))
        (pair M (gradientExpr j) (difference (queryExpr W i) (queryExpr W j)))))
    (pair M (difference (gradientExpr i) (gradientExpr j))
      (difference (gradientExpr i) (gradientExpr j))))

def feasibleFormula {N n : ℕ} (L R : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n))
    (M : Matrix (Index N) (Index N) (Expr n)) (φ : Fin (N+1) → Expr n) : FirstOrder n :=
  .conj (psdFormula M) (.atom (.conj
    (.nonnegative (Expr.sub (.mul R R) (M none none)))
    (interpolationFormula L W M φ)))

theorem feasibleFormula_correct {N n : ℕ} (L R : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n))
    (M : Matrix (Index N) (Index N) (Expr n)) (φ : Fin (N+1) → Expr n)
    (a : Fin n → ℝ) (hL : 0<L.evalReal a) :
    (feasibleFormula L R W M φ).evalReal a ↔
      Feasible (W.map (Expr.evalReal a)) (L.evalReal a) (R.evalReal a)
        (M.map (Expr.evalReal a)) (fun i => (φ i).evalReal a) := by
  simp only [feasibleFormula,FirstOrder.evalReal,psdFormula_correct,Formula.evalReal,
    interpolationFormula,allIndex_correct,Expr.sub,Expr.evalReal,pair_correct,
    difference_correct,gradientExpr_correct,queryExpr_correct,valueExpr_correct,
    Rat.cast_ofNat,← sub_eq_add_neg,sub_nonneg]
  simp only [Feasible,Matrix.map_apply,pow_two]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  simpa only [sub_nonneg] using scaled_nonneg_iff (L.evalReal a)
    (value (fun j => (φ j).evalReal a) i-value (fun j => (φ j).evalReal a) j-
      w j ⬝ᵥ ((M.map (Expr.evalReal a)) *ᵥ
        (v (W.map (Expr.evalReal a)) i-v (W.map (Expr.evalReal a)) j)))
    ((w i-w j) ⬝ᵥ ((M.map (Expr.evalReal a)) *ᵥ (w i-w j))) hL

end MemorySemialgebraic.SymbolicQE.SmoothGramSyntax
