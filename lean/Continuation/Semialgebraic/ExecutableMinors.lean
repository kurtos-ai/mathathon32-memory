module
public import Continuation.Semialgebraic.SymbolicAffineQE
public import Continuation.Semialgebraic.MinorRank
public import MemoryRank.IncrementalRank
public meta import Continuation.Semialgebraic.SymbolicAffineQE
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Matrix

namespace Expr
variable {n : ℕ}

def sumList : List (Expr n) → Expr n
  | [] => .constant 0
  | a :: p => .add a (sumList p)

@[simp] theorem eval_sumList (v : Fin n → ℝ) (p : List (Expr n)) :
    (sumList p).evalReal v = (p.map (Expr.evalReal v)).sum := by
  induction p <;> simp_all only [sumList,evalReal,Rat.cast_zero,List.map_nil,List.sum_nil,
    List.map_cons,List.sum_cons]

@[simp] theorem eval_sumList_ofFn (v : Fin n → ℝ) {k : ℕ} (p : Fin k → Expr n) :
    (sumList (List.ofFn p)).evalReal v = ∑ i,(p i).evalReal v := by
  rw [eval_sumList,List.map_ofFn,List.sum_ofFn]
  rfl

/-- Executable Laplace expansion; no polynomial syntax or choice oracle is used. -/
def determinant : (k : ℕ) → Matrix (Fin k) (Fin k) (Expr n) → Expr n
  | 0, _ => .constant 1
  | k+1, A => sumList (List.ofFn fun j : Fin (k+1) =>
      .mul (.mul (.constant ((-1:ℚ)^j.val)) (A 0 j))
        (determinant k (A.submatrix Fin.succ j.succAbove)))

/-- The executable expansion specializes to the actual matrix determinant. -/
@[simp] theorem determinant_eval (v : Fin n → ℝ) (k : ℕ)
    (A : Matrix (Fin k) (Fin k) (Expr n)) :
    (determinant k A).evalReal v = (A.map (Expr.evalReal v)).det := by
  induction k with
  | zero => simp [-evalReal_refines,determinant,evalReal]
  | succ k ih =>
    rw [determinant,eval_sumList_ofFn,Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    simp only [evalReal,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,ih,Matrix.map_apply]
    rfl
end Expr

/-- An explicit list of every map between two finite ordinals, including empty domains. -/
def allTuples (k : ℕ) : (l : ℕ) → List (Fin l → Fin k)
  | 0 => [Fin.elim0]
  | l+1 => (List.ofFn fun a : Fin k => (allTuples k l).map (Fin.cons a)).flatten

@[simp] theorem mem_allTuples (k l : ℕ) (f : Fin l → Fin k) : f ∈ allTuples k l := by
  induction l with
  | zero =>
    have hf : f=Fin.elim0 := by ext i; exact Fin.elim0 i
    simp [allTuples,hf]
  | succ l ih =>
    rw [allTuples,List.mem_flatten]
    refine ⟨(allTuples k l).map (Fin.cons (f 0)),?_,?_⟩
    · exact List.mem_ofFn.mpr ⟨f 0,rfl⟩
    · exact List.mem_map.mpr ⟨Fin.tail f,ih (Fin.tail f),Fin.cons_self_tail f⟩

namespace Formula
variable {n : ℕ}

@[simp] theorem all_ofFn_eval (v : Fin n → ℝ) {k : ℕ} (f : Fin k → Formula n) :
    (all (List.ofFn f)).evalReal v ↔ ∀ i,(f i).evalReal v := by
  simp [all_eval,List.mem_ofFn]

/-- All minors of size m+1, enumerating maps rather than relying on noncomputable finite sets. -/
def rankBound (r c m : ℕ) (A : Matrix (Fin r) (Fin c) (Expr n)) : Formula n :=
  all ((allTuples r (m+1)).map fun rows =>
    all ((allTuples c (m+1)).map fun cols =>
      .eqZero (Expr.determinant (m+1) (A.submatrix rows cols))))

@[simp] theorem rankBound_eval (v : Fin n → ℝ) (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) (Expr n)) :
    (rankBound r c m A).evalReal v ↔ (A.map (Expr.evalReal v)).rank ≤ m := by
  rw [MinorSelection.rank_le_iff_minors_vanish]
  simp only [rankBound,all_eval,List.forall_mem_map,evalReal,Expr.determinant_eval]
  simp only [mem_allTuples,forall_const]
  rfl

/-- Explicit zero entries on and above the diagonal. -/
def strictLower (N : ℕ) (A : Matrix (Fin N) (Fin N) (Expr n)) : Formula n :=
  all (List.ofFn fun i : Fin N => all (List.ofFn fun j : Fin N =>
    if i.val ≤ j.val then .eqZero (A i j) else .tru))

@[simp] theorem strictLower_eval (v : Fin n → ℝ) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) (Expr n)) :
    (strictLower N A).evalReal v ↔ ∀ i j,i.val ≤ j.val → (A i j).evalReal v=0 := by
  simp only [strictLower,all_ofFn_eval]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  by_cases h : i.val ≤ j.val <;> simp [h,evalReal]

end Formula
end MemorySemialgebraic.SymbolicQE
