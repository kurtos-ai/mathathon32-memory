module
public import Continuation.Semialgebraic.ExecutableMinors
public import RealizationCore.Coordinates
public meta import Continuation.Semialgebraic.ExecutableMinors
public meta import Continuation.Semialgebraic.SymbolicAffineQE
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Matrix

/-- A symbolic cut retains the future increment rows and past gradient columns. -/
def cutEntries {n : ℕ} (N : ℕ) (A : Matrix (Fin N) (Fin N) (Expr n)) (k : Fin N) :
    Matrix (Fin (N-k.val)) (Fin k.val) (Expr n) :=
  fun i j => A ⟨k.val+i.val,by omega⟩ ⟨j.val,by omega⟩

lemma cutEntries_eval {n : ℕ} (v : Fin n → ℝ) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) (Expr n)) (k : Fin N) :
    (cutEntries N A k).map (Expr.evalReal v) =
      MemoryRank.Incremental.S_k N k.val (A.map (Expr.evalReal v)) := by
  ext i j
  simp [cutEntries,MemoryRank.Incremental.S_k,show k.val ≤ N by omega]

/-- Fully executable memory-locus syntax, compositional in arbitrary coefficient expressions. -/
def memoryFormula {n : ℕ} (N m : ℕ) (A : Matrix (Fin N) (Fin N) (Expr n)) : Formula n :=
  .conj (Formula.strictLower N A)
    (Formula.all (List.ofFn fun k : Fin N =>
      Formula.rankBound (N-k.val) k.val m (cutEntries N A k)))

/-- The computed formula expresses exactly strict triangularity and every required cut-rank bound. -/
theorem memoryFormula_correct {n : ℕ} (v : Fin n → ℝ) (N m : ℕ)
    (A : Matrix (Fin N) (Fin N) (Expr n)) :
    (memoryFormula N m A).evalReal v ↔
      (∀ i j,i.val ≤ j.val → (A i j).evalReal v = 0) ∧
      MemoryRank.Incremental.Q N m (A.map (Expr.evalReal v)) := by
  simp only [memoryFormula,Formula.evalReal,Formula.strictLower_eval,
    Formula.all_ofFn_eval,Formula.rankBound_eval,cutEntries_eval]
  apply and_congr Iff.rfl
  constructor
  · intro h k hk hkN
    exact h ⟨k,hkN⟩
  · intro h k
    by_cases hk : k.val=0
    · have hw := MemoryRank.Incremental.S_k_rank_le_width N k.val (A.map (Expr.evalReal v))
      omega
    · exact h k.val (by omega) k.isLt

/-- Rational formula variables are a fixed flattening of the N by N entry array. -/
def entryVariables (N : ℕ) : Matrix (Fin N) (Fin N) (Expr (N*N)) :=
  fun i j => .variable (finProdFinEquiv (i,j))

def matrixAssignment (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) : Fin (N*N) → ℝ :=
  fun k => T (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

lemma entryVariables_eval (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    (entryVariables N).map (Expr.evalReal (matrixAssignment N T)) = T := by
  ext i j
  simp only [entryVariables,Matrix.map_apply,Expr.evalReal,matrixAssignment,
    Equiv.symm_apply_apply]

def flatMemoryFormula (N m : ℕ) : Formula (N*N) := memoryFormula N m (entryVariables N)

/-- Given only N and m, this executable syntax describes the exact memory locus over N² real entries. -/
theorem flatMemoryFormula_correct (N m : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    (flatMemoryFormula N m).evalReal (matrixAssignment N T) ↔
      (∀ i j,i.val ≤ j.val → T i j=0) ∧ MemoryRank.Incremental.Q N m T := by
  rw [flatMemoryFormula,memoryFormula_correct,entryVariables_eval]
  simp only [entryVariables,Expr.evalReal,matrixAssignment,Equiv.symm_apply_apply]

/-- The syntax also characterizes actual one-coordinate register implementations at every step vector. -/
theorem flatMemoryFormula_realization (N m : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) :
    (flatMemoryFormula N m).evalReal (matrixAssignment N T.val) ↔
      RegisterMachine.HasRealization N (RealizationCore.W_of N d T.val) (m+1) := by
  rw [flatMemoryFormula_correct,RealizationCore.realization_iff_coordinates]
  exact and_iff_right T.property

/-- info: [false, true, false] -/
#guard_msgs in
#eval [
  (flatMemoryFormula 2 0).evalRat (fun i => if i.val=2 then 1 else 0),
  (flatMemoryFormula 2 1).evalRat (fun i => if i.val=2 then 1 else 0),
  (flatMemoryFormula 2 1).evalRat (fun i => if i.val=0 then 1 else 0)]

end MemorySemialgebraic.SymbolicQE
