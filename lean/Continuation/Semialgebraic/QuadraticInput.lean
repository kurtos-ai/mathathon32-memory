module
public import Continuation.Semialgebraic.ProcedureCoefficients
public import Continuation.Quadratic.ExactLossModel
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax
open Matrix Polynomial
open ProcedureSyntax

/-- Compile the residual recurrence directly from the method coefficients. -/
def residual {n : ℕ} (N : ℕ) (d : Fin N → Expr n)
    (T : Matrix (Fin N) (Fin N) (Expr n)) (x : Expr n) : ℕ → Expr n
  | 0 => .constant 1
  | k+1 => if h : k < N then
      .add (.mul (.add (.constant 1) (.mul (d ⟨k,h⟩) x)) (residual N d T x k))
        (.mul x (Expr.sumList (List.ofFn fun j : Fin k =>
          .mul (T ⟨k,h⟩ ⟨j.val,by omega⟩) (residual N d T x j.val))))
    else .constant 1

/-- The compiled expression equals evaluation of the paper's residual polynomial. -/
theorem residual_correct {n : ℕ} (N : ℕ) (d : Fin N → Expr n)
    (T : Matrix (Fin N) (Fin N) (Expr n)) (x : Expr n) (v : Fin n → ℝ) (k : ℕ) :
    (residual N d T x k).evalReal v =
      (QuadraticFoundations.pIter N (fun i => (d i).evalReal v)
        (T.map (Expr.evalReal v)) k).eval (x.evalReal v) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp only [residual,Expr.evalReal,Rat.cast_one,QuadraticFoundations.pIter,eval_one]
    | succ k =>
      by_cases h : k < N
      · simp only [residual,QuadraticFoundations.pIter,dite_eq_left h,Expr.evalReal,
          Expr.eval_sumList_ofFn,Rat.cast_one,eval_add,eval_mul,eval_C,eval_X,eval_finsetSum]
        rw [ih k (by omega)]
        congr 2
        apply Finset.sum_congr rfl
        intro j _
        rw [ih j.val (by omega)]
        rfl
      · simp only [residual,QuadraticFoundations.pIter,dite_eq_right h,Expr.evalReal,Rat.cast_one,eval_one]

/-- Bind the spectral value and squared radius; all other expressions remain parameters. -/
def lossFormula {n : ℕ} (N : ℕ) (d : Fin N → Expr n)
    (T : Matrix (Fin N) (Fin N) (Expr n)) (L R z : Expr n) : FirstOrder n :=
  let lift := fun e : Expr n => e.renameVariables (fun i => i.succ.succ)
  let mu : Expr (n+1+1) := .variable (Fin.succ 0)
  let rho : Expr (n+1+1) := .variable 0
  let p := residual N (fun i => lift (d i)) (fun i j => lift (T i j)) mu N
  .ex (.ex (.atom (Formula.all [
    .nonnegative mu, .nonnegative (Expr.sub (lift L) mu),
    .nonnegative rho, .nonnegative (Expr.sub (.mul (lift R) (lift R)) rho),
    .eqZero (Expr.sub (lift z) (.mul (.mul (.constant (1/2)) rho)
      (.mul mu (.mul p p))))])))

theorem lossFormula_correct {n : ℕ} (N : ℕ) (d : Fin N → Expr n)
    (T : Matrix (Fin N) (Fin N) (Expr n)) (L R z : Expr n) (v : Fin n → ℝ) :
    (lossFormula N d T L R z).evalReal v ↔
      z.evalReal v ∈ QuadraticSpectral.scalarLossSet (L.evalReal v) (R.evalReal v)
        (QuadraticFoundations.pIter N (fun i => (d i).evalReal v)
          (T.map (Expr.evalReal v)) N) := by
  have hp (mu rho : ℝ) :
      (residual N (fun i => (d i).renameVariables (fun j => j.succ.succ))
        (fun i j => (T i j).renameVariables (fun j => j.succ.succ))
        (.variable (Fin.succ 0)) N).evalReal (Fin.cons rho (Fin.cons mu v)) =
      (QuadraticFoundations.pIter N (fun i => (d i).evalReal v)
        (T.map (Expr.evalReal v)) N).eval mu := by
    have h := residual_correct N
      (fun i => (d i).renameVariables (fun j => j.succ.succ))
      (fun i j => (T i j).renameVariables (fun j => j.succ.succ))
      (.variable (Fin.succ 0)) (Fin.cons rho (Fin.cons mu v)) N
    simpa only [Expr.renameVariables_correct,Expr.evalReal,Fin.cons_succ,
      Fin.cons_zero,Function.comp_def,Matrix.map,Matrix.of_apply] using h
  simp only [lossFormula,FirstOrder.evalReal,Formula.all,Formula.evalReal,Expr.sub,
    Expr.evalReal,Expr.renameVariables_correct,Fin.cons_zero,Fin.cons_succ,and_true]
  simp only [hp,Function.comp_def,Fin.cons_succ,QuadraticSpectral.scalarLossSet,
    Set.mem_ofPred_eq,Set.mem_Icc,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  constructor
  · rintro ⟨mu,rho,hmu,hmuL,hrho,hrhoR,hz⟩
    exact ⟨mu,⟨hmu,by linarith⟩,rho,⟨hrho,by nlinarith⟩,by nlinarith [hz]⟩
  · rintro ⟨mu,⟨hmu,hmuL⟩,rho,⟨hrho,hrhoR⟩,hz⟩
    exact ⟨mu,rho,hmu,by linarith,hrho,by nlinarith,by nlinarith [hz]⟩

/-- A concrete input formula in the exact coefficient layout of the general procedure. -/
def input (N : ℕ) (L R : ℚ) : FirstOrder ((N+N*N)+1) :=
  lossFormula N
    (fun i => .variable (Fin.castAdd (N*N) i).succ)
    (fun i j => .variable (Fin.natAdd N (finProdFinEquiv (i,j))).succ)
    (.constant L) (.constant R) (.variable 0)

theorem input_correct (N : ℕ) (L R : ℚ) (hL : 0 ≤ L)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (z : ℝ) :
    (input N L R).evalReal (Fin.cons z (packCoefficients N d T.val)) ↔
      z ∈ QuadraticSpectral.historyLossSet N d T L R := by
  rw [QuadraticSpectral.historyLossSet_eq_scalarLossSet N d T L R (by exact_mod_cast hL)]
  have h := lossFormula_correct N
    (fun i => Expr.variable (Fin.castAdd (N*N) i).succ)
    (fun i j => Expr.variable (Fin.natAdd N (finProdFinEquiv (i,j))).succ)
    (.constant L) (.constant R) (.variable 0) (Fin.cons z (packCoefficients N d T.val))
  have hT : Matrix.map
      (fun i j : Fin N => (Expr.variable (Fin.natAdd N (finProdFinEquiv (i,j))).succ : Expr ((N+N*N)+1)))
      (Expr.evalReal (Fin.cons z (packCoefficients N d T.val))) = T.val := by
    ext i j
    change ((Fin.cons z (packCoefficients N d T.val)) : Fin ((N+N*N)+1) → ℝ) ((Fin.natAdd N (finProdFinEquiv (i,j))).succ) = T.val i j
    simp only [Fin.cons_succ,packCoefficients,Fin.addCases_right,matrixAssignment,Equiv.symm_apply_apply]
  rw [hT] at h
  simpa only [input,Expr.evalReal,Fin.cons_zero,Fin.cons_succ,packCoefficients,
    Fin.addCases_left] using h

/-- The same input with arbitrary real parameters in the layout [loss,L,R,d,T]. -/
def parametricInput (N : ℕ) : FirstOrder ((N+N*N)+3) :=
  lossFormula N
    (fun i => .variable (Fin.castAdd (N*N) i).succ.succ.succ)
    (fun i j => .variable (Fin.natAdd N (finProdFinEquiv (i,j))).succ.succ.succ)
    (.variable (Fin.succ 0)) (.variable (Fin.succ (Fin.succ 0))) (.variable 0)

theorem parametricInput_correct (N : ℕ) (L R : ℝ) (hL : 0 ≤ L)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) (z : ℝ) :
    (parametricInput N).evalReal (Fin.cons z (Fin.cons L (Fin.cons R (packCoefficients N d T.val)))) ↔
      z ∈ QuadraticSpectral.historyLossSet N d T L R := by
  rw [QuadraticSpectral.historyLossSet_eq_scalarLossSet N d T L R hL]
  have h := lossFormula_correct N
    (fun i => Expr.variable (Fin.castAdd (N*N) i).succ.succ.succ)
    (fun i j => Expr.variable (Fin.natAdd N (finProdFinEquiv (i,j))).succ.succ.succ)
    (.variable (Fin.succ 0)) (.variable (Fin.succ (Fin.succ 0))) (.variable 0)
    (Fin.cons z (Fin.cons L (Fin.cons R (packCoefficients N d T.val))))
  have hT : Matrix.map
      (fun i j : Fin N => (Expr.variable (Fin.natAdd N (finProdFinEquiv (i,j))).succ.succ.succ : Expr ((N+N*N)+3)))
      (Expr.evalReal (Fin.cons z (Fin.cons L (Fin.cons R (packCoefficients N d T.val))))) = T.val := by
    ext i j
    change ((Fin.cons z (Fin.cons L (Fin.cons R (packCoefficients N d T.val)))) : Fin ((N+N*N)+3) → ℝ)
      ((Fin.natAdd N (finProdFinEquiv (i,j))).succ.succ.succ) = T.val i j
    simp only [Fin.cons_succ,packCoefficients,Fin.addCases_right,matrixAssignment,Equiv.symm_apply_apply]
  rw [hT] at h
  simpa only [parametricInput,Expr.evalReal,Fin.cons_zero,Fin.cons_succ,packCoefficients,
    Fin.addCases_left] using h

end MemorySemialgebraic.SymbolicQE.QuadraticLossSyntax
