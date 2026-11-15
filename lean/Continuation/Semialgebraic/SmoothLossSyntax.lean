module
public import Continuation.Semialgebraic.SmoothGramSyntax
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.SmoothLossSyntax
open Matrix SmoothGramModel

def witnessSize (N : ℕ) : ℕ := (N+2)*(N+2)+(N+1)

def gramSlot (N : ℕ) (i j : Index N) : Fin (witnessSize N) :=
  Fin.castAdd (N+1) (finProdFinEquiv
    ((finSuccEquiv (N+1)).symm i,(finSuccEquiv (N+1)).symm j))

def valueSlot (N : ℕ) (i : Fin (N+1)) : Fin (witnessSize N) :=
  Fin.natAdd ((N+2)*(N+2)) i

def unpackGram (N : ℕ) (a : Fin (witnessSize N) → ℝ) : Matrix (Index N) (Index N) ℝ :=
  fun i j => a (gramSlot N i j)

def unpackValues (N : ℕ) (a : Fin (witnessSize N) → ℝ) : Fin (N+1) → ℝ :=
  fun i => a (valueSlot N i)

/-- Explicit coordinates for arbitrary Gram entries and function values. -/
def packWitness (N : ℕ) (M : Matrix (Index N) (Index N) ℝ) (φ : Fin (N+1) → ℝ) :
    Fin (witnessSize N) → ℝ :=
  Fin.addCases (fun k => M (finSuccEquiv (N+1) (finProdFinEquiv.symm k).1)
    (finSuccEquiv (N+1) (finProdFinEquiv.symm k).2)) φ

@[simp] theorem unpackGram_pack (N : ℕ) (M : Matrix (Index N) (Index N) ℝ)
    (φ : Fin (N+1) → ℝ) : unpackGram N (packWitness N M φ)=M := by
  ext i j
  simp only [unpackGram,gramSlot,packWitness,Fin.addCases_left,
    Equiv.symm_apply_apply,Equiv.apply_symm_apply]

@[simp] theorem unpackValues_pack (N : ℕ) (M : Matrix (Index N) (Index N) ℝ)
    (φ : Fin (N+1) → ℝ) : unpackValues N (packWitness N M φ)=φ := by
  funext i
  simp [unpackValues,valueSlot,packWitness]

def liftExpr {n : ℕ} (k : ℕ) (e : Expr n) : Expr (k+n) := e.renameVariables (Fin.natAdd k)

@[simp] theorem liftExpr_correct {n : ℕ} (k : ℕ) (e : Expr n)
    (a : Fin k → ℝ) (v : Fin n → ℝ) :
    (liftExpr k e).evalReal (Fin.addCases a v)=e.evalReal v := by
  rw [liftExpr,Expr.renameVariables_correct]
  congr 1
  funext i
  simp

def gramVariables (N n : ℕ) : Matrix (Index N) (Index N) (Expr (witnessSize N+n)) :=
  fun i j => .variable (Fin.castAdd n (gramSlot N i j))

def valueVariables (N n : ℕ) : Fin (N+1) → Expr (witnessSize N+n) :=
  fun i => .variable (Fin.castAdd n (valueSlot N i))

@[simp] theorem gramVariables_correct (N n : ℕ) (a : Fin (witnessSize N) → ℝ)
    (v : Fin n → ℝ) :
    (gramVariables N n).map (Expr.evalReal (Fin.addCases a v))=unpackGram N a := by
  ext i j
  simp only [gramVariables,Matrix.map_apply,Expr.evalReal,Fin.addCases_left,unpackGram]

@[simp] theorem valueVariables_correct (N n : ℕ) (a : Fin (witnessSize N) → ℝ)
    (v : Fin n → ℝ) (i : Fin (N+1)) :
    (valueVariables N n i).evalReal (Fin.addCases a v)=unpackValues N a i := by
  simp only [valueVariables,Expr.evalReal,Fin.addCases_left,unpackValues]

/-- Polynomial Gram feasibility and equality to the selected terminal loss. -/
def bodyFormula {N n : ℕ} (L R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) : FirstOrder (witnessSize N+n) :=
  .conj (SmoothGramSyntax.feasibleFormula (liftExpr (witnessSize N) L)
    (liftExpr (witnessSize N) R) (fun i j => liftExpr (witnessSize N) (W i j))
    (gramVariables N n) (valueVariables N n))
    (.atom (.eqZero (Expr.sub (liftExpr (witnessSize N) z) (valueVariables N n (Fin.last N)))))

theorem bodyFormula_correct {N n : ℕ} (L R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n))
    (a : Fin (witnessSize N) → ℝ) (v : Fin n → ℝ) (hL : 0<L.evalReal v) :
    (bodyFormula L R z W).evalReal (Fin.addCases a v) ↔
      Feasible (W.map (Expr.evalReal v)) (L.evalReal v) (R.evalReal v)
        (unpackGram N a) (unpackValues N a) ∧ z.evalReal v=unpackValues N a (Fin.last N) := by
  have hl : 0<(liftExpr (witnessSize N) L).evalReal (Fin.addCases a v) := by
    simpa only [liftExpr_correct] using hL
  have hf := SmoothGramSyntax.feasibleFormula_correct
    (liftExpr (witnessSize N) L) (liftExpr (witnessSize N) R)
    (fun i j => liftExpr (witnessSize N) (W i j))
    (gramVariables N n) (valueVariables N n) (Fin.addCases a v) hl
  have hW : Matrix.map (fun i j => liftExpr (witnessSize N) (W i j))
        (Expr.evalReal (Fin.addCases a v)) = W.map (Expr.evalReal v) := by
    ext i j
    exact liftExpr_correct (witnessSize N) (W i j) a v
  simp only [liftExpr_correct,gramVariables_correct,valueVariables_correct,hW] at hf
  simp only [bodyFormula,FirstOrder.evalReal,Formula.evalReal,Expr.sub,Expr.evalReal,
    liftExpr_correct,valueVariables_correct,← sub_eq_add_neg,sub_eq_zero]
  exact and_congr hf Iff.rfl


/-- Executable first-order syntax for attainable smooth losses, with every Gram witness quantified. -/
def lossFormula {N n : ℕ} (L R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) : FirstOrder n :=
  FirstOrder.existsBlock (witnessSize N) n (bodyFormula L R z W)

theorem lossFormula_model {N n : ℕ} (L R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) (v : Fin n → ℝ)
    (hL : 0<L.evalReal v) :
    (lossFormula L R z W).evalReal v ↔
      z.evalReal v ∈ modelLossSet N (W.map (Expr.evalReal v)) (L.evalReal v) (R.evalReal v) := by
  rw [lossFormula,FirstOrder.existsBlock_correct]
  simp_rw [bodyFormula_correct L R z W _ v hL]
  constructor
  · rintro ⟨a,ha,hz⟩
    exact ⟨unpackGram N a,unpackValues N a,ha,hz⟩
  · rintro ⟨M,φ,hF,hz⟩
    refine ⟨packWitness N M φ,?_⟩
    simpa only [unpackGram_pack,unpackValues_pack] using And.intro hF hz

/-- Exact actual-function semantics, including minimizer interpolation and the prescribed radius. -/
theorem lossFormula_correct {N n : ℕ} (L R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) (v : Fin n → ℝ)
    (hL : 0<L.evalReal v) (hR : 0≤R.evalReal v) :
    (lossFormula L R z W).evalReal v ↔
      z.evalReal v ∈ actualLossSet N (W.map (Expr.evalReal v)) (L.evalReal v) (R.evalReal v) := by
  rw [actualLossSet_eq_modelLossSet N _ _ _ hL hR]
  exact lossFormula_model L R z W v hL

end MemorySemialgebraic.SymbolicQE.SmoothLossSyntax
