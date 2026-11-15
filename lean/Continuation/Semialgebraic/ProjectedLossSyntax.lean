module
public import Continuation.Semialgebraic.SymbolicGram
public import Continuation.Projected.LossModel
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Finite syntax for projected losses in a fixed Euclidean dimension

Domain and permitted-slope membership are supplied by rational polynomial formulas
whose additional free coordinates can represent algebraic coefficient parameters.
The projection graph is compiled from its variational characterization, with every
coordinate of the test point explicitly universally quantified.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE

namespace Expr
def substitute {n m : ℕ} (s : Fin n → Expr m) : Expr n → Expr m
  | .constant q => .constant q
  | .variable i => s i
  | .add p q => .add (substitute s p) (substitute s q)
  | .neg p => .neg (substitute s p)
  | .mul p q => .mul (substitute s p) (substitute s q)

@[simp] theorem substitute_correct {n m : ℕ} (s : Fin n → Expr m)
    (e : Expr n) (v : Fin m → ℝ) :
    (substitute s e).evalReal v = e.evalReal (fun i => (s i).evalReal v) := by
  induction e <;> simp_all only [substitute, evalReal]
end Expr

namespace Formula
def substitute {n m : ℕ} (s : Fin n → Expr m) : Formula n → Formula m
  | .eqZero p => .eqZero (p.substitute s)
  | .positive p => .positive (p.substitute s)
  | .nonnegative p => .nonnegative (p.substitute s)
  | .conj f g => .conj (substitute s f) (substitute s g)
  | .disj f g => .disj (substitute s f) (substitute s g)
  | .neg f => .neg (substitute s f)
  | .tru => .tru
  | .fls => .fls

@[simp] theorem substitute_correct {n m : ℕ} (s : Fin n → Expr m)
    (f : Formula n) (v : Fin m → ℝ) :
    (substitute s f).evalReal v ↔ f.evalReal (fun i => (s i).evalReal v) := by
  induction f <;> simp_all only [substitute, evalReal, Expr.substitute_correct]
end Formula

namespace FirstOrder
def allList {n : ℕ} : List (FirstOrder n) → FirstOrder n
  | [] => .atom .tru
  | f :: fs => .conj f (allList fs)

@[simp] theorem allList_correct {n : ℕ} (fs : List (FirstOrder n)) (v : Fin n → ℝ) :
    (allList fs).evalReal v ↔ ∀ f ∈ fs, f.evalReal v := by
  induction fs <;> simp_all only [allList, evalReal, Formula.evalReal, List.mem_cons,
    List.not_mem_nil, forall_false, implies_true, forall_eq_or_imp]
end FirstOrder

namespace ProjectedLossSyntax
open scoped InnerProductSpace
open Continuation.ProjectedSupport
variable {d n m : ℕ}

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def evalVector (v : Fin n → ℝ) (x : Fin d → Expr n) : Space d :=
  WithLp.toLp 2 (fun i => (x i).evalReal v)

@[simp] theorem evalVector_apply (v : Fin n → ℝ) (x : Fin d → Expr n) (i : Fin d) :
    evalVector v x i = (x i).evalReal v := rfl

def lift (k : ℕ) (e : Expr n) : Expr (k+n) := e.renameVariables (Fin.natAdd k)

@[simp] theorem lift_correct (k : ℕ) (e : Expr n) (a : Fin k → ℝ) (v : Fin n → ℝ) :
    (lift k e).evalReal (Fin.addCases a v) = e.evalReal v := by
  rw [lift, Expr.renameVariables_correct]
  congr 1
  funext i
  simp

def vectorSub (x y : Fin d → Expr n) : Fin d → Expr n := fun i => Expr.sub (x i) (y i)

@[simp] theorem evalVector_sub (v : Fin n → ℝ) (x y : Fin d → Expr n) :
    evalVector v (vectorSub x y) = evalVector v x - evalVector v y := by
  ext i
  change (Expr.sub (x i) (y i)).evalReal v = (x i).evalReal v - (y i).evalReal v
  rfl

def innerExpr (x y : Fin d → Expr n) : Expr n :=
  Expr.sumList (List.ofFn fun i => .mul (x i) (y i))

@[simp] theorem innerExpr_correct (v : Fin n → ℝ) (x y : Fin d → Expr n) :
    (innerExpr x y).evalReal v = ⟪evalVector v x, evalVector v y⟫_ℝ := by
  rw [innerExpr, Expr.eval_sumList_ofFn, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [-Expr.evalReal_refines, Expr.evalReal, evalVector, mul_comm]

noncomputable def domain (κ : Formula (d+n)) (v : Fin n → ℝ) : Set (Space d) :=
  {x | κ.evalReal (Fin.addCases (fun i => x i) v)}

def domainAt (κ : Formula (d+n)) (env : Fin n → Expr m) (x : Fin d → Expr m) : Formula m :=
  κ.substitute (Fin.addCases x env)

@[simp] theorem domainAt_correct (κ : Formula (d+n)) (env : Fin n → Expr m)
    (x : Fin d → Expr m) (v : Fin m → ℝ) :
    (domainAt κ env x).evalReal v ↔ evalVector v x ∈ domain κ (fun i => (env i).evalReal v) := by
  rw [domainAt, Formula.substitute_correct]
  change κ.evalReal _ ↔ κ.evalReal _
  have he : (fun i : Fin (d+n) => (Fin.addCases x env i : Expr m).evalReal v) =
      Fin.addCases (fun i => evalVector v x i) (fun i => (env i).evalReal v) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left, evalVector_apply]
    · intro j
      simp only [Fin.addCases_right]
  rw [he]

def projectionFormula (κ : Formula (d+n)) (env : Fin n → Expr m)
    (u x : Fin d → Expr m) : FirstOrder m :=
  .conj (.atom (domainAt κ env x))
    (FirstOrder.allBlock d m (.disj
      (.neg (.atom (domainAt κ (fun i => lift d (env i))
        (fun i => .variable (Fin.castAdd m i)))))
      (.atom (.nonnegative (.neg (innerExpr
        (vectorSub (fun i => lift d (u i)) (fun i => lift d (x i)))
        (vectorSub (fun i => .variable (Fin.castAdd m i)) (fun i => lift d (x i)))))))))

theorem projectionFormula_correct (κ : Formula (d+n)) (env : Fin n → Expr m)
    (u x : Fin d → Expr m) (v : Fin m → ℝ) :
    (projectionFormula κ env u x).evalReal v ↔
      ProjRelation (domain κ (fun i => (env i).evalReal v)) (evalVector v u) (evalVector v x) := by
  simp only [projectionFormula, FirstOrder.evalReal, domainAt_correct, FirstOrder.allBlock_correct,
    Formula.evalReal, Expr.evalReal, innerExpr_correct, evalVector_sub, lift_correct,
    neg_nonneg]
  have hl (a : Fin d → ℝ) (y : Fin d → Expr m) :
      evalVector (Fin.addCases a v) (fun i => lift d (y i)) = evalVector v y := by
    ext i
    exact lift_correct d (y i) a v
  have hv (a : Fin d → ℝ) :
      evalVector (Fin.addCases a v) (fun i => Expr.variable (Fin.castAdd m i)) = WithLp.toLp 2 a := by
    ext i
    simp [evalVector, Expr.evalReal]
  simp_rw [hl, hv]
  change (_ ∧ ∀ a : Fin d → ℝ, ¬ WithLp.toLp 2 a ∈ _ ∨ _) ↔ (_ ∧ ∀ y ∈ _, _)
  apply and_congr Iff.rfl
  constructor
  · intro h y hy
    exact (h (fun i => y i)).resolve_left (by simpa using hy)
  · intro h a
    by_cases ha : WithLp.toLp 2 a ∈ domain κ (fun i => (env i).evalReal v)
    · exact Or.inr (h _ ha)
    · exact Or.inl ha

def indices (N : ℕ) : List (Option (Fin (N+1))) := none :: (List.ofFn some)

@[simp] theorem mem_indices (N : ℕ) (i : Option (Fin (N+1))) : i ∈ indices N := by
  cases i with
  | none => exact List.mem_cons_self
  | some i => exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

def siteExpr {N : ℕ} (xStar : Fin d → Expr m) (x : Fin (N+1) → Fin d → Expr m) :
    Option (Fin (N+1)) → Fin d → Expr m
  | none => xStar
  | some i => x i

def slopeExpr {N : ℕ} (g : Fin (N+1) → Fin d → Expr m) :
    Option (Fin (N+1)) → Fin d → Expr m
  | none => fun _ => .constant 0
  | some i => g i

def valueExpr {N : ℕ} (φ : Fin (N+1) → Expr m) : Option (Fin (N+1)) → Expr m
  | none => .constant 0
  | some i => φ i

@[simp] theorem siteExpr_correct {N : ℕ} (xStar : Fin d → Expr m)
    (x : Fin (N+1) → Fin d → Expr m) (v : Fin m → ℝ) (i : Option (Fin (N+1))) :
    evalVector v (siteExpr xStar x i) =
      ProjectedLossModel.site (evalVector v xStar) (fun j => evalVector v (x j)) i := by
  cases i <;> rfl

@[simp] theorem slopeExpr_correct {N : ℕ} (g : Fin (N+1) → Fin d → Expr m)
    (v : Fin m → ℝ) (i : Option (Fin (N+1))) :
    evalVector v (slopeExpr g i) = ProjectedLossModel.slope (fun j => evalVector v (g j)) i := by
  cases i with
  | none => ext j; simp [-Expr.evalReal_refines, evalVector, slopeExpr, ProjectedLossModel.slope, Expr.evalReal]
  | some i => rfl

@[simp] theorem valueExpr_correct {N : ℕ} (φ : Fin (N+1) → Expr m)
    (v : Fin m → ℝ) (i : Option (Fin (N+1))) :
    (valueExpr φ i).evalReal v = ProjectedLossModel.val (fun j => (φ j).evalReal v) i := by
  cases i <;> simp [-Expr.evalReal_refines, valueExpr, ProjectedLossModel.val, Expr.evalReal]

def interpolationFormula {N : ℕ} (xStar : Fin d → Expr m)
    (x g : Fin (N+1) → Fin d → Expr m) (φ : Fin (N+1) → Expr m) : Formula m :=
  Formula.all ((indices N).map fun i => Formula.all ((indices N).map fun j =>
    .nonnegative (Expr.sub (valueExpr φ j) (.add (valueExpr φ i)
      (innerExpr (slopeExpr g i) (vectorSub (siteExpr xStar x j) (siteExpr xStar x i)))))))

theorem interpolationFormula_correct {N : ℕ} (xStar : Fin d → Expr m)
    (x g : Fin (N+1) → Fin d → Expr m) (φ : Fin (N+1) → Expr m) (v : Fin m → ℝ) :
    (interpolationFormula xStar x g φ).evalReal v ↔
      ∀ i j : Option (Fin (N+1)),
        ProjectedLossModel.val (fun k => (φ k).evalReal v) i +
          ⟪ProjectedLossModel.slope (fun k => evalVector v (g k)) i,
            ProjectedLossModel.site (evalVector v xStar) (fun k => evalVector v (x k)) j -
            ProjectedLossModel.site (evalVector v xStar) (fun k => evalVector v (x k)) i⟫_ℝ ≤
        ProjectedLossModel.val (fun k => (φ k).evalReal v) j := by
  simp only [interpolationFormula, Formula.all_eval, List.forall_mem_map,
    mem_indices, forall_const, Formula.evalReal, Expr.sub,
    Expr.evalReal, innerExpr_correct, evalVector_sub, siteExpr_correct, slopeExpr_correct,
    valueExpr_correct, ← sub_eq_add_neg, sub_nonneg]

def preExpr {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr m))
    (x g : Fin (N+1) → Fin d → Expr m) (k : Fin N) : Fin d → Expr m := fun i =>
  .add (.add (x k.castSucc i) (.mul (W k.succ k.castSucc) (g k.castSucc i)))
    (Expr.sumList (List.ofFn fun j : Fin k.val => .mul
      (Expr.sub (W k.succ ⟨j.val, by omega⟩) (W k.castSucc ⟨j.val, by omega⟩))
      (g ⟨j.val, by omega⟩ i)))

theorem preExpr_correct {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr m))
    (x g : Fin (N+1) → Fin d → Expr m) (k : Fin N) (v : Fin m → ℝ) :
    evalVector v (preExpr W x g k) = ProjectedLossModel.pre (W.map (Expr.evalReal v))
      (fun j => evalVector v (x j)) (fun j => evalVector v (g j)) k := by
  ext i
  simp [-Expr.evalReal_refines, evalVector, preExpr, ProjectedLossModel.pre, Expr.evalReal,
    Expr.sub, List.sum_ofFn, Function.comp_def, Matrix.map_apply, Finset.sum_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, sub_eq_add_neg]

def feasibleFormula {N : ℕ} (κ β : Formula (d+n)) (env : Fin n → Expr m)
    (R : Expr m) (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr m))
    (xStar : Fin d → Expr m) (x g : Fin (N+1) → Fin d → Expr m)
    (φ : Fin (N+1) → Expr m) : FirstOrder m :=
  .conj (.atom (domainAt κ env xStar))
    (.conj (.atom (Formula.all (List.ofFn fun i => domainAt κ env (x i))))
      (.conj (.atom (.nonnegative (Expr.sub (.mul R R)
        (innerExpr (vectorSub (x 0) xStar) (vectorSub (x 0) xStar)))))
        (.conj (.atom (Formula.all (List.ofFn fun i => domainAt β env (g i))))
          (.conj (.atom (interpolationFormula xStar x g φ))
            (FirstOrder.allList (List.ofFn fun k => projectionFormula κ env
              (preExpr W x g k) (x k.succ)))))))

theorem feasibleFormula_correct {N : ℕ} (κ β : Formula (d+n)) (env : Fin n → Expr m)
    (R : Expr m) (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr m))
    (xStar : Fin d → Expr m) (x g : Fin (N+1) → Fin d → Expr m)
    (φ : Fin (N+1) → Expr m) (v : Fin m → ℝ) :
    (feasibleFormula κ β env R W xStar x g φ).evalReal v ↔
      ProjectedLossModel.Feasible (W.map (Expr.evalReal v))
        (domain κ (fun i => (env i).evalReal v)) (domain β (fun i => (env i).evalReal v))
        (R.evalReal v) (evalVector v xStar) (fun i => evalVector v (x i))
        (fun i => evalVector v (g i)) (fun i => (φ i).evalReal v) := by
  simp only [feasibleFormula, FirstOrder.evalReal, domainAt_correct, Formula.all_ofFn_eval,
    Formula.evalReal, Expr.sub, Expr.evalReal, innerExpr_correct, evalVector_sub,
    real_inner_self_eq_norm_sq, ← sub_eq_add_neg, sub_nonneg, ← pow_two,
    interpolationFormula_correct, FirstOrder.allList_correct, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, projectionFormula_correct, preExpr_correct,
    ProjectedLossModel.Feasible]

def witnessSize (N d : ℕ) : ℕ := d + ((N+1)*d + ((N+1)*d + (N+1)))

def starSlot (N d : ℕ) (j : Fin d) : Fin (witnessSize N d) :=
  Fin.castAdd ((N+1)*d + ((N+1)*d + (N+1))) j

def pointSlot (N d : ℕ) (i : Fin (N+1)) (j : Fin d) : Fin (witnessSize N d) :=
  Fin.natAdd d (Fin.castAdd ((N+1)*d + (N+1)) (finProdFinEquiv (i,j)))

def slopeSlot (N d : ℕ) (i : Fin (N+1)) (j : Fin d) : Fin (witnessSize N d) :=
  Fin.natAdd d (Fin.natAdd ((N+1)*d) (Fin.castAdd (N+1) (finProdFinEquiv (i,j))))

def valueSlot (N d : ℕ) (i : Fin (N+1)) : Fin (witnessSize N d) :=
  Fin.natAdd d (Fin.natAdd ((N+1)*d) (Fin.natAdd ((N+1)*d) i))

noncomputable def unpackStar (N d : ℕ) (a : Fin (witnessSize N d) → ℝ) : Space d :=
  WithLp.toLp 2 (fun j => a (starSlot N d j))

noncomputable def unpackPoints (N d : ℕ) (a : Fin (witnessSize N d) → ℝ) :
    Fin (N+1) → Space d := fun i => WithLp.toLp 2 (fun j => a (pointSlot N d i j))

noncomputable def unpackSlopes (N d : ℕ) (a : Fin (witnessSize N d) → ℝ) :
    Fin (N+1) → Space d := fun i => WithLp.toLp 2 (fun j => a (slopeSlot N d i j))

def unpackValues (N d : ℕ) (a : Fin (witnessSize N d) → ℝ) : Fin (N+1) → ℝ :=
  fun i => a (valueSlot N d i)

def packWitness (N d : ℕ) (xStar : Space d) (x g : Fin (N+1) → Space d) (φ : Fin (N+1) → ℝ) :
    Fin (witnessSize N d) → ℝ :=
  Fin.addCases (fun j => xStar j)
    (Fin.addCases (fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      (Fin.addCases (fun k => g (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) φ))

@[simp] theorem unpackStar_pack (N d : ℕ) (xStar : Space d) (x g : Fin (N+1) → Space d)
    (φ : Fin (N+1) → ℝ) : unpackStar N d (packWitness N d xStar x g φ) = xStar := by
  ext j
  simp [unpackStar, packWitness, starSlot]

@[simp] theorem unpackPoints_pack (N d : ℕ) (xStar : Space d) (x g : Fin (N+1) → Space d)
    (φ : Fin (N+1) → ℝ) : unpackPoints N d (packWitness N d xStar x g φ) = x := by
  funext i
  ext j
  simp only [unpackPoints, packWitness, pointSlot, PiLp.toLp_apply,
    Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]

@[simp] theorem unpackSlopes_pack (N d : ℕ) (xStar : Space d) (x g : Fin (N+1) → Space d)
    (φ : Fin (N+1) → ℝ) : unpackSlopes N d (packWitness N d xStar x g φ) = g := by
  funext i
  ext j
  simp only [unpackSlopes, packWitness, slopeSlot, PiLp.toLp_apply,
    Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]

@[simp] theorem unpackValues_pack (N d : ℕ) (xStar : Space d) (x g : Fin (N+1) → Space d)
    (φ : Fin (N+1) → ℝ) : unpackValues N d (packWitness N d xStar x g φ) = φ := by
  funext i
  simp [unpackValues, packWitness, valueSlot]

def starVariables (N d n : ℕ) : Fin d → Expr (witnessSize N d+n) :=
  fun j => .variable (Fin.castAdd n (starSlot N d j))

def pointVariables (N d n : ℕ) : Fin (N+1) → Fin d → Expr (witnessSize N d+n) :=
  fun i j => .variable (Fin.castAdd n (pointSlot N d i j))

def slopeVariables (N d n : ℕ) : Fin (N+1) → Fin d → Expr (witnessSize N d+n) :=
  fun i j => .variable (Fin.castAdd n (slopeSlot N d i j))

def valueVariables (N d n : ℕ) : Fin (N+1) → Expr (witnessSize N d+n) :=
  fun i => .variable (Fin.castAdd n (valueSlot N d i))

@[simp] theorem starVariables_correct (N d n : ℕ) (a : Fin (witnessSize N d) → ℝ)
    (v : Fin n → ℝ) : evalVector (Fin.addCases a v) (starVariables N d n) = unpackStar N d a := by
  ext j
  simp [-Expr.evalReal_refines, evalVector, starVariables, Expr.evalReal, unpackStar]

@[simp] theorem pointVariables_correct (N d n : ℕ) (a : Fin (witnessSize N d) → ℝ)
    (v : Fin n → ℝ) (i : Fin (N+1)) :
    evalVector (Fin.addCases a v) (pointVariables N d n i) = unpackPoints N d a i := by
  ext j
  simp [-Expr.evalReal_refines, evalVector, pointVariables, Expr.evalReal, unpackPoints]

@[simp] theorem slopeVariables_correct (N d n : ℕ) (a : Fin (witnessSize N d) → ℝ)
    (v : Fin n → ℝ) (i : Fin (N+1)) :
    evalVector (Fin.addCases a v) (slopeVariables N d n i) = unpackSlopes N d a i := by
  ext j
  simp [-Expr.evalReal_refines, evalVector, slopeVariables, Expr.evalReal, unpackSlopes]

@[simp] theorem valueVariables_correct (N d n : ℕ) (a : Fin (witnessSize N d) → ℝ)
    (v : Fin n → ℝ) (i : Fin (N+1)) :
    (valueVariables N d n i).evalReal (Fin.addCases a v) = unpackValues N d a i := by
  simp [-Expr.evalReal_refines, valueVariables, Expr.evalReal, unpackValues]

def bodyFormula {N : ℕ} (κ β : Formula (d+n)) (R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) : FirstOrder (witnessSize N d+n) :=
  .conj (feasibleFormula κ β (fun i => lift (witnessSize N d) (.variable i))
    (lift (witnessSize N d) R) (fun i j => lift (witnessSize N d) (W i j))
    (starVariables N d n) (pointVariables N d n) (slopeVariables N d n) (valueVariables N d n))
    (.atom (.eqZero (Expr.sub (lift (witnessSize N d) z) (valueVariables N d n (Fin.last N)))))

theorem bodyFormula_correct {N : ℕ} (κ β : Formula (d+n)) (R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n))
    (a : Fin (witnessSize N d) → ℝ) (v : Fin n → ℝ) :
    (bodyFormula κ β R z W).evalReal (Fin.addCases a v) ↔
      ProjectedLossModel.Feasible (W.map (Expr.evalReal v)) (domain κ v) (domain β v)
        (R.evalReal v) (unpackStar N d a) (unpackPoints N d a) (unpackSlopes N d a)
        (unpackValues N d a) ∧ z.evalReal v = unpackValues N d a (Fin.last N) := by
  have hf := feasibleFormula_correct κ β (fun i => lift (witnessSize N d) (.variable i))
    (lift (witnessSize N d) R) (fun i j => lift (witnessSize N d) (W i j))
    (starVariables N d n) (pointVariables N d n) (slopeVariables N d n)
    (valueVariables N d n) (Fin.addCases a v)
  have hW : Matrix.map (fun i j => lift (witnessSize N d) (W i j))
      (Expr.evalReal (Fin.addCases a v)) = W.map (Expr.evalReal v) := by
    ext i j
    exact lift_correct (witnessSize N d) (W i j) a v
  simp only [lift_correct, Expr.evalReal, starVariables_correct, pointVariables_correct,
    slopeVariables_correct, valueVariables_correct, hW] at hf
  simp only [bodyFormula, FirstOrder.evalReal, Formula.evalReal, Expr.sub, Expr.evalReal,
    lift_correct, valueVariables_correct, ← sub_eq_add_neg, sub_eq_zero]
  exact and_congr hf Iff.rfl

/-- Quantify every finite projected trajectory witness. -/
def lossFormula {N : ℕ} (κ β : Formula (d+n)) (R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) : FirstOrder n :=
  FirstOrder.existsBlock (witnessSize N d) n (bodyFormula κ β R z W)

theorem lossFormula_model {N : ℕ} (κ β : Formula (d+n)) (R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) (v : Fin n → ℝ) :
    (lossFormula κ β R z W).evalReal v ↔
      z.evalReal v ∈ ProjectedLossModel.modelLossSet (W.map (Expr.evalReal v))
        (domain κ v) (domain β v) (R.evalReal v) := by
  rw [lossFormula, FirstOrder.existsBlock_correct]
  simp_rw [bodyFormula_correct]
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨unpackStar N d a, unpackPoints N d a, unpackSlopes N d a,
      unpackValues N d a, ha, hz⟩
  · rintro ⟨xStar,x,g,φ,hF,hz⟩
    refine ⟨packWitness N d xStar x g φ, ?_⟩
    simpa only [unpackStar_pack,unpackPoints_pack,unpackSlopes_pack,unpackValues_pack]
      using And.intro hF hz

/-- The compiled finite syntax describes exactly actual projected oracle losses. -/
theorem lossFormula_correct {N : ℕ} (κ β : Formula (d+n)) (R z : Expr n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) (Expr n)) (v : Fin n → ℝ)
    (hK : Convex ℝ (domain κ v)) (hcK : IsClosed (domain κ v)) (hneK : (domain κ v).Nonempty)
    (hB0 : (0 : Space d) ∈ domain β v) (hR : 0 ≤ R.evalReal v) :
    (lossFormula κ β R z W).evalReal v ↔
      z.evalReal v ∈ ProjectedLossModel.actualLossSet (B := domain β v) hK hcK hneK
        (W.map (Expr.evalReal v)) (R.evalReal v) := by
  rw [ProjectedLossModel.lossSet_eq hK hcK hneK hB0 hR]
  exact lossFormula_model κ β R z W v

end ProjectedLossSyntax
end MemorySemialgebraic.SymbolicQE
