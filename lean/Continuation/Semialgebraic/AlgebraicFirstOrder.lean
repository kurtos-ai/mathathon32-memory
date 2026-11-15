module
public import Continuation.Semialgebraic.AlgebraicSyntax
public import Continuation.Semialgebraic.FirstOrder
public meta import Continuation.Semialgebraic.AlgebraicSyntax
public meta import Continuation.Semialgebraic.FirstOrder

@[expose] public section
namespace MemorySemialgebraic.AlgebraicParameters
open SymbolicQE

namespace AlgebraicExpr
/-- Compile with explicit maps for coefficient and ordinary variable positions. -/
def compileWith {k n m : ℕ} (c : Fin k → Fin m) (v : Fin n → Fin m) : AlgebraicExpr k n → Expr m
  | .rational q => .constant q
  | .coefficient i => .variable (c i)
  | .variable j => .variable (v j)
  | .add p q => .add (compileWith c v p) (compileWith c v q)
  | .neg p => .neg (compileWith c v p)
  | .mul p q => .mul (compileWith c v p) (compileWith c v q)

@[simp] theorem compileWith_eval {k n m : ℕ} (c : Fin k → Fin m) (v : Fin n → Fin m)
    (ρ : Fin m → ℝ) (p : AlgebraicExpr k n) :
    Expr.evalReal ρ (compileWith c v p) = evalReal (ρ ∘ c) (ρ ∘ v) p := by
  induction p <;> simp_all [-Expr.evalReal_refines,compileWith,Expr.evalReal,evalReal,Function.comp_def]
end AlgebraicExpr

namespace AlgebraicFormula
def compileWith {k n m : ℕ} (c : Fin k → Fin m) (v : Fin n → Fin m) : AlgebraicFormula k n → Formula m
  | .eqZero p => .eqZero (p.compileWith c v)
  | .positive p => .positive (p.compileWith c v)
  | .nonnegative p => .nonnegative (p.compileWith c v)
  | .conj f g => .conj (compileWith c v f) (compileWith c v g)
  | .disj f g => .disj (compileWith c v f) (compileWith c v g)
  | .neg f => .neg (compileWith c v f)
  | .tru => .tru
  | .fls => .fls

@[simp] theorem compileWith_eval {k n m : ℕ} (c : Fin k → Fin m) (v : Fin n → Fin m)
    (ρ : Fin m → ℝ) (f : AlgebraicFormula k n) :
    Formula.evalReal ρ (compileWith c v f) ↔ evalReal (ρ ∘ c) (ρ ∘ v) f := by
  induction f <;> simp_all [-Expr.evalReal_refines,compileWith,Formula.evalReal,evalReal]
end AlgebraicFormula

/-- Arbitrary quantifier alternation with a finite specified algebraic coefficient table. -/
inductive AlgebraicFirstOrder (k : ℕ) : ℕ → Type where
  | atom {n : ℕ} : AlgebraicFormula k n → AlgebraicFirstOrder k n
  | conj {n : ℕ} : AlgebraicFirstOrder k n → AlgebraicFirstOrder k n → AlgebraicFirstOrder k n
  | disj {n : ℕ} : AlgebraicFirstOrder k n → AlgebraicFirstOrder k n → AlgebraicFirstOrder k n
  | neg {n : ℕ} : AlgebraicFirstOrder k n → AlgebraicFirstOrder k n
  | ex {n : ℕ} : AlgebraicFirstOrder k (n+1) → AlgebraicFirstOrder k n
  | all {n : ℕ} : AlgebraicFirstOrder k (n+1) → AlgebraicFirstOrder k n
  deriving Repr

namespace AlgebraicFirstOrder
noncomputable def evalReal {k n : ℕ} (a : Fin k → ℝ) (v : Fin n → ℝ) : AlgebraicFirstOrder k n → Prop
  | .atom f => f.evalReal a v
  | .conj f g => evalReal a v f ∧ evalReal a v g
  | .disj f g => evalReal a v f ∨ evalReal a v g
  | .neg f => ¬evalReal a v f
  | .ex f => ∃ x : ℝ, evalReal a (Fin.cons x v) f
  | .all f => ∀ x : ℝ, evalReal a (Fin.cons x v) f

/-- Shift old variables and preserve the new head variable at each quantifier. -/
def headMap {n m : ℕ} (v : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun j => (v j).succ)

lemma headMap_eval {n m : ℕ} (v : Fin n → Fin m) (ρ : Fin m → ℝ) (x : ℝ) :
    (Fin.cons x ρ) ∘ headMap v = Fin.cons x (ρ ∘ v) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [headMap,Function.comp_def]

lemma coefficientMap_eval {k m : ℕ} (c : Fin k → Fin m) (ρ : Fin m → ℝ) (x : ℝ) :
    (Fin.cons x ρ) ∘ (fun i => (c i).succ) = ρ ∘ c := by
  funext i
  simp [Function.comp_def]

def compileWith {k : ℕ} : {n m : ℕ} → (Fin k → Fin m) → (Fin n → Fin m) →
    AlgebraicFirstOrder k n → FirstOrder m
  | _,_,c,v,.atom f => .atom (f.compileWith c v)
  | _,_,c,v,.conj f g => .conj (compileWith c v f) (compileWith c v g)
  | _,_,c,v,.disj f g => .disj (compileWith c v f) (compileWith c v g)
  | _,_,c,v,.neg f => .neg (compileWith c v f)
  | _,_,c,v,.ex f => .ex (compileWith (fun i => (c i).succ) (headMap v) f)
  | _,_,c,v,.all f => .all (compileWith (fun i => (c i).succ) (headMap v) f)

/-- The compiler preserves every quantifier and all polynomial semantics. -/
theorem compileWith_eval {k n m : ℕ} (f : AlgebraicFirstOrder k n)
    (c : Fin k → Fin m) (v : Fin n → Fin m) (ρ : Fin m → ℝ) :
    FirstOrder.evalReal ρ (compileWith c v f) ↔ evalReal (ρ ∘ c) (ρ ∘ v) f := by
  induction f generalizing m with
  | atom f => exact AlgebraicFormula.compileWith_eval c v ρ f
  | conj f g ihf ihg => exact and_congr (ihf c v ρ) (ihg c v ρ)
  | disj f g ihf ihg => exact or_congr (ihf c v ρ) (ihg c v ρ)
  | neg f ih => exact not_congr (ih c v ρ)
  | ex f ih =>
    change (∃ x : ℝ, FirstOrder.evalReal (Fin.cons x ρ)
      (compileWith (fun i => (c i).succ) (headMap v) f)) ↔
      ∃ x : ℝ, evalReal (ρ ∘ c) (Fin.cons x (ρ ∘ v)) f
    apply exists_congr
    intro x
    simpa only [coefficientMap_eval,headMap_eval] using
      ih (fun i => (c i).succ) (headMap v) (Fin.cons x ρ)
  | all f ih =>
    change (∀ x : ℝ, FirstOrder.evalReal (Fin.cons x ρ)
      (compileWith (fun i => (c i).succ) (headMap v) f)) ↔
      ∀ x : ℝ, evalReal (ρ ∘ c) (Fin.cons x (ρ ∘ v)) f
    apply forall_congr'
    intro x
    simpa only [coefficientMap_eval,headMap_eval] using
      ih (fun i => (c i).succ) (headMap v) (Fin.cons x ρ)

def compile {k n : ℕ} (f : AlgebraicFirstOrder k n) : FirstOrder (k+n) :=
  compileWith (Fin.castAdd n) (Fin.natAdd k) f

@[simp] theorem compile_eval {k n : ℕ} (f : AlgebraicFirstOrder k n)
    (a : Fin k → ℝ) (v : Fin n → ℝ) :
    FirstOrder.evalReal (assignment a v) (compile f) ↔ evalReal a v f := by
  simpa only [compile,Function.comp_def,assignment_left,assignment_right] using
    compileWith_eval f (Fin.castAdd n) (Fin.natAdd k) (assignment a v)

def rationalBody {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k n) : FirstOrder (k+n) :=
  .conj (.atom (constraints cs)) (compile f)

/-- The same finite coefficient block works outside arbitrary quantifier alternation. -/
theorem rationalBody_exact {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k n)
    (v : Fin n → ℝ) :
    (∃ a : Fin k → ℝ, FirstOrder.evalReal (assignment a v) (rationalBody cs f)) ↔
      evalReal (fun i => (cs i).value) v f := by
  constructor
  · rintro ⟨a,ha,hf⟩
    have heq : a = fun i => (cs i).value := by
      apply funext
      simpa only [FirstOrder.evalReal,constraints_exact,assignment_left] using ha
    subst a
    exact (compile_eval _ _ _).mp hf
  · intro hf
    refine ⟨fun i => (cs i).value,?_,(compile_eval _ _ _).mpr hf⟩
    simp [FirstOrder.evalReal,constraints_exact]
end AlgebraicFirstOrder

end MemorySemialgebraic.AlgebraicParameters
