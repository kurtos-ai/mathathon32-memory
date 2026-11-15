module
public import Continuation.Semialgebraic.AlgebraicReduction
public meta import Continuation.Semialgebraic.AlgebraicReduction

@[expose] public section
open Polynomial RootIsolation.SimpleRoots RootIsolation.Executable
namespace MemorySemialgebraic.EndpointSelection
open SymbolicQE AlgebraicParameters

abbrev QEStep := {n : ℕ} → Formula (n+1) → Formula n

def StepCorrect (step : QEStep) : Prop :=
  ∀ {n : ℕ} (f : Formula (n+1)) (v : Fin n → ℝ),
    (step f).evalReal v ↔ ∃ x : ℝ, f.evalReal (Fin.cons x v)

/-- Decide a closed rational formula after the supplied rational QE algorithm. -/
def decideClosed (step : QEStep) (f : FirstOrder 0) : Bool :=
  (FirstOrder.eliminate step f).evalRat Fin.elim0

theorem decideClosed_correct (step : QEStep) (hstep : StepCorrect step) (f : FirstOrder 0) :
    decideClosed step f = true ↔ f.evalReal Fin.elim0 := by
  rw [decideClosed,Formula.evalRat_refines,FirstOrder.eliminate_correct step hstep]
  have hv : (fun i : Fin 0 => ((Fin.elim0 i : ℚ) : ℝ)) = (Fin.elim0 : Fin 0 → ℝ) := by
    funext i
    exact Fin.elim0 i
  rw [hv]

/-- An unchecked rational root specification; soundness uses the certified output invariant. -/
def rootConstraint {n : ℕ} (p : Poly) (I : IsoInterval) (x : Expr n) : Formula n :=
  .conj (.eqZero (polynomialAt p x)) (cellConstraint I x)

lemma rootConstraint_eval {n : ℕ} (p : Poly) (I : IsoInterval) (x : Expr n) (v : Fin n → ℝ) :
    (rootConstraint p I x).evalReal v ↔
      (RootIsolation.Executable.denote p).aeval (x.evalReal v) = 0 ∧ x.evalReal v ∈ I.toSet := by
  simp only [rootConstraint,Formula.evalReal,polynomialAt_eval,cellConstraint_eval]

/-- A literal closed rational formula comparing two isolated algebraic roots. -/
def rootLessFormula (p : Poly) (I : IsoInterval) (q : Poly) (J : IsoInterval) : FirstOrder 0 :=
  .ex (.ex (.atom (.conj (rootConstraint p I (.variable 1))
    (.conj (rootConstraint q J (.variable 0))
      (.positive (.sub (.variable 0) (.variable 1)))))))

lemma rootLessFormula_eval (p : Poly) (I : IsoInterval) (q : Poly) (J : IsoInterval) :
    (rootLessFormula p I q J).evalReal Fin.elim0 ↔
      ∃ x y : ℝ, ((RootIsolation.Executable.denote p).aeval x = 0 ∧ x ∈ I.toSet) ∧
        ((RootIsolation.Executable.denote q).aeval y = 0 ∧ y ∈ J.toSet) ∧ x < y := by
  simp [-Expr.evalReal_refines,rootLessFormula,FirstOrder.evalReal,Formula.evalReal,
    rootConstraint_eval,Expr.sub,Expr.evalReal,← sub_eq_add_neg,sub_pos]

lemma compare_roots_correct (step : QEStep) (hstep : StepCorrect step)
    (p : Poly) (I : IsoInterval) (q : Poly) (J : IsoInterval)
    (hp : RootIsolation.Executable.denote p ≠ 0) (hI : I ∈ intervals p)
    (hq : RootIsolation.Executable.denote q ≠ 0) (hJ : J ∈ intervals q)
    (x y : ℝ) (hx : (RootIsolation.Executable.denote p).aeval x = 0 ∧ x ∈ I.toSet)
    (hy : (RootIsolation.Executable.denote q).aeval y = 0 ∧ y ∈ J.toSet) :
    decideClosed step (rootLessFormula p I q J) = true ↔ x < y := by
  rw [decideClosed_correct step hstep,rootLessFormula_eval]
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    have hax := roots_eq_of_mem_interval p hp I hI a x ha.1 hx.1 ha.2 hx.2
    have hby := roots_eq_of_mem_interval q hq J hJ b y hb.1 hy.1 hb.2 hy.2
    simpa only [hax,hby] using hab
  · intro h
    exact ⟨x,y,hx,hy,h⟩

/-- Invalid input is explicit. Every valid comparison uses only finite rational formulas. -/
def compareOutputs (step : QEStep) : Output → Output → Option Ordering
  | .invalid,_ => none
  | _,.invalid => none
  | .negInfinity,.negInfinity => some .eq
  | .posInfinity,.posInfinity => some .eq
  | .negInfinity,_ => some .lt
  | _,.negInfinity => some .gt
  | .posInfinity,_ => some .gt
  | _,.posInfinity => some .lt
  | .finite p I,.finite q J =>
      if decideClosed step (rootLessFormula p I q J) then some .lt
      else if decideClosed step (rootLessFormula q J p I) then some .gt else some .eq

noncomputable def valueOrdering (u v : EReal) : Ordering :=
  if u < v then .lt else if v < u then .gt else .eq

lemma valueOrdering_lt (u v : EReal) : valueOrdering u v = .lt ↔ u < v := by
  by_cases h : u < v <;> simp [valueOrdering,h]

lemma valueOrdering_eq (u v : EReal) : valueOrdering u v = .eq ↔ u = v := by
  by_cases h : u < v
  · simp [valueOrdering,h,ne_of_lt h]
  by_cases h' : v < u
  · simp [valueOrdering,h,h',ne_of_gt h']
  have he : u = v := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
  simp [valueOrdering,h,h',he]

/-- Certified endpoint codes are compared according to their independent extended real values. -/
theorem compareOutputs_correct (step : QEStep) (hstep : StepCorrect step)
    (a b : Output) (u v : EReal) (ha : a.Denotes u) (hb : b.Denotes v) :
    compareOutputs step a b = some (valueOrdering u v) := by
  cases a with
  | invalid => exact ha.elim
  | negInfinity =>
    change u = ⊥ at ha
    subst u
    cases b with
    | invalid => exact hb.elim
    | negInfinity => change v = ⊥ at hb; subst v; simp [compareOutputs,valueOrdering]
    | posInfinity => change v = ⊤ at hb; subst v; simp [compareOutputs,valueOrdering]
    | finite q J =>
      obtain ⟨_,_,y,rfl,_,_⟩ := hb
      simp [compareOutputs,valueOrdering]
  | posInfinity =>
    change u = ⊤ at ha
    subst u
    cases b with
    | invalid => exact hb.elim
    | negInfinity => change v = ⊥ at hb; subst v; simp [compareOutputs,valueOrdering]
    | posInfinity => change v = ⊤ at hb; subst v; simp [compareOutputs,valueOrdering]
    | finite q J =>
      obtain ⟨_,_,y,rfl,_,_⟩ := hb
      simp [compareOutputs,valueOrdering]
  | finite p I =>
    obtain ⟨hp,hI,x,rfl,hx,hxI⟩ := ha
    cases b with
    | invalid => exact hb.elim
    | negInfinity => change v = ⊥ at hb; subst v; simp [compareOutputs,valueOrdering]
    | posInfinity => change v = ⊤ at hb; subst v; simp [compareOutputs,valueOrdering]
    | finite q J =>
      obtain ⟨hq,hJ,y,rfl,hy,hyJ⟩ := hb
      have hab := compare_roots_correct step hstep p I q J hp hI hq hJ x y ⟨hx,hxI⟩ ⟨hy,hyJ⟩
      have hba := compare_roots_correct step hstep q J p I hq hJ hp hI y x ⟨hy,hyJ⟩ ⟨hx,hxI⟩
      simp only [compareOutputs,hab,hba,valueOrdering,EReal.coe_lt_coe_iff]
      split_ifs <;> rfl

lemma compareOutputs_none_iff (step : QEStep) (a b : Output) :
    compareOutputs step a b = none ↔ a = .invalid ∨ b = .invalid := by
  cases a <;> cases b <;> simp [compareOutputs]
  split_ifs <;> simp

/-- A total executable equality test; malformed inputs return false. -/
def equalOutputs (step : QEStep) (a b : Output) : Bool :=
  decide (compareOutputs step a b = some .eq)

theorem equalOutputs_correct (step : QEStep) (hstep : StepCorrect step)
    (a b : Output) (u v : EReal) (ha : a.Denotes u) (hb : b.Denotes v) :
    equalOutputs step a b = true ↔ u = v := by
  simp only [equalOutputs,decide_eq_true_eq,compareOutputs_correct step hstep a b u v ha hb,
    Option.some.injEq,valueOrdering_eq]

/-- Decide whether the next budget strictly improves the current endpoint. -/
def strictGain (step : QEStep) (current next : Output) : Bool :=
  decide (compareOutputs step next current = some .lt)

theorem strictGain_correct (step : QEStep) (hstep : StepCorrect step)
    (current next : Output) (u v : EReal) (hu : current.Denotes u) (hv : next.Denotes v) :
    strictGain step current next = true ↔ v < u := by
  simp only [strictGain,decide_eq_true_eq,compareOutputs_correct step hstep next current v u hv hu,
    Option.some.injEq,valueOrdering_lt]

/-- Concrete threshold descriptions decide strict gain without receiving either minimax value. -/
theorem strictGain_thresholds {D T Z : Type*} (step : QEStep) (hstep : StepCorrect step)
    (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ) (f g : Formula 1)
    (hf : f.toQF.solutionSet1 = MemoryDecision.thresholds feasible loss memory m)
    (hg : g.toQF.solutionSet1 = MemoryDecision.thresholds feasible loss memory (m+1)) :
    strictGain step (select f) (select g) = true ↔
      MemoryDecision.value feasible loss memory (m+1) < MemoryDecision.value feasible loss memory m :=
  strictGain_correct step hstep _ _ _ _ (select_minimax _ _ _ _ _ hf) (select_minimax _ _ _ _ _ hg)

end MemorySemialgebraic.EndpointSelection
