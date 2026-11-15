module
public import Continuation.Semialgebraic.EndpointRoots
public meta import Continuation.Semialgebraic.UnivariateDecision
public meta import Continuation.Semialgebraic.EndpointRoots

@[expose] public section
open Polynomial RootIsolation.SimpleRoots RootIsolation.Executable
namespace MemorySemialgebraic.EndpointSelection
open SymbolicQE

/-- Roots at which the threshold formula is false. For a strict upper ray, its endpoint
is the greatest such root. All tests in this definition use exact rational arithmetic. -/
def falseRootCells (f : Formula 1) : List IsoInterval :=
  let p := familyProduct f.atomPolys
  (intervals p).filter (fun I => !f.evalSigns (fun q => rootSign p q I))

lemma mem_falseRootCells (f : Formula 1) (I : IsoInterval) :
    I ∈ falseRootCells f ↔ I ∈ intervals (familyProduct f.atomPolys) ∧
      f.evalSigns (fun q => rootSign (familyProduct f.atomPolys) q I) = false := by
  simp [falseRootCells]

lemma eval_at_isolated_root (f : Formula 1) (I : IsoInterval)
    (hI : I ∈ intervals (familyProduct f.atomPolys)) (x : ℝ)
    (hx : (RootIsolation.Executable.denote (familyProduct f.atomPolys)).aeval x = 0)
    (hxI : x ∈ I.toSet) :
    f.evalSigns (fun q => rootSign (familyProduct f.atomPolys) q I) = true ↔
      Formula.evalReal (fun _ => x) f := by
  apply Formula.evalSigns_correct
  intro q hq
  exact rootSign_correct _ q (familyProduct_ne_zero _) (familyProduct_covers _ q hq) I hI x hx hxI

/-- Finite exact minimax output. A finite value is a rational polynomial and isolating cell.
`invalid` is possible on arbitrary non-ray input and is proved impossible for strict threshold sets. -/
inductive Output where
  | negInfinity
  | posInfinity
  | finite : Poly → IsoInterval → Output
  | invalid
  deriving DecidableEq, Repr

/-- Executable endpoint selection: classify the empty and full sets, then select the largest
false algebraic root by its rational isolating-cell center. -/
def select (f : Formula 1) : Output :=
  if f.decideExists then
    if f.decideForall then .negInfinity
    else match (falseRootCells f).argmax center with
      | none => .invalid
      | some I => .finite (familyProduct f.atomPolys) I
  else .posInfinity

theorem select_empty (f : Formula 1) (hf : ∀ x : ℝ, ¬ Formula.evalReal (fun _ => x) f) :
    select f = .posInfinity := by
  have h : f.decideExists = false := Bool.eq_false_iff.mpr (by
    intro htrue
    obtain ⟨x,hx⟩ := (Formula.decideExists_correct f).mp htrue
    exact hf x hx)
  simp [select,h]

theorem select_full (f : Formula 1) (hf : ∀ x : ℝ, Formula.evalReal (fun _ => x) f) :
    select f = .negInfinity := by
  have he := (Formula.decideExists_correct f).mpr ⟨0,hf 0⟩
  have ha := (Formula.decideForall_correct f).mpr hf
  simp [select,he,ha]

/-- The output for a finite strict upper ray is a certified isolating code of its exact endpoint. -/
theorem select_ray (f : Formula 1) (v : ℝ)
    (hf : ∀ x : ℝ, Formula.evalReal (fun _ => x) f ↔ v < x) :
    ∃ I, select f = .finite (familyProduct f.atomPolys) I ∧
      I ∈ intervals (familyProduct f.atomPolys) ∧
      (RootIsolation.Executable.denote (familyProduct f.atomPolys)).aeval v = 0 ∧ v ∈ I.toSet := by
  let p := familyProduct f.atomPolys
  have hp : RootIsolation.Executable.denote p ≠ 0 := familyProduct_ne_zero _
  have hv : (RootIsolation.Executable.denote p).aeval v = 0 := ray_endpoint_is_root f v hf
  obtain ⟨I,hI,hvI⟩ := every_root_mem_intervals p hp v hv
  have hIfalse : I ∈ falseRootCells f := by
    apply (mem_falseRootCells f I).mpr
    refine ⟨hI,Bool.eq_false_iff.mpr ?_⟩
    intro htrue
    have hvf := (eval_at_isolated_root f I hI v hv hvI).mp htrue
    exact lt_irrefl v ((hf v).mp hvf)
  have hne : falseRootCells f ≠ [] := by
    intro he
    simpa [he] using hIfalse
  have hargne : (falseRootCells f).argmax center ≠ none := by
    intro hnone
    exact hne (List.argmax_eq_none.mp hnone)
  obtain ⟨J,hJ⟩ : ∃ J, (falseRootCells f).argmax center = some J := by
    cases h : (falseRootCells f).argmax center with
    | none => exact (hargne h).elim
    | some J => exact ⟨J,rfl⟩
  have hJfalse := (mem_falseRootCells f J).mp (List.argmax_mem hJ)
  obtain ⟨x,hx,huniq⟩ := existsUnique_root_of_mem_intervals p hp J hJfalse.1
  have hxle : x ≤ v := by
    apply le_of_not_gt
    intro hvx
    have he := (eval_at_isolated_root f J hJfalse.1 x hx.1 hx.2).mpr ((hf x).mpr hvx)
    rw [hJfalse.2] at he
    contradiction
  have hxv : x = v := by
    by_contra hne
    have hxlt : x < v := lt_of_le_of_ne hxle hne
    have hJI : J ≠ I := by
      intro he
      subst J
      exact hne (RootIsolation.Executable.roots_eq_of_mem_interval p hp I hI x v
        hx.1 hv hx.2 hvI)
    have hc := center_lt_of_disjoint J I x v hx.2 hvI
      (disjoint_intervals_of_ne p hp J I hJfalse.1 hI hJI) hxlt
    exact (not_lt_of_ge (List.le_of_mem_argmax hIfalse hJ)) hc
  have he := (Formula.decideExists_correct f).mpr ⟨v+1,(hf _).mpr (by linarith)⟩
  have ha : f.decideForall = false := Bool.eq_false_iff.mpr (by
    intro htrue
    have hall := (Formula.decideForall_correct f).mp htrue
    exact lt_irrefl v ((hf v).mp (hall v)))
  refine ⟨J,?_,hJfalse.1,hv,?_⟩
  · simp [select,he,ha,hJ]
  · simpa only [hxv] using hx.2

/-- The independent extended minimax value denoted by a finite algorithm output. -/
def Output.Denotes : Output → EReal → Prop
  | .negInfinity, v => v = ⊥
  | .posInfinity, v => v = ⊤
  | .finite p I, v => RootIsolation.Executable.denote p ≠ 0 ∧ I ∈ intervals p ∧
      ∃ x : ℝ, v = (x : EReal) ∧ (RootIsolation.Executable.denote p).aeval x = 0 ∧ x ∈ I.toSet
  | .invalid, _ => False

/-- Exact rational threshold descriptions compose with root isolation and sign decision to
compute the independently defined extended minimax value. No endpoint is supplied to the algorithm. -/
theorem select_minimax {D T Z : Type*}
    (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ) (f : Formula 1)
    (hf : f.toQF.solutionSet1 = MemoryDecision.thresholds feasible loss memory m) :
    (select f).Denotes (MemoryDecision.value feasible loss memory m) := by
  let V := MemoryDecision.value feasible loss memory m
  have hsem (x : ℝ) : Formula.evalReal (fun _ => x) f ↔ V < (x:EReal) := by
    have he := congrArg (fun s : Set ℝ => x ∈ s) hf
    simpa only [QFFormula.solutionSet1,Set.mem_setOf_eq,Formula.toQF_refines,
      MemoryDecision.threshold_iff_value_lt] using (Iff.of_eq he)
  by_cases htop : V = ⊤
  · have ho : select f = .posInfinity := select_empty f (by
      intro x
      rw [hsem,htop]
      exact not_lt_of_ge le_top)
    simpa only [ho,Output.Denotes] using htop
  by_cases hbot : V = ⊥
  · have ho : select f = .negInfinity := select_full f (by
      intro x
      rw [hsem,hbot]
      exact EReal.bot_lt_coe x)
    simpa only [ho,Output.Denotes] using hbot
  have hcoe : (V.toReal:EReal) = V := EReal.coe_toReal htop hbot
  have hray (x : ℝ) : Formula.evalReal (fun _ => x) f ↔ V.toReal < x := by
    calc
      _ ↔ (V.toReal:EReal) < (x:EReal) := by rw [hcoe]; exact hsem x
      _ ↔ _ := EReal.coe_lt_coe_iff
  obtain ⟨I,hout,hI,hroot,hmem⟩ := select_ray f V.toReal hray
  rw [hout]
  exact ⟨familyProduct_ne_zero _,hI,V.toReal,hcoe.symm,hroot,hmem⟩

end MemorySemialgebraic.EndpointSelection
