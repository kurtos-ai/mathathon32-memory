module
public import Continuation.Semialgebraic.EndpointComparison
public import Continuation.Semialgebraic.ProcedureCoefficients
public meta import Continuation.Semialgebraic.EndpointComparison
public meta import Continuation.Semialgebraic.ProcedureCoefficients

@[expose] public section
namespace MemorySemialgebraic.MemorySelection
open EndpointSelection SymbolicQE AlgebraicParameters

/-- The actual coordinate memory class; this is the predicate compiled by methodMemoryFormula. -/
def memory (N m : ℕ) : Set (RealizationCore.StrictIncrement N) :=
  {T | MemoryRank.Incremental.Q N m T.val}

/-- The stated finite bound exhausts every coefficient method, for any loss model. -/
theorem memory_saturated (N m : ℕ) (hm : N/2 ≤ m) : memory N m = Set.univ := by
  apply Set.eq_univ_of_forall
  intro T k hk hkN
  have hw := MemoryRank.Incremental.S_k_rank_le_width N k T.val
  have hh := MemoryRank.Incremental.S_k_rank_le_height N k T.val
  omega

noncomputable def unrestrictedValue {N : ℕ} {Z : Type*}
    (feasible : (Fin N → ℝ) → RealizationCore.StrictIncrement N → Z → Prop)
    (loss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → Z → ℝ) : EReal :=
  ⨅ T, ⨅ d, MemoryDecision.risk feasible loss d T

theorem value_eq_unrestricted {N : ℕ} {Z : Type*}
    (feasible : (Fin N → ℝ) → RealizationCore.StrictIncrement N → Z → Prop)
    (loss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → Z → ℝ)
    (m : ℕ) (hm : N/2 ≤ m) :
    MemoryDecision.value feasible loss (memory N) m = unrestrictedValue feasible loss := by
  apply le_antisymm
  · apply le_iInf
    intro T
    apply le_iInf
    intro d
    have ht : T ∈ memory N m := by rw [memory_saturated N m hm]; trivial
    exact iInf_le_of_le ⟨T,ht⟩ (iInf_le _ d)
  · apply le_iInf
    intro T
    apply le_iInf
    intro d
    exact iInf_le_of_le T.val (iInf_le _ d)

/-- Compare a budget with the last, unrestricted budget. Out-of-range and malformed inputs fail. -/
def budgetMatches (step : QEStep) (cap : ℕ) (outputs : Fin (cap+1) → Output) (m : ℕ) : Bool :=
  if hm : m ≤ cap then equalOutputs step (outputs ⟨m,by omega⟩) (outputs (Fin.last cap)) else false

/-- Scan the finite budget range in order, using only the computed endpoint codes. -/
def leastBudget (step : QEStep) (cap : ℕ) (outputs : Fin (cap+1) → Output) : Option ℕ :=
  (List.range (cap+1)).find? (budgetMatches step cap outputs)

lemma budgetMatches_correct (step : QEStep) (hstep : StepCorrect step) (cap : ℕ)
    (outputs : Fin (cap+1) → Output) (values : Fin (cap+1) → EReal)
    (hout : ∀ i, (outputs i).Denotes (values i)) (m : ℕ) (hm : m ≤ cap) :
    budgetMatches step cap outputs m = true ↔ values ⟨m,by omega⟩ = values (Fin.last cap) := by
  simp only [budgetMatches,dif_pos hm]
  exact equalOutputs_correct step hstep _ _ _ _ (hout _) (hout _)

/-- The scan returns the least index with the final endpoint; that endpoint itself guarantees success. -/
theorem leastBudget_correct (step : QEStep) (hstep : StepCorrect step) (cap : ℕ)
    (outputs : Fin (cap+1) → Output) (values : Fin (cap+1) → EReal)
    (hout : ∀ i, (outputs i).Denotes (values i)) :
    ∃ m : Fin (cap+1), leastBudget step cap outputs = some m.val ∧
      IsLeast {j : Fin (cap+1) | values j = values (Fin.last cap)} m := by
  have hend : budgetMatches step cap outputs cap = true :=
    (budgetMatches_correct step hstep cap outputs values hout cap le_rfl).mpr rfl
  have hne : leastBudget step cap outputs ≠ none := by
    intro hnone
    have h := (List.find?_range_eq_none.mp hnone) cap (by omega)
    simp [hend] at h
  obtain ⟨m,hm⟩ : ∃ m, leastBudget step cap outputs = some m := by
    cases h : leastBudget step cap outputs with
    | none => exact (hne h).elim
    | some m => exact ⟨m,rfl⟩
  obtain ⟨hmatch,hmem,hprev⟩ := List.find?_range_eq_some.mp hm
  have hmlt : m < cap+1 := List.mem_range.mp hmem
  refine ⟨⟨m,hmlt⟩,hm,?_,?_⟩
  · exact (budgetMatches_correct step hstep cap outputs values hout m (by omega)).mp hmatch
  · intro j hj
    change m ≤ j.val
    by_contra! hjm
    have hjmatch := (budgetMatches_correct step hstep cap outputs values hout j.val
      (by omega)).mpr hj
    have h := hprev j.val hjm
    simp [hjmatch] at h

/-- The end-to-end finite-budget selector accepts threshold formulas, never minimax values. -/
def leastSufficientBudget (step : QEStep) (N : ℕ)
    (formulas : Fin (N/2+1) → Formula 1) : Option ℕ :=
  leastBudget step (N/2) (fun m => select (formulas m))

/-- Its returned budget is the least natural budget attaining the independent unrestricted value. -/
theorem leastSufficientBudget_correct {N : ℕ} {Z : Type*}
    (step : QEStep) (hstep : StepCorrect step)
    (feasible : (Fin N → ℝ) → RealizationCore.StrictIncrement N → Z → Prop)
    (loss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → Z → ℝ)
    (formulas : Fin (N/2+1) → Formula 1)
    (hformulas : ∀ m, (formulas m).toQF.solutionSet1 =
      MemoryDecision.thresholds feasible loss (memory N) m.val) :
    ∃ m ≤ N/2, leastSufficientBudget step N formulas = some m ∧
      IsLeast {j : ℕ | MemoryDecision.value feasible loss (memory N) j =
        unrestrictedValue feasible loss} m := by
  let values : Fin (N/2+1) → EReal := fun m => MemoryDecision.value feasible loss (memory N) m.val
  have hout (i : Fin (N/2+1)) : (select (formulas i)).Denotes (values i) :=
    select_minimax feasible loss (memory N) i.val (formulas i) (hformulas i)
  obtain ⟨m,hm,hmin⟩ := leastBudget_correct step hstep (N/2) _ values hout
  have hfull := value_eq_unrestricted feasible loss (N/2) le_rfl
  refine ⟨m.val,by omega,hm,?_,?_⟩
  · exact hmin.1.trans hfull
  · intro j hj
    by_cases hjcap : j ≤ N/2
    · have hj' : values ⟨j,by omega⟩ = values (Fin.last (N/2)) := hj.trans hfull.symm
      exact hmin.2 hj'
    · omega

/-- Compute each threshold formula from the finite loss model and the actual memory minors. -/
def methodThresholds (step : QEStep) (N : ℕ) (input : FirstOrder ((N+N*N)+1))
    (m : ℕ) : Formula 1 :=
  FirstOrder.eliminate step (ProcedureSyntax.methodThresholdFormula N m input)

lemma methodThresholds_correct (step : QEStep) (hstep : StepCorrect step) (N m : ℕ)
    (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) :
    (methodThresholds step N input m).toQF.solutionSet1 =
      MemoryDecision.thresholds actualLoss (fun _ _ l => l) (memory N) m := by
  ext γ
  change (Formula.toQF (methodThresholds step N input m)).eval (fun _ => γ) ↔ _
  rw [Formula.toQF_refines,methodThresholds,FirstOrder.eliminate_correct step hstep]
  exact ProcedureSyntax.methodThresholdFormula_correct N m input actualLoss hinput γ

def methodLeastBudget (step : QEStep) (N : ℕ) (input : FirstOrder ((N+N*N)+1)) : Option ℕ :=
  leastSufficientBudget step N (fun m => methodThresholds step N input m.val)

/-- Complete executable least-memory composition from the actual finite loss formula. -/
theorem methodLeastBudget_correct (step : QEStep) (hstep : StepCorrect step) (N : ℕ)
    (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) :
    ∃ m ≤ N/2, methodLeastBudget step N input = some m ∧
      IsLeast {j : ℕ | MemoryDecision.value actualLoss (fun _ _ l => l) (memory N) j =
        unrestrictedValue actualLoss (fun _ _ l => l)} m :=
  leastSufficientBudget_correct step hstep actualLoss (fun _ _ l => l) _
    (fun m => methodThresholds_correct step hstep N m.val input actualLoss hinput)

def methodStrictGain (step : QEStep) (N m : ℕ) (input : FirstOrder ((N+N*N)+1)) : Bool :=
  strictGain step (select (methodThresholds step N input m))
    (select (methodThresholds step N input (m+1)))

/-- The Boolean test is equivalent to strict gain for the independently defined actual minimax values. -/
theorem methodStrictGain_correct (step : QEStep) (hstep : StepCorrect step) (N m : ℕ)
    (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) :
    methodStrictGain step N m input = true ↔
      MemoryDecision.value actualLoss (fun _ _ l => l) (memory N) (m+1) <
        MemoryDecision.value actualLoss (fun _ _ l => l) (memory N) m :=
  strictGain_thresholds step hstep actualLoss (fun _ _ l => l) (memory N) m _ _
    (methodThresholds_correct step hstep N m input actualLoss hinput)
    (methodThresholds_correct step hstep N (m+1) input actualLoss hinput)

/-- Exact threshold inputs never reach the malformed-output branch. -/
theorem thresholdOutput_ne_invalid {D T Z : Type*}
    (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ) (f : Formula 1)
    (hf : f.toQF.solutionSet1 = MemoryDecision.thresholds feasible loss memory m) :
    select f ≠ .invalid := by
  intro he
  have h := select_minimax feasible loss memory m f hf
  rw [he] at h
  exact h

theorem methodThresholdOutput_ne_invalid (step : QEStep) (hstep : StepCorrect step) (N m : ℕ)
    (input : FirstOrder ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔
      actualLoss d T l) :
    select (methodThresholds step N input m) ≠ .invalid :=
  thresholdOutput_ne_invalid actualLoss (fun _ _ l => l) (memory N) m _
    (methodThresholds_correct step hstep N m input actualLoss hinput)

/-- The same executable selector accepts finitely specified algebraic coefficients directly. -/
def algebraicMethodLeastBudget (step : QEStep) (N : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1)) : Option ℕ :=
  methodLeastBudget step N (rationalizeFirstOrder cs input)

theorem algebraicMethodLeastBudget_correct (step : QEStep) (hstep : StepCorrect step)
    (N : ℕ) {k : ℕ} (cs : Fin k → Code) (input : AlgebraicFirstOrder k ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (fun i => (cs i).value)
      (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔ actualLoss d T l) :
    ∃ m ≤ N/2, algebraicMethodLeastBudget step N cs input = some m ∧
      IsLeast {j : ℕ | MemoryDecision.value actualLoss (fun _ _ l => l) (memory N) j =
        unrestrictedValue actualLoss (fun _ _ l => l)} m := by
  apply methodLeastBudget_correct step hstep N (rationalizeFirstOrder cs input) actualLoss
  intro d T l
  exact (rationalizeFirstOrder_exact cs input _).trans (hinput d T l)

def algebraicMethodStrictGain (step : QEStep) (N m : ℕ) {k : ℕ} (cs : Fin k → Code)
    (input : AlgebraicFirstOrder k ((N+N*N)+1)) : Bool :=
  methodStrictGain step N m (rationalizeFirstOrder cs input)

theorem algebraicMethodStrictGain_correct (step : QEStep) (hstep : StepCorrect step)
    (N m : ℕ) {k : ℕ} (cs : Fin k → Code) (input : AlgebraicFirstOrder k ((N+N*N)+1))
    (actualLoss : (Fin N → ℝ) → RealizationCore.StrictIncrement N → ℝ → Prop)
    (hinput : ∀ d T l,input.evalReal (fun i => (cs i).value)
      (Fin.cons l (ProcedureSyntax.packCoefficients N d T.val)) ↔ actualLoss d T l) :
    algebraicMethodStrictGain step N m cs input = true ↔
      MemoryDecision.value actualLoss (fun _ _ l => l) (memory N) (m+1) <
        MemoryDecision.value actualLoss (fun _ _ l => l) (memory N) m := by
  apply methodStrictGain_correct step hstep N m (rationalizeFirstOrder cs input) actualLoss
  intro d T l
  exact (rationalizeFirstOrder_exact cs input _).trans (hinput d T l)

end MemorySemialgebraic.MemorySelection
