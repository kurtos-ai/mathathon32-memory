module
public import Continuation.Semialgebraic.AlgebraicFirstOrder
public import Continuation.Semialgebraic.FirstOrderBlocks
public import Continuation.Semialgebraic.EndpointSelection
public meta import Continuation.Semialgebraic.AlgebraicFirstOrder
public meta import Continuation.Semialgebraic.FirstOrderBlocks
public meta import Continuation.Semialgebraic.EndpointSelection

@[expose] public section
namespace MemorySemialgebraic.AlgebraicParameters
open SymbolicQE

/-- Literal rational first-order output, with the finite coefficient block bound at the outside. -/
def rationalizeFirstOrder {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k n) : FirstOrder n :=
  FirstOrder.existsBlock k n (f.rationalBody cs)

/-- Algebraic coefficient elimination preserves arbitrary quantifier alternation exactly. -/
theorem rationalizeFirstOrder_exact {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k n)
    (v : Fin n → ℝ) :
    FirstOrder.evalReal v (rationalizeFirstOrder cs f) ↔ f.evalReal (fun i => (cs i).value) v := by
  rw [rationalizeFirstOrder,FirstOrder.existsBlock_correct]
  exact f.rationalBody_exact cs v

/-- Every finite family of arbitrary algebraic coefficients admits a literal rational
first-order formula with the same truth set, using their minimal-polynomial codes. -/
theorem algebraic_firstOrder_rational_reduction {k n : ℕ}
    (a : Fin k → ℝ) (ha : ∀ i, IsAlgebraic ℚ (a i)) (f : AlgebraicFirstOrder k n) :
    ∃ cs : Fin k → Code,
      (∀ i, RootIsolation.Executable.denote (cs i).poly = minpoly ℚ (a i)) ∧
      ∀ v : Fin n → ℝ, FirstOrder.evalReal v (rationalizeFirstOrder cs f) ↔ f.evalReal a v := by
  obtain ⟨cs,hv,hp⟩ := exists_minpoly_codes a ha
  refine ⟨cs,hp,?_⟩
  intro v
  simpa only [hv] using rationalizeFirstOrder_exact cs f v

/-- Compose coefficient rationalization with a supplied one-variable rational QE algorithm. -/
def eliminateFirstOrder (step : {n : ℕ} → Formula (n+1) → Formula n)
    {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k n) : Formula n :=
  FirstOrder.eliminate step (rationalizeFirstOrder cs f)

theorem eliminateFirstOrder_correct
    (step : {n : ℕ} → Formula (n+1) → Formula n)
    (hstep : ∀ {n : ℕ} (f : Formula (n+1)) (v : Fin n → ℝ),
      (step f).evalReal v ↔ ∃ x : ℝ, f.evalReal (Fin.cons x v))
    {k n : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k n) (v : Fin n → ℝ) :
    (eliminateFirstOrder step cs f).evalReal v ↔ f.evalReal (fun i => (cs i).value) v := by
  rw [eliminateFirstOrder,FirstOrder.eliminate_correct step hstep,rationalizeFirstOrder_exact]

/-- Finite exact output from the complete displayed coefficient/QE/root/sign pipeline. -/
def minimaxOutput (step : {n : ℕ} → Formula (n+1) → Formula n)
    {k : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k 1) : EndpointSelection.Output :=
  EndpointSelection.select (eliminateFirstOrder step cs f)

/-- Correctness is compositional in the rational QE step; coefficient handling, all binders,
root isolation, exact signs, and endpoint selection are proved by the displayed implementations. -/
theorem minimaxOutput_correct {D T Z : Type*}
    (step : {n : ℕ} → Formula (n+1) → Formula n)
    (hstep : ∀ {n : ℕ} (f : Formula (n+1)) (v : Fin n → ℝ),
      (step f).evalReal v ↔ ∃ x : ℝ, f.evalReal (Fin.cons x v))
    {k : ℕ} (cs : Fin k → Code) (f : AlgebraicFirstOrder k 1)
    (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ)
    (hf : ∀ γ : ℝ, f.evalReal (fun i => (cs i).value) (fun _ => γ) ↔
      γ ∈ MemoryDecision.thresholds feasible loss memory m) :
    (minimaxOutput step cs f).Denotes (MemoryDecision.value feasible loss memory m) := by
  apply EndpointSelection.select_minimax feasible loss memory m
  ext γ
  change (Formula.toQF (eliminateFirstOrder step cs f)).eval (fun _ => γ) ↔ _
  rw [Formula.toQF_refines,eliminateFirstOrder_correct step hstep]
  exact hf γ

end MemorySemialgebraic.AlgebraicParameters
