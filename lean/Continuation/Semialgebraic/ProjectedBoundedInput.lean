module
public import Continuation.Semialgebraic.ProjectedProcedureInput

/-! # Explicit bounded and unrestricted slope constraints for the projected procedure -/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput
open ProjectedLossSyntax AlgebraicParameters
open scoped InnerProductSpace

/-- Put every algebraic domain coefficient into an explicit parameter coordinate. -/
def algebraicDomain {d k : ℕ} (κ : AlgebraicFormula k d) : Formula (d+k) :=
  κ.compileWith (Fin.natAdd d) (Fin.castAdd k)

theorem domain_algebraicDomain {d k : ℕ} (κ : AlgebraicFormula k d) (a : Fin k → ℝ) :
    domain (algebraicDomain κ) a = {x : Space d | κ.evalReal a (fun i => x i)} := by
  ext x
  simp only [domain, Set.mem_ofPred_eq, algebraicDomain, AlgebraicFormula.compileWith_eval,
    Function.comp_def, Fin.addCases_left, Fin.addCases_right]

/-- The permitted slope ball has polynomial syntax, with its radius among the supplied parameters. -/
def slopeBall (d : ℕ) {k : ℕ} (M : Expr k) : Formula (d+k) :=
  .nonnegative (Expr.sub
    (.mul (M.renameVariables (Fin.natAdd d)) (M.renameVariables (Fin.natAdd d)))
    (innerExpr (fun i : Fin d => .variable (Fin.castAdd k i))
      (fun i : Fin d => .variable (Fin.castAdd k i))))

theorem domain_slopeBall (d : ℕ) {k : ℕ} (M : Expr k) (a : Fin k → ℝ)
    (hM : 0 ≤ M.evalReal a) :
    domain (slopeBall d M) a = Metric.closedBall (0 : Space d) (M.evalReal a) := by
  ext x
  have hx : evalVector (Fin.addCases (fun i => x i) a)
      (fun i : Fin d => Expr.variable (Fin.castAdd k i)) = x := by
    ext i
    simp only [evalVector_apply, Expr.evalReal, Fin.addCases_left]
  change (slopeBall d M).evalReal (Fin.addCases (fun i => x i) a) ↔ _
  simp only [slopeBall, Formula.evalReal, Expr.sub, Expr.evalReal,
    Expr.renameVariables_correct, Function.comp_def, Fin.addCases_right,
    innerExpr_correct, hx, real_inner_self_eq_norm_sq, ← sub_eq_add_neg, sub_nonneg,
    ← pow_two, Metric.mem_closedBall, dist_zero_right]
  exact sq_le_sq₀ (norm_nonneg x) hM

@[simp] theorem domain_unrestricted (d k : ℕ) (a : Fin k → ℝ) :
    domain (Formula.tru : Formula (d+k)) a = Set.univ := by
  ext x
  simp [domain, Formula.evalReal]

/-- The bounded projected endpoint algorithm takes the domain syntax and two radius expressions. -/
def boundedEndpoint (N m d : ℕ) {k : ℕ} (cs : Fin k → Code) (κ : Formula (d+k))
    (M R : Expr k) : EndpointSelection.Output := endpoint N m cs κ (slopeBall d M) R

theorem boundedEndpoint_correct (N m d : ℕ) {k : ℕ} (cs : Fin k → Code)
    (κ : Formula (d+k)) (M R : Expr k)
    (hK : Convex ℝ (domain κ (fun i => (cs i).value)))
    (hcK : IsClosed (domain κ (fun i => (cs i).value)))
    (hneK : (domain κ (fun i => (cs i).value)).Nonempty)
    (hM : 0 ≤ M.evalReal (fun i => (cs i).value))
    (hR : 0 ≤ R.evalReal (fun i => (cs i).value)) :
    (boundedEndpoint N m d cs κ M R).Denotes
      (MemoryDecision.value
        (ProjectedOperational.feasible hK hcK hneK N
          (Metric.closedBall (0 : Space d) (M.evalReal (fun i => (cs i).value)))
          (R.evalReal (fun i => (cs i).value)))
        (ProjectedOperational.loss N) (ProjectedOperational.memory N) m) := by
  have hB0 : (0 : Space d) ∈ domain (slopeBall d M) (fun i => (cs i).value) := by
    rw [domain_slopeBall d M _ hM]
    exact Metric.mem_closedBall_self hM
  have h := endpoint_correct N cs κ (slopeBall d M) R hK hcK hneK hB0 hR m
  rw [domain_slopeBall d M _ hM] at h
  exact h

/-- The bounded procedure always describes a finite real algebraic value in the stated range. -/
theorem boundedEndpoint_finite (N m d : ℕ) {k : ℕ} (cs : Fin k → Code)
    (κ : Formula (d+k)) (M R : Expr k)
    (hK : Convex ℝ (domain κ (fun i => (cs i).value)))
    (hcK : IsClosed (domain κ (fun i => (cs i).value)))
    (hneK : (domain κ (fun i => (cs i).value)).Nonempty)
    (hM : 0 ≤ M.evalReal (fun i => (cs i).value))
    (hR : 0 ≤ R.evalReal (fun i => (cs i).value)) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ M.evalReal (fun i => (cs i).value) * R.evalReal (fun i => (cs i).value) ∧
      (boundedEndpoint N m d cs κ M R).Denotes (v : EReal) := by
  obtain ⟨v,hv0,hvM,hv⟩ := ProjectedOperational.bounded_value_finite hK hcK hneK N m
    (M.evalReal (fun i => (cs i).value)) (R.evalReal (fun i => (cs i).value)) hM hR
  refine ⟨v,hv0,hvM,?_⟩
  rw [← hv]
  exact boundedEndpoint_correct N m d cs κ M R hK hcK hneK hM hR

end MemorySemialgebraic.SymbolicQE.ProjectedProcedureInput
