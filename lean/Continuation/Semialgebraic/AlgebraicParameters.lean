module
public import Continuation.Semialgebraic.SymbolicAffineQE
public import Continuation.RootIsolation.ExecutableIsolation
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public meta import Continuation.Semialgebraic.SymbolicAffineQE
public meta import Continuation.RootIsolation.ExecutableIsolation

@[expose] public section
open Polynomial RootIsolation.SimpleRoots
namespace MemorySemialgebraic.AlgebraicParameters
open SymbolicQE
open RootIsolation.Executable

/-- Finite rational input specifying one real algebraic number. The proof fields certify
membership in the output of the executable isolator and are erased at runtime. -/
structure Code where
  poly : Poly
  cell : IsoInterval
  nonzero : RootIsolation.Executable.denote poly ≠ 0
  isolated : cell ∈ intervals poly

noncomputable def Code.value (c : Code) : ℝ :=
  (existsUnique_root_of_mem_intervals c.poly c.nonzero c.cell c.isolated).choose

lemma Code.value_spec (c : Code) :
    (RootIsolation.Executable.denote c.poly).aeval c.value = 0 ∧ c.value ∈ c.cell.toSet :=
  (existsUnique_root_of_mem_intervals c.poly c.nonzero c.cell c.isolated).choose_spec.1

lemma Code.value_unique (c : Code) (x : ℝ)
    (hx : (RootIsolation.Executable.denote c.poly).aeval x = 0 ∧ x ∈ c.cell.toSet) : x = c.value :=
  (existsUnique_root_of_mem_intervals c.poly c.nonzero c.cell c.isolated).choose_spec.2 x hx

lemma Code.value_algebraic (c : Code) : IsAlgebraic ℚ c.value :=
  ⟨RootIsolation.Executable.denote c.poly,c.nonzero,c.value_spec.1⟩

/-- Every real algebraic number has a code using its minimal polynomial. This existence
statement is separate from algorithms consuming already specified finite codes. -/
theorem exists_minpoly_code (x : ℝ) (hx : IsAlgebraic ℚ x) :
    ∃ c : Code, c.value = x ∧ RootIsolation.Executable.denote c.poly = minpoly ℚ x := by
  obtain ⟨p,hp⟩ := RootIsolation.Executable.denote_surjective (minpoly ℚ x)
  have hp0 : RootIsolation.Executable.denote p ≠ 0 := hp ▸ minpoly.ne_zero hx.isIntegral
  have hroot : (RootIsolation.Executable.denote p).aeval x = 0 := by
    rw [hp]
    exact minpoly.aeval ℚ x
  obtain ⟨I,hI,hxI⟩ := every_root_mem_intervals p hp0 x hroot
  let c : Code := ⟨p,I,hp0,hI⟩
  exact ⟨c,(c.value_unique x ⟨hroot,hxI⟩).symm,hp⟩

/-- A finite specified family introduces only finitely many rationally constrained parameters. -/
theorem exists_minpoly_codes {k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, IsAlgebraic ℚ (a i)) :
    ∃ cs : Fin k → Code, (∀ i, (cs i).value = a i) ∧
      ∀ i, RootIsolation.Executable.denote (cs i).poly = minpoly ℚ (a i) := by
  choose cs hv hp using fun i => exists_minpoly_code (a i) (ha i)
  exact ⟨cs,hv,hp⟩

/-- Polynomial powers and substitution are built solely from the existing rational syntax. -/
def power {n : ℕ} (x : Expr n) : ℕ → Expr n
  | 0 => .constant 1
  | k+1 => .mul (power x k) x

@[simp] lemma power_eval {n : ℕ} (v : Fin n → ℝ) (x : Expr n) (k : ℕ) :
    Expr.evalReal v (power x k) = (Expr.evalReal v x)^k := by
  induction k <;> simp_all [-Expr.evalReal_refines,power,Expr.evalReal,pow_succ]

def polynomialAt {n : ℕ} : Poly → Expr n → Expr n
  | [], _ => .constant 0
  | q::p, x => .add (.mul (.constant q) (power x p.length)) (polynomialAt p x)

@[simp] lemma polynomialAt_eval {n : ℕ} (v : Fin n → ℝ) (p : Poly) (x : Expr n) :
    Expr.evalReal v (polynomialAt p x) =
      (RootIsolation.Executable.denote p).aeval (Expr.evalReal v x) := by
  induction p <;> simp_all [-Expr.evalReal_refines,polynomialAt,Expr.evalReal,denote_cons]

def cellConstraint {n : ℕ} : IsoInterval → Expr n → Formula n
  | .point q, x => .eqZero (.sub x (.constant q))
  | .openInterval a b, x => .conj (.positive (.sub x (.constant a)))
      (.positive (.sub (.constant b) x))

@[simp] lemma cellConstraint_eval {n : ℕ} (v : Fin n → ℝ) (I : IsoInterval) (x : Expr n) :
    Formula.evalReal v (cellConstraint I x) ↔ Expr.evalReal v x ∈ I.toSet := by
  cases I <;> simp [cellConstraint,Formula.evalReal,Expr.sub,Expr.evalReal,
    IsoInterval.toSet,← sub_eq_add_neg,sub_eq_zero,sub_pos]

def Code.constraint {n : ℕ} (c : Code) (x : Expr n) : Formula n :=
  .conj (.eqZero (polynomialAt c.poly x)) (cellConstraint c.cell x)

/-- The polynomial and rational isolating interval specify exactly one real value. -/
theorem Code.constraint_exact {n : ℕ} (c : Code) (v : Fin n → ℝ) (x : Expr n) :
    Formula.evalReal v (c.constraint x) ↔ Expr.evalReal v x = c.value := by
  change ((Expr.evalReal v (polynomialAt c.poly x) = 0) ∧
    Formula.evalReal v (cellConstraint c.cell x)) ↔ _
  rw [polynomialAt_eval,cellConstraint_eval]
  exact ⟨c.value_unique _, fun h => h ▸ c.value_spec⟩

def constraints {k n : ℕ} (cs : Fin k → Code) : Formula (k+n) :=
  Formula.all (List.ofFn (fun i => (cs i).constraint (.variable (Fin.castAdd n i))))

lemma constraints_exact {k n : ℕ} (cs : Fin k → Code) (v : Fin (k+n) → ℝ) :
    Formula.evalReal v (constraints (n:=n) cs) ↔ ∀ i, v (Fin.castAdd n i) = (cs i).value := by
  simp only [constraints,Formula.all_eval,List.mem_ofFn,forall_exists_index,
    forall_apply_eq_imp_iff,Code.constraint_exact,Expr.evalReal]

/-- Concatenate coefficient variables and ordinary variables. -/
def assignment {k n : ℕ} (c : Fin k → ℝ) (v : Fin n → ℝ) : Fin (k+n) → ℝ :=
  Fin.addCases c v

@[simp] lemma assignment_left {k n : ℕ} (c : Fin k → ℝ) (v : Fin n → ℝ) (i : Fin k) :
    assignment c v (Fin.castAdd n i) = c i := by simp [assignment]

@[simp] lemma assignment_right {k n : ℕ} (c : Fin k → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    assignment c v (Fin.natAdd k i) = v i := by simp [assignment]

lemma coefficient_realization_unique {k n : ℕ} (cs : Fin k → Code) (v : Fin n → ℝ) :
    ∃! c : Fin k → ℝ, Formula.evalReal (assignment c v) (constraints (n:=n) cs) := by
  refine ⟨fun i => (cs i).value,?_,?_⟩
  · simp [constraints_exact]
  · intro c hc
    apply _root_.funext
    simpa only [constraints_exact,assignment_left] using hc

end MemorySemialgebraic.AlgebraicParameters
