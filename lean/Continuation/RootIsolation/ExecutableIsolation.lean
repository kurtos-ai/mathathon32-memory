module
public import Continuation.RootIsolation.ExecutablePolynomial
public import Continuation.RootIsolation.Certificate
public meta import Continuation.RootIsolation.SimpleRoots
public meta import Continuation.RootIsolation.ExecutablePolynomial
public meta import Continuation.RootIsolation.Partition

/-!
# Executable certified rational root isolation

The runtime representation is a finite list of rational coefficients. All polynomial operations
are supplied by `ExecutablePolynomial`, whose denotations refine Mathlib. The isolator computes
squarefree preprocessing, extended-Euclidean Bezout coefficients, rational separation bounds,
and a sign-filtered rational grid. Its output refines the complete mathematical certificate.
The zero polynomial is explicitly reported by `none` because its real root set is not finite.
-/

@[expose] public section
open Polynomial RootIsolation.SimpleRoots
namespace RootIsolation.Executable

/-- Squarefree preprocessing, using executable derivative, gcd, and division. -/
def squarefreePart (p : Poly) : Poly := (divMod p (gcd p (derivative p))).1

@[simp] theorem squarefreePart_refines (p : Poly) :
    denote (squarefreePart p) = RootIsolation.squarefreePart (denote p) := by
  simp [squarefreePart, RootIsolation.squarefreePart]

/-- A normalized Bezout coefficient for the polynomial itself. -/
def bezoutA (q : Poly) : Poly :=
  scale (coeff (gcd q (derivative q)) 0)⁻¹ (gcdA q (derivative q))

/-- A normalized Bezout coefficient for the derivative. -/
def bezoutB (q : Poly) : Poly :=
  scale (coeff (gcd q (derivative q)) 0)⁻¹ (gcdB q (derivative q))

def A (p : Poly) : Poly := bezoutA (squarefreePart p)

def B (p : Poly) : Poly := bezoutB (squarefreePart p)

@[simp] theorem A_refines (p : Poly) (hp : denote p ≠ 0) :
    denote (A p) = RootIsolation.Effective.A (denote p) hp := by
  simp [A, bezoutA, RootIsolation.Effective.A, RootIsolation.Effective.bezoutA,
    RootIsolation.Effective.bezoutNormalizer]

@[simp] theorem B_refines (p : Poly) (hp : denote p ≠ 0) :
    denote (B p) = RootIsolation.Effective.B (denote p) hp := by
  simp [B, bezoutB, RootIsolation.Effective.B, RootIsolation.Effective.bezoutB,
    RootIsolation.Effective.bezoutNormalizer]

/-- Exact rational Cauchy bound. -/
def rootBound (p : Poly) : ℚ :=
  (∑ i ∈ Finset.range (natDegree p), |coeff p i|) / |leadingCoeff p| + 1

@[simp] theorem rootBound_refines (p : Poly) :
    rootBound p = RootIsolation.Effective.rootBound (denote p) := by
  simp [rootBound, RootIsolation.Effective.rootBound, RootIsolation.rationalRootBound]

/-- Coefficient bound computed by a finite rational sum. -/
def coeffAbsSum (p : Poly) (C : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (natDegree p + 1), |coeff p i| * C ^ i

@[simp] theorem coeffAbsSum_refines (p : Poly) (C : ℚ) :
    coeffAbsSum p C = RootIsolation.coeffAbsSum (denote p) C := by
  simp [coeffAbsSum, RootIsolation.coeffAbsSum]

def coefficientBound (p : Poly) : ℚ := max 1 (coeffAbsSum (B p) (rootBound p))

def curvatureBound (p : Poly) : ℚ :=
  max 1 (coeffAbsSum (derivative (derivative (squarefreePart p))) (rootBound p))

def epsilon (p : Poly) : ℚ := 1 / (2 * coefficientBound p * curvatureBound p)

def gridStep (p : Poly) : ℚ := epsilon p / 2

@[simp] theorem coefficientBound_refines (p : Poly) (hp : denote p ≠ 0) :
    coefficientBound p = RootIsolation.Effective.coefficientBound (denote p) hp := by
  simp only [coefficientBound, RootIsolation.Effective.coefficientBound,
    coeffAbsSum_refines, B_refines p hp, rootBound_refines]

@[simp] theorem curvatureBound_refines (p : Poly) :
    curvatureBound p = RootIsolation.Effective.curvatureBound (denote p) := by
  simp [curvatureBound, RootIsolation.Effective.curvatureBound]

@[simp] theorem epsilon_refines (p : Poly) (hp : denote p ≠ 0) :
    epsilon p = RootIsolation.Effective.epsilon (denote p) hp := by
  simp only [epsilon, RootIsolation.Effective.epsilon, RootIsolation.separationEps,
    coefficientBound_refines p hp, curvatureBound_refines]

@[simp] theorem gridStep_refines (p : Poly) (hp : denote p ≠ 0) :
    gridStep p = RootIsolation.Effective.gridStep (denote p) hp := by
  simp only [gridStep, RootIsolation.Effective.gridStep, epsilon_refines p hp]

/-- Runtime filtering uses exact rational Horner evaluation. -/
def filteredIntervals (p : Poly) (C delta : ℚ) : List IsoInterval :=
  ((RootIsolation.partitionPoints C delta).filter (fun r => decide (eval p r = 0))).map
      IsoInterval.point ++
    ((RootIsolation.consecutivePairs (RootIsolation.partitionPoints C delta)).filter
      (fun ab => decide (eval p ab.1 * eval p ab.2 < 0))).map
      (fun ab => IsoInterval.openInterval ab.1 ab.2)

@[simp] theorem filteredIntervals_refines (p : Poly) (C delta : ℚ) :
    filteredIntervals p C delta =
      RootIsolation.SimpleRoots.filteredIntervals (denote p) C delta := by
  simp [filteredIntervals, RootIsolation.SimpleRoots.filteredIntervals,
    RootIsolation.SimpleRoots.pointRoots, RootIsolation.SimpleRoots.signChangingIntervals]

/-- The complete finite computation, with no noncomputable operations in its call graph. -/
def intervals (p : Poly) : List IsoInterval :=
  filteredIntervals (squarefreePart p) (rootBound p) (gridStep p)

/-- Exact equality with the previously certified mathematical algorithm. -/
theorem intervals_refines (p : Poly) (hp : denote p ≠ 0) :
    intervals p = RootIsolation.Effective.intervals (denote p) hp := by
  simp only [intervals, RootIsolation.Effective.intervals, filteredIntervals_refines,
    squarefreePart_refines, rootBound_refines, gridStep_refines p hp]

/-- All real roots are covered by the executable result. -/
theorem every_root_mem_intervals (p : Poly) (hp : denote p ≠ 0) (x : ℝ)
    (hx : (denote p).aeval x = 0) : ∃ I ∈ intervals p, x ∈ I.toSet := by
  rw [intervals_refines p hp]
  exact RootIsolation.Effective.every_root_mem_intervals (denote p) hp x hx

/-- Every returned interval contains exactly one root of the original polynomial. -/
theorem existsUnique_root_of_mem_intervals (p : Poly) (hp : denote p ≠ 0)
    (I : IsoInterval) (hI : I ∈ intervals p) :
    ∃! x : ℝ, (denote p).aeval x = 0 ∧ x ∈ I.toSet := by
  rw [intervals_refines p hp] at hI
  obtain ⟨x, hx, huniq⟩ := RootIsolation.Effective.existsUnique_root_of_mem_filteredInterval
    (denote p) hp I hI
  have hrootiff (y : ℝ) : (denote p).aeval y = 0 ↔
      (RootIsolation.squarefreePart (denote p)).aeval y = 0 := by
    rw [RootIsolation.Effective.squarefree_parts_eq]
    exact SquarefreePreprocessing.squarefree_aeval_root_iff (denote p) hp y
  refine ⟨x, ⟨(hrootiff x).mpr hx.1, hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨(hrootiff y).mp hy.1, hy.2⟩

/-- Distinct returned cells are disjoint as sets of real numbers. -/
theorem disjoint_intervals_of_ne (p : Poly) (hp : denote p ≠ 0)
    (I J : IsoInterval) (hI : I ∈ intervals p) (hJ : J ∈ intervals p) (hne : I ≠ J) :
    Disjoint I.toSet J.toSet := by
  rw [intervals_refines p hp] at hI hJ
  exact RootIsolation.Effective.disjoint_intervals_of_ne (denote p) hp I J hI hJ hne

/-- `none` identifies the zero polynomial; `some cells` is its finite certified root isolation. -/
def isolate (p : Poly) : Option (List IsoInterval) :=
  if trim p = [] then none else some (intervals p)

@[simp] theorem isolate_none_iff (p : Poly) : isolate p = none ↔ denote p = 0 := by
  simp [isolate, trim_eq_nil_iff]

theorem isolate_some_iff (p : Poly) (L : List IsoInterval) :
    isolate p = some L ↔ denote p ≠ 0 ∧ L = intervals p := by
  by_cases hp : trim p = []
  · simp [isolate, hp, (trim_eq_nil_iff p).mp hp]
  · simp [isolate, hp, mt (trim_eq_nil_iff p).mpr hp, eq_comm]

/-- Full soundness, completeness, uniqueness, and disjointness of the executable result. -/
theorem isolate_spec (p : Poly) (L : List IsoInterval) (h : isolate p = some L) :
    (∀ x : ℝ, (denote p).aeval x = 0 → ∃ I ∈ L, x ∈ I.toSet) ∧
    (∀ I ∈ L, ∃! x : ℝ, (denote p).aeval x = 0 ∧ x ∈ I.toSet) ∧
    (∀ I ∈ L, ∀ J ∈ L, I ≠ J → Disjoint I.toSet J.toSet) := by
  obtain ⟨hp, rfl⟩ := (isolate_some_iff p L).mp h
  exact ⟨every_root_mem_intervals p hp, existsUnique_root_of_mem_intervals p hp,
    fun I hI J hJ hne => disjoint_intervals_of_ne p hp I J hI hJ hne⟩

end RootIsolation.Executable

/-- info: some [RootIsolation.SimpleRoots.IsoInterval.openInterval (-3 : Rat)/2 (-4 : Rat)/3,
 RootIsolation.SimpleRoots.IsoInterval.openInterval (4 : Rat)/3 (3 : Rat)/2] -/
#guard_msgs in
#eval RootIsolation.Executable.isolate [1, 0, -2]
/-- info: some [RootIsolation.SimpleRoots.IsoInterval.point 1] -/
#guard_msgs in
#eval RootIsolation.Executable.isolate [1, -2, 1]
/-- info: some [] -/
#guard_msgs in
#eval RootIsolation.Executable.isolate [1, 0, 1]
/-- info: some [] -/
#guard_msgs in
#eval RootIsolation.Executable.isolate [5]
/-- info: none -/
#guard_msgs in
#eval RootIsolation.Executable.isolate [0, 0]
