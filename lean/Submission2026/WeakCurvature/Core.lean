module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

/-- Curvature parameter `c` in Section 5, in normalized units. -/
def curvatureC (q : ℝ) : ℝ := -q / (2 * (1 - q))

/-- Curvature parameter `a` in Section 5, in normalized units. -/
def curvatureA (q : ℝ) : ℝ := 1 / (1 - q)

/-- Upper endpoint `u_c` of the normalized scalar root interval. -/
def capacityUpper (c : ℝ) : ℝ := 1 / (1 - c)

/-- The scalar function `Psi_c` from Appendix F. -/
def tailPsi (c a s t : ℝ) : ℝ :=
  4 * c * (2 * t - t ^ 2) + (1 - a * t / s - 2 * c * t) ^ 2 / (a / s + c)

/-- Leading coefficient of the quadratic capacity equation. -/
def capacityA (c a ν t : ℝ) : ℝ := 1 - 4 * c * a * t - c * ν

/-- Linear-coefficient parameter of the quadratic capacity equation. -/
def capacityB (c ν t : ℝ) : ℝ := ν + 2 * (1 - 4 * c) * t

/-- The uncapped upper capacity root from Appendix F. -/
def capacityRoot (c a ν t : ℝ) : ℝ :=
  a * (capacityB c ν t + Real.sqrt (capacityB c ν t ^ 2 - 4 * capacityA c a ν t * t ^ 2)) /
    (2 * capacityA c a ν t)

/-- The capped capacity map from Appendix F. -/
def capacity (c a ν t : ℝ) : ℝ := min 1 (capacityRoot c a ν t)

/-- Left side of the scalar root equation at horizon `N`. -/
def scalarBalance (N : ℕ) (c a ν : ℝ) : ℝ :=
  (capacity c a ν)^[N] 0 + Real.sqrt ((ν - 4 * c) / (2 * a))

/-- The scalar root predicate in normalized units. -/
def IsScalarRoot (N : ℕ) (q ν : ℝ) : Prop :=
  scalarBalance N (curvatureC q) (curvatureA q) ν = 1

/-- Discriminant in the explicit one-step formula. -/
def oneStepD (q : ℝ) : ℝ := 1 - q + q ^ 2

/-- Scalar `t_q` in the explicit one-step formula. -/
def oneStepT (q : ℝ) : ℝ := (1 - q) / (1 + Real.sqrt (oneStepD q))

/-- Normalized one-step terminal-gradient value `U_1(q)`. -/
def oneStepNu (q : ℝ) : ℝ := 2 * oneStepT q ^ 2

end Submission2026.WeakCurvature
