module

/-
Smooth-convex instance semantics shared by the attainment work (paper Section 6,
`lem:compact`). Everything lives in `EuclideanSpace ℝ (Fin n)`, so the norm is the
Euclidean one, not the `Pi` sup norm.
-/
public import Mathlib
@[expose] public section
noncomputable section

namespace SmoothAttain

/-- A smooth-convex problem: convex `C¹` objective with `L`-Lipschitz gradient, an
attained global minimum, and an initial point within `R` of it. The Lipschitz
witness is a field, so `0 ≤ L` comes with the instance rather than the hypotheses. -/
structure Instance (n : ℕ) (L R : ℝ) where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  hasGrad : ∀ x, HasGradientAt f (G x) x
  convex : ConvexOn ℝ Set.univ f
  lip : NNReal
  lip_eq : (lip : ℝ) = L
  lipschitz : LipschitzWith lip G
  x0 : EuclideanSpace ℝ (Fin n)
  xStar : EuclideanSpace ℝ (Fin n)
  isMin : IsMinOn f Set.univ xStar
  near : ‖x0 - xStar‖ ≤ R

variable {n N : ℕ} {L R : ℝ}

/-- One-register iterate: `x_{k+1} = x_k - α_k • G x_k`. -/
def iter (I : Instance n L R) (α : Fin N → ℝ) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => I.x0
  | k + 1 => if h : k < N then iter I α k - α ⟨k, h⟩ • I.G (iter I α k) else iter I α k

/-- Terminal objective error of the one-register method on this instance. -/
def terminalLoss (I : Instance n L R) (α : Fin N → ℝ) : ℝ :=
  I.f (iter I α N) - I.f I.xStar

end SmoothAttain
