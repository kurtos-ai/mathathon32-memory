module
public import Continuation.Smooth.Attain.Instances
public import Mathlib
@[expose] public section
noncomputable section
namespace SmoothAttain

open Matrix

variable {n N : ℕ} {L R : ℝ}

-- ============================================================================
-- SECTION 1: Bridge between EuclideanSpace and Pi type
-- ============================================================================

def toPi2 {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) : Fin m → ℝ :=
  (WithLp.equiv 2 (Fin m → ℝ)) x

def ofPi2 {m : ℕ} (x : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) :=
  (WithLp.equiv 2 (Fin m → ℝ)).symm x

@[simp] theorem ofPi2_toPi2 {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) : ofPi2 (toPi2 x) = x := by
  simp [toPi2, ofPi2]

@[simp] theorem toPi2_ofPi2 {m : ℕ} (x : Fin m → ℝ) : toPi2 (ofPi2 x) = x := by
  simp [toPi2, ofPi2]

theorem ofPi2_zero {m : ℕ} : (ofPi2 (0 : Fin m → ℝ) : EuclideanSpace ℝ (Fin m)) = 0 := by
  have h : (WithLp.equiv 2 (Fin m → ℝ)).symm (0 : Fin m → ℝ) = (0 : EuclideanSpace ℝ (Fin m)) := by
    show (Equiv.symm (WithLp.equiv 2 (Fin m → ℝ))) 0 = 0
    simp
  exact h

-- ============================================================================
-- SECTION 2: Continuity of iter and terminalLoss in the schedule α
--           (DIRECTION 2, part (c))
-- ============================================================================

theorem G_continuous (I : Instance n L R) : Continuous I.G :=
  I.lipschitz.continuous

theorem f_continuous (I : Instance n L R) : Continuous I.f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (I.hasGrad x).hasFDerivAt.continuousAt

theorem iter_continuous (I : Instance n L R) (k : ℕ) :
    Continuous (fun α : Fin N → ℝ => iter I α k) := by
  induction k with
  | zero =>
    simp only [iter]
    exact continuous_const
  | succ k ih =>
    by_cases hk : k < N
    · have heq : (fun α : Fin N → ℝ => iter I α (k + 1)) = (fun α : Fin N → ℝ => iter I α k - α ⟨k, hk⟩ • I.G (iter I α k)) := by
        funext α
        simp only [iter, hk, dite_true]
      rw [heq]
      apply Continuous.sub ih
      exact Continuous.smul (continuous_apply ⟨k, hk⟩) (I.lipschitz.continuous.comp ih)
    · have heq : (fun α : Fin N → ℝ => iter I α (k + 1)) = (fun α : Fin N → ℝ => iter I α k) := by
        funext α
        simp only [iter, hk, dite_false]
      rw [heq]
      exact ih

theorem terminalLoss_continuous (I : Instance n L R) :
    Continuous (fun α : Fin N → ℝ => terminalLoss I α) := by
  unfold terminalLoss
  have h1 : Continuous (fun α : Fin N → ℝ => I.f (iter I α N)) :=
    (f_continuous I).comp (iter_continuous I N)
  exact h1.sub continuous_const

theorem terminalLoss_lsc (I : Instance n L R) :
    LowerSemicontinuous (fun α : Fin N → ℝ => terminalLoss I α) :=
  (terminalLoss_continuous I).lowerSemicontinuous

-- ============================================================================
-- SECTION 3: Quadratic embedding — objective and gradient definitions
--           (DIRECTION 2, part (a))
-- ============================================================================

def quadObjective {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (xStar x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (1/2 : ℝ) * (toPi2 (x - xStar) ⬝ᵥ (Q *ᵥ toPi2 (x - xStar)))

def quadGradient {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (xStar x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  ofPi2 (Q *ᵥ toPi2 (x - xStar))

theorem quadObjective_at_xStar {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (xStar : EuclideanSpace ℝ (Fin m)) :
    quadObjective Q xStar xStar = 0 := by
  unfold quadObjective
  have h : toPi2 (xStar - xStar : EuclideanSpace ℝ (Fin m)) = (0 : Fin m → ℝ) := by
    have : (xStar - xStar : EuclideanSpace ℝ (Fin m)) = 0 := sub_self xStar
    rw [this]
    show (WithLp.equiv 2 (Fin m → ℝ)) (0 : EuclideanSpace ℝ (Fin m)) = 0
    simp
  rw [h]
  simp

theorem quadGradient_at_xStar {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (xStar : EuclideanSpace ℝ (Fin m)) :
    quadGradient Q xStar xStar = 0 := by
  unfold quadGradient
  have h : toPi2 (xStar - xStar : EuclideanSpace ℝ (Fin m)) = (0 : Fin m → ℝ) := by
    have : (xStar - xStar : EuclideanSpace ℝ (Fin m)) = 0 := sub_self xStar
    rw [this]
    show (WithLp.equiv 2 (Fin m → ℝ)) (0 : EuclideanSpace ℝ (Fin m)) = 0
    simp
  rw [h, Matrix.mulVec_zero]
  exact ofPi2_zero

theorem quadObjective_nonneg {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosSemidef)
    (xStar x : EuclideanSpace ℝ (Fin m)) : 0 ≤ quadObjective Q xStar x := by
  unfold quadObjective
  have h : 0 ≤ (star (toPi2 (x - xStar)) ⬝ᵥ (Q *ᵥ toPi2 (x - xStar))) := by
    have := hQ.dotProduct_mulVec_nonneg (toPi2 (x - xStar))
    simpa only [star_trivial] using this
  have h2 : toPi2 (x - xStar) ⬝ᵥ (Q *ᵥ toPi2 (x - xStar)) = star (toPi2 (x - xStar)) ⬝ᵥ (Q *ᵥ toPi2 (x - xStar)) := by
    simp [star_trivial]
  rw [h2]
  positivity

theorem quadObjective_isMin {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosSemidef)
    (xStar : EuclideanSpace ℝ (Fin m)) : IsMinOn (quadObjective Q xStar) Set.univ xStar := by
  intro x _
  show quadObjective Q xStar xStar ≤ quadObjective Q xStar x
  rw [quadObjective_at_xStar]
  exact quadObjective_nonneg Q hQ xStar x

def errorPoly (α : Fin N → ℝ) (lam : ℝ) : ℝ :=
  Finset.prod Finset.univ (fun i : Fin N => 1 - α i * lam)

theorem errorPoly_zero_eq_one : ∀ (α : Fin 0 → ℝ) (lam : ℝ), errorPoly α lam = 1 := by
  intro α lam
  simp [errorPoly]


end SmoothAttain
