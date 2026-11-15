module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

def R0 (ν t : ℝ) : ℝ :=
  (ν + 2 * t + Real.sqrt ((ν + 2 * t) ^ 2 - 4 * t ^ 2)) / 2

def cappedR0 (ν t : ℝ) : ℝ := min (1 : ℝ) (R0 ν t)

theorem R0_mono_nu {ν₁ ν₂ t : ℝ} (hν₁ : 0 ≤ ν₁) (_hν₂ : 0 ≤ ν₂) (hle : ν₁ ≤ ν₂) (ht0 : 0 ≤ t) :
    R0 ν₁ t ≤ R0 ν₂ t := by
  unfold R0
  have hD_le : (ν₁ + 2 * t) ^ 2 - 4 * t ^ 2 ≤ (ν₂ + 2 * t) ^ 2 - 4 * t ^ 2 := by nlinarith
  have hsqrt_le : Real.sqrt ((ν₁ + 2 * t) ^ 2 - 4 * t ^ 2) ≤ Real.sqrt ((ν₂ + 2 * t) ^ 2 - 4 * t ^ 2) :=
    Real.sqrt_le_sqrt hD_le
  linarith

theorem cappedR0_mono_nu {ν₁ ν₂ t : ℝ} (hν₁ : 0 ≤ ν₁) (hν₂ : 0 ≤ ν₂) (hle : ν₁ ≤ ν₂) (ht0 : 0 ≤ t) :
    cappedR0 ν₁ t ≤ cappedR0 ν₂ t := by
  unfold cappedR0
  have hR_le := R0_mono_nu hν₁ hν₂ hle ht0
  exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) hR_le)

theorem discriminant_mono_t {ν t₁ t₂ : ℝ} (hν : 0 ≤ ν) (ht1_le : t₁ ≤ t₂) (_ht1_0 : 0 ≤ t₁) :
    (ν + 2 * t₁) ^ 2 - 4 * t₁ ^ 2 ≤ (ν + 2 * t₂) ^ 2 - 4 * t₂ ^ 2 := by
  have h_eq1 : (ν + 2 * t₁) ^ 2 - 4 * t₁ ^ 2 = ν ^ 2 + 4 * ν * t₁ := by ring
  have h_eq2 : (ν + 2 * t₂) ^ 2 - 4 * t₂ ^ 2 = ν ^ 2 + 4 * ν * t₂ := by ring
  nlinarith

theorem R0_mono_t {ν t₁ t₂ : ℝ} (hν : 0 ≤ ν) (hle : t₁ ≤ t₂) (ht1_0 : 0 ≤ t₁) :
    R0 ν t₁ ≤ R0 ν t₂ := by
  unfold R0
  have hD_le := discriminant_mono_t hν hle ht1_0
  have hsqrt_le : Real.sqrt ((ν + 2 * t₁) ^ 2 - 4 * t₁ ^ 2) ≤ Real.sqrt ((ν + 2 * t₂) ^ 2 - 4 * t₂ ^ 2) :=
    Real.sqrt_le_sqrt hD_le
  linarith

theorem cappedR0_mono_t {ν t₁ t₂ : ℝ} (hν : 0 ≤ ν) (hle : t₁ ≤ t₂) (ht1_0 : 0 ≤ t₁) :
    cappedR0 ν t₁ ≤ cappedR0 ν t₂ := by
  unfold cappedR0
  exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) (R0_mono_t hν hle ht1_0))

theorem R0_nonneg {ν t : ℝ} (hν : 0 ≤ ν) (ht0 : 0 ≤ t) : 0 ≤ R0 ν t := by
  unfold R0
  have hsqrt : 0 ≤ Real.sqrt ((ν + 2 * t) ^ 2 - 4 * t ^ 2) := Real.sqrt_nonneg _
  positivity

theorem cappedR0_le_one (ν t : ℝ) : cappedR0 ν t ≤ 1 :=
  min_le_left _ _

theorem cappedR0_nonneg {ν t : ℝ} (hν : 0 ≤ ν) (ht0 : 0 ≤ t) : 0 ≤ cappedR0 ν t :=
  le_min (by linarith) (R0_nonneg hν ht0)

theorem cappedR0_mem_Icc {ν t : ℝ} (hν : 0 ≤ ν) (ht0 : 0 ≤ t) :
    cappedR0 ν t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cappedR0_nonneg hν ht0, cappedR0_le_one _ _⟩

#print axioms R0_mono_nu
#print axioms cappedR0_mono_nu
#print axioms R0_mono_t
#print axioms cappedR0_mono_t

end Submission2026.WeakCurvature
