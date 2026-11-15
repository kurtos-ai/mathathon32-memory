module
public import Continuation.GJP.ActualUniqueness
public import Continuation.Smooth.DroriZeroQuery
public import Continuation.Smooth.OperationalAttainment

@[expose] public section
noncomputable section
namespace GJP
variable {N : ℕ}

/-- The attained one-register optimum is strictly worse than the sharp benchmark for N≥2. -/
theorem operational_zero_memory_gap (L R : ℝ) (hN : 2 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    ((L*R^2/(2*SmoothBenchmark.theta N N^2) : ℝ) : EReal) <
      MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
        (SmoothOperational.memory N) 0 := by
  have hlo := SmoothDrori.operational_value_lower N 0 L R (by omega) hL hR
  apply lt_of_le_of_ne hlo
  intro heq
  obtain ⟨d,hd,hr⟩ := SmoothOperational.exists_optimal_one_register (N:=N) hL hR
  have hrisk : MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      d (SmoothOperational.zeroIncrement N) ≤
      ((L*R^2/(2*SmoothBenchmark.theta N N^2) : ℝ) : EReal) := by
    rw [hr,←heq]
  have heqW := operational_method_unique L R hL hR d (SmoothOperational.zeroIncrement N) hrisk
  have hnot := InstalledOGM.s_WO_not_one_of_ge2 N L hN (ne_of_gt hL)
    (ne_of_gt (SmoothBenchmark.theta_pos N 2 (by omega)))
  apply hnot
  rw [←heqW]
  exact hd

/-- One additional register strictly improves the actual minimax value for N≥2. -/
theorem operational_strict_gain (L R : ℝ) (hN : 2 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) 1 <
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) 0 := by
  rw [SmoothDrori.operational_value_eq N 1 L R (by omega) hL hR le_rfl]
  exact operational_zero_memory_gap L R hN hL hR

/-- Complete marginal-memory classification, including the zero- and one-query endpoints. -/
theorem operational_strict_gain_iff (m : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    (MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) (m+1) <
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) m) ↔ m = 0 ∧ 2 ≤ N := by
  constructor
  · intro h
    have hN : 2 ≤ N := by
      by_contra hn
      have hn' : N = 0 ∨ N = 1 := by omega
      rcases hn' with rfl | rfl
      · rw [SmoothDrori.operational_value_zero_query (m+1) L R hL hR,
          SmoothDrori.operational_value_zero_query m L R hL hR] at h
        exact lt_irrefl _ h
      · rw [SmoothDrori.operational_value_one_query (m+1) L R hL hR,
          SmoothDrori.operational_value_one_query m L R hL hR] at h
        exact lt_irrefl _ h
    refine ⟨?_,hN⟩
    by_contra hm
    exact SmoothDrori.operational_no_strict_gain_beyond_one N m L R (by omega)
      hL hR (by omega) h
  · rintro ⟨rfl,hN⟩
    exact operational_strict_gain L R hN hL hR

/-- A new strict performance threshold is possible exactly at the first additional register and N≥2. -/
theorem operational_threshold_gain_iff (m : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    (MemoryDecision.thresholds (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) (m+1) \
      MemoryDecision.thresholds (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
        (SmoothOperational.memory N) m).Nonempty ↔ m = 0 ∧ 2 ≤ N := by
  rw [← MemoryDecision.gain_iff]
  exact operational_strict_gain_iff m L R hL hR

end GJP
