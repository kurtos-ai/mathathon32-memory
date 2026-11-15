module
public import Continuation.Smooth.DroriLowerBound
public import Continuation.Smooth.OGMOperational
@[expose] public section
noncomputable section
namespace SmoothDrori

/-- Every operational schedule and strict increment has risk at least the sharp
    smooth benchmark; the witness is an actual constructed smooth function. -/
theorem operational_risk_lower (N : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) :
    ((L*R^2/(2*(SmoothBenchmark.theta N N)^2) : ℝ) : EReal) ≤
      MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N) d T := by
  obtain ⟨z,hz,hbound⟩ := actualLossSet_has_sharp_lower_witness N L R hN hL hR
    (RealizationCore.W_of N d T.val)
  apply le_iSup_of_le ⟨z,hz⟩
  exact_mod_cast hbound

/-- The minimax lower bound follows from the independent infimum over algorithms,
    for every memory budget, including zero additional registers. -/
theorem operational_value_lower (N m : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    ((L*R^2/(2*(SmoothBenchmark.theta N N)^2) : ℝ) : EReal) ≤
      MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
        (SmoothOperational.memory N) m := by
  exact le_iInf (fun T => le_iInf (fun d => operational_risk_lower N L R hN hL hR d T.val))

/-- The sharp operational smooth-convex minimax value is attained with one
    additional register and remains the same at every larger memory budget. -/
theorem operational_value_eq (N m : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) (hm : 1 ≤ m) :
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) m = ((L*R^2/(2*(SmoothBenchmark.theta N N)^2) : ℝ) : EReal) :=
  le_antisymm (OGMVerified.value_upper N m L R hL hm) (operational_value_lower N m L R hN hL hR)

/-- The implemented optimized gradient method attains the actual oracle risk. -/
theorem operational_ogm_risk_eq (N : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (OGMVerified.coordinates N L).1 (OGMVerified.coordinates N L).2 =
      ((L*R^2/(2*(SmoothBenchmark.theta N N)^2) : ℝ) : EReal) :=
  le_antisymm (OGMVerified.risk_upper N L R hL)
    (operational_risk_lower N L R hN hL hR _ _)

/-- The strict performance thresholds are the open ray above the independently
    computed minimax value. -/
theorem operational_thresholds_eq_ray (N m : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) (hm : 1 ≤ m) :
    MemoryDecision.thresholds (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) m = Set.Ioi (L*R^2/(2*(SmoothBenchmark.theta N N)^2)) :=
  MemoryDecision.thresholds_eq_ray_of_value_eq _ _ _ _ _
    (operational_value_eq N m L R hN hL hR hm)

/-- Additional memory beyond one extra register brings no improvement. -/
theorem operational_no_gain_beyond_one (N m : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) (hm : 1 ≤ m) :
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) m =
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) 1 := by
  rw [operational_value_eq N m L R hN hL hR hm,
    operational_value_eq N 1 L R hN hL hR le_rfl]

lemma operational_no_strict_gain_beyond_one (N m : ℕ) (L R : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) (hm : 1 ≤ m) :
    ¬ MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) (m+1) <
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) m := by
  rw [operational_no_gain_beyond_one N (m+1) L R hN hL hR (by omega),
    operational_no_gain_beyond_one N m L R hN hL hR hm]
  exact lt_irrefl _

/-- For one query the same exact value is attained with no additional register. -/
theorem operational_value_one_query_zero_memory (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    MemoryDecision.value (SmoothOperational.feasible 1 L R) (SmoothOperational.loss 1)
      (SmoothOperational.memory 1) 0 = ((L*R^2/8 : ℝ) : EReal) := by
  apply le_antisymm (OGMVerified.value_upper_one_query L R hL)
  have h := operational_value_lower 1 0 L R le_rfl hL hR
  norm_num [InstalledOGM.theta_one_one] at h ⊢
  exact h

lemma operational_value_one_query (m : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    MemoryDecision.value (SmoothOperational.feasible 1 L R) (SmoothOperational.loss 1)
      (SmoothOperational.memory 1) m = ((L*R^2/8 : ℝ) : EReal) := by
  by_cases hm : m = 0
  · subst m
    exact operational_value_one_query_zero_memory L R hL hR
  · have h := operational_value_eq 1 m L R le_rfl hL hR (by omega)
    norm_num [InstalledOGM.theta_one_one] at h ⊢
    exact h

theorem operational_thresholds_one_query (m : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    MemoryDecision.thresholds (SmoothOperational.feasible 1 L R) (SmoothOperational.loss 1)
      (SmoothOperational.memory 1) m = Set.Ioi (L*R^2/8) :=
  MemoryDecision.thresholds_eq_ray_of_value_eq _ _ _ _ _
    (operational_value_one_query m L R hL hR)

end SmoothDrori
