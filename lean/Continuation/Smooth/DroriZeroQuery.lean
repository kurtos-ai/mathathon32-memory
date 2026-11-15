module
public import Continuation.Smooth.DroriOperational
@[expose] public section
noncomputable section
namespace SmoothDrori

lemma scalar_zero_query_witness (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (W : Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ I : SmoothAttain.Instance 1 L R, SmoothGramModel.terminalLoss I W = L*R^2/2 := by
  let x0 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 R
  have hn : ‖x0-(0 : EuclideanSpace ℝ (Fin 1))‖ ≤ R := by
    simp [x0,PiLp.norm_single,Real.norm_eq_abs,abs_of_pos hR]
  let I := SmoothAttain.scalarInstance L ⟨hL.le,le_rfl⟩ 0 x0 hn
  refine ⟨I,?_⟩
  change I.f (OracleTrajectory.run W I.G I.x0 (0 : Fin 1))-I.f I.xStar = _
  rw [OracleTrajectory.run_zero]
  simp [I,SmoothAttain.scalarInstance,SmoothAttain.scalarObj,x0,
    PiLp.norm_single,Real.norm_eq_abs,abs_of_pos hR]
  ring

lemma operational_risk_zero_query (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (d : Fin 0 → ℝ) (T : RealizationCore.StrictIncrement 0) :
    MemoryDecision.risk (SmoothOperational.feasible 0 L R) (SmoothOperational.loss 0) d T =
      ((L*R^2/2 : ℝ) : EReal) := by
  apply le_antisymm
  · apply (MemoryDecision.risk_le_iff _ _ _ _ _).mpr
    rintro z ⟨n,I,rfl⟩
    have h := OGMVerified.actual_upper_bound (N:=0) I hL
    change SmoothGramModel.terminalLoss I (RealizationCore.W_of 0 d T.val) ≤ _
    simpa [SmoothGramModel.terminalLoss,OracleTrajectory.run_zero,SmoothBenchmark.theta_zero] using h
  · obtain ⟨I,hI⟩ := scalar_zero_query_witness L R hL hR (RealizationCore.W_of 0 d T.val)
    have hz : SmoothOperational.feasible 0 L R d T (L*R^2/2) :=
      ⟨0,I,hI.symm⟩
    exact le_iSup (fun z : {z : ℝ // SmoothOperational.feasible 0 L R d T z} =>
      (SmoothOperational.loss 0 d T z.val : EReal)) ⟨L*R^2/2,hz⟩

/-- With no oracle calls, every memory budget has the elementary quadratic value. -/
theorem operational_value_zero_query (m : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    MemoryDecision.value (SmoothOperational.feasible 0 L R) (SmoothOperational.loss 0)
      (SmoothOperational.memory 0) m = ((L*R^2/2 : ℝ) : EReal) := by
  apply le_antisymm
  · apply iInf_le_of_le ⟨SmoothOperational.zeroIncrement 0,SmoothOperational.zeroIncrement_mem 0 m⟩
    apply iInf_le_of_le (fun _ => 0)
    exact (operational_risk_zero_query L R hL hR _ _).le
  · exact le_iInf (fun T => le_iInf (fun d => (operational_risk_zero_query L R hL hR d T.val).ge))

theorem operational_thresholds_zero_query (m : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    MemoryDecision.thresholds (SmoothOperational.feasible 0 L R) (SmoothOperational.loss 0)
      (SmoothOperational.memory 0) m = Set.Ioi (L*R^2/2) :=
  MemoryDecision.thresholds_eq_ray_of_value_eq _ _ _ _ _
    (operational_value_zero_query m L R hL hR)

/-- The sharp operational minimax formula includes the zero-query endpoint. -/
theorem operational_value_eq_all_queries (N m : ℕ) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hm : 1 ≤ m) :
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) m = ((L*R^2/(2*(SmoothBenchmark.theta N N)^2) : ℝ) : EReal) := by
  by_cases hN : N = 0
  · subst N
    simpa [SmoothBenchmark.theta_zero] using operational_value_zero_query m L R hL hR
  · exact operational_value_eq N m L R (by omega) hL hR hm

end SmoothDrori
