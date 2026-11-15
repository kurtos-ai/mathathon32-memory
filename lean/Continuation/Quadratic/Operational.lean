module
public import Continuation.Quadratic.Lower.Minimax
public import RealizationCore.Coordinates
public import Decision.ExactThresholds
@[expose] public section
noncomputable section
namespace QuadraticOperational
open QuadraticLower QuadraticSpectral QuadraticFoundations

/-- Feasibility is membership in the actual all-dimensional terminal loss set. -/
def feasible (N : ℕ) (L R : ℝ) (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N)
    (z : ℝ) : Prop := z ∈ historyLossSet N d T L R

def loss (N : ℕ) (_d : Fin N → ℝ) (_T : RealizationCore.StrictIncrement N) (z : ℝ) : ℝ := z

def memory (N m : ℕ) : Set (RealizationCore.StrictIncrement N) :=
  {T | MemoryRank.Incremental.Q N m T.val}

def zeroIncrement (N : ℕ) : RealizationCore.StrictIncrement N :=
  ⟨0,by intro i j _; rfl⟩

theorem mem_memory_iff_realization (N m : ℕ) (T : RealizationCore.StrictIncrement N)
    (d : Fin N → ℝ) : T ∈ memory N m ↔
    RegisterMachine.HasRealization N (RealizationCore.W_of N d T.val) (m+1) :=
  (RealizationCore.realization_iff_coordinates N m d T).symm

theorem zeroIncrement_mem (N m : ℕ) : zeroIncrement N ∈ memory N m :=
  MemoryRank.Incremental.zero_mem_Q N m

theorem schedule_has_one_register (N : ℕ) (L : ℝ) :
    RegisterMachine.HasRealization N (RealizationCore.W_of N (schedD N L) 0) 1 :=
  (RealizationCore.realization_iff_coordinates N 0 (schedD N L) (zeroIncrement N)).mpr
    (zeroIncrement_mem N 0)

theorem risk_lower_bound (N : ℕ) (L R : ℝ) (hL : 0 < L)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) :
    ((R^2/2 * (L/(2*(N:ℝ)+1)^2) : ℝ) : EReal) ≤
      MemoryDecision.risk (feasible N L R) (loss N) d T := by
  obtain ⟨x,hx,hb⟩ := pIter_lower_bound N L hL d T.val
  let z := R^2/2 * (x * (pIter N d T.val N).eval x^2)
  have hz : feasible N L R d T z := by
    rw [feasible,historyLossSet_eq]
    exact scalar_loss_mem L R _ x hx
  have hbound : R^2/2 * (L/(2*(N:ℝ)+1)^2) ≤ z :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  calc ((R^2/2 * (L/(2*(N:ℝ)+1)^2) : ℝ) : EReal) ≤ (z : EReal) := EReal.coe_le_coe_iff.mpr hbound
    _ ≤ MemoryDecision.risk (feasible N L R) (loss N) d T :=
      le_iSup (fun w : {z : ℝ // feasible N L R d T z} => (loss N d T w.val : EReal)) ⟨z,hz⟩

theorem schedule_risk (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    MemoryDecision.risk (feasible N L R) (loss N) (schedD N L) (zeroIncrement N) =
      ((R^2/2 * (L/(2*(N:ℝ)+1)^2) : ℝ) : EReal) := by
  apply le_antisymm
  · apply (MemoryDecision.risk_le_iff _ _ _ _ _).mpr
    intro z hz
    exact (historyLossSet_schedD_isGreatest N L R hL).2 hz
  · exact risk_lower_bound N L R hL _ _

/-- Independently defined minimax infimum at every operational memory budget. -/
theorem value_eq (N m : ℕ) (L R : ℝ) (hL : 0 < L) :
    MemoryDecision.value (feasible N L R) (loss N) (memory N) m =
      ((L*R^2/(2*(2*(N:ℝ)+1)^2) : ℝ) : EReal) := by
  have heq : L*R^2/(2*(2*(N:ℝ)+1)^2) = R^2/2*(L/(2*(N:ℝ)+1)^2) := by
    have hM : 2*(N:ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [heq]
  apply le_antisymm
  · apply iInf_le_of_le ⟨zeroIncrement N,zeroIncrement_mem N m⟩
    apply iInf_le_of_le (schedD N L)
    exact (schedule_risk N L R hL).le
  · apply le_iInf
    intro T
    apply le_iInf
    intro d
    exact risk_lower_bound N L R hL d T.val

theorem thresholds_eq (N m : ℕ) (L R : ℝ) (hL : 0 < L) :
    MemoryDecision.thresholds (feasible N L R) (loss N) (memory N) m =
      Set.Ioi (L*R^2/(2*(2*(N:ℝ)+1)^2)) :=
  MemoryDecision.thresholds_eq_ray_of_value_eq _ _ _ _ _ (value_eq N m L R hL)

theorem no_memory_gain (N m : ℕ) (L R : ℝ) (hL : 0 < L) :
    ¬ MemoryDecision.value (feasible N L R) (loss N) (memory N) (m+1) <
      MemoryDecision.value (feasible N L R) (loss N) (memory N) m := by
  rw [value_eq N (m+1) L R hL,value_eq N m L R hL]
  exact lt_irrefl _

end QuadraticOperational
