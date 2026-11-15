module
public import Continuation.Smooth.GramExact
public import Continuation.Smooth.Attain.ScalarRisk
public import RealizationCore.Coordinates
public import Decision.ExactThresholds
@[expose] public section

noncomputable section
namespace SmoothOperational
variable {N n : ℕ} {L R : ℝ}

theorem iter_cumulative (I : SmoothAttain.Instance n L R) (α : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) :
    SmoothAttain.iter I α k = I.x0 + ∑ j : Fin k,
      (-α ⟨j.val, by omega⟩) • I.G (SmoothAttain.iter I α j.val) := by
  induction k with
  | zero => simp [SmoothAttain.iter]
  | succ k ih =>
    have hkN : k < N := by omega
    rw [SmoothAttain.iter, dite_eq_left hkN, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← add_assoc, ← ih (by omega)]
    simp [neg_smul, sub_eq_add_neg]

/-- The zero-increment history map executes precisely the one-register step schedule. -/
theorem zero_increment_trajectory (I : SmoothAttain.Instance n L R) (α : Fin N → ℝ) :
    OracleTrajectory.run (RealizationCore.W_of N (fun j => -α j) 0) I.G I.x0 =
      fun i => SmoothAttain.iter I α i.val := by
  symm
  apply OracleTrajectory.unique
  intro i
  rw [iter_cumulative I α i.val (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val < i.val := j.isLt
  simp [RealizationCore.W_of, RealizationCore.extendedIncrement, hj]

theorem zero_increment_loss (I : SmoothAttain.Instance n L R) (α : Fin N → ℝ) :
    SmoothGramModel.terminalLoss I (RealizationCore.W_of N (fun j => -α j) 0) =
      SmoothAttain.terminalLoss I α := by
  simp only [SmoothGramModel.terminalLoss, zero_increment_trajectory,
    SmoothAttain.terminalLoss, Fin.val_last]

def feasible (N : ℕ) (L R : ℝ) (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N)
    (z : ℝ) : Prop := z ∈ SmoothGramModel.actualLossSet N (RealizationCore.W_of N d T.val) L R

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

theorem mem_memory_zero_iff (T : RealizationCore.StrictIncrement N) :
    T ∈ memory N 0 ↔ T = zeroIncrement N := by
  change MemoryRank.Incremental.Q N 0 T.val ↔ _
  rw [MemoryRank.Incremental.Q_zero_iff N T.val T.property]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem actualLossSet_iff (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (z : ℝ) :
    z ∈ SmoothGramModel.actualLossSet N W L R ↔
      ∃ I : SmoothAttain.AllInstances L R, z = SmoothGramModel.terminalLoss I.2 W := by
  constructor
  · rintro ⟨n,I,hz⟩
    exact ⟨⟨⟨n+1,by omega⟩,I⟩,hz⟩
  · rintro ⟨⟨⟨n,hn⟩,I⟩,hz⟩
    cases n with
    | zero => omega
    | succ n => exact ⟨n,I,hz⟩

theorem zero_increment_risk (α : Fin N → ℝ) :
    MemoryDecision.risk (feasible N L R) (loss N) (fun j => -α j) (zeroIncrement N) =
      SmoothAttain.risk0 L R α := by
  apply le_antisymm
  · apply iSup_le
    intro z
    obtain ⟨⟨k,I⟩,hz⟩ := (actualLossSet_iff _ z.val).mp z.property
    change z.val = SmoothGramModel.terminalLoss I (RealizationCore.W_of N (fun j => -α j) 0) at hz
    rw [zero_increment_loss] at hz
    change (z.val : EReal) ≤ SmoothAttain.risk0 L R α
    rw [hz]
    exact le_iSup (fun I : SmoothAttain.AllInstances L R =>
      (SmoothAttain.terminalLoss I.2 α : EReal)) ⟨k,I⟩
  · apply iSup_le
    intro I
    change (SmoothAttain.terminalLoss I.2 α : EReal) ≤
      ⨆ z : {z : ℝ // feasible N L R (fun j => -α j) (zeroIncrement N) z}, (z.val : EReal)
    have hz : feasible N L R (fun j => -α j) (zeroIncrement N)
        (SmoothAttain.terminalLoss I.2 α) := by
      apply (actualLossSet_iff _ _).mpr
      exact ⟨I,(zero_increment_loss I.2 α).symm⟩
    exact le_iSup (fun z : {z : ℝ // feasible N L R (fun j => -α j) (zeroIncrement N) z} =>
      (z.val : EReal)) ⟨SmoothAttain.terminalLoss I.2 α,hz⟩

/-- The operational one-register minimax problem equals minimization over step schedules. -/
theorem value_zero_eq_inf_risk0 :
    MemoryDecision.value (feasible N L R) (loss N) (memory N) 0 =
      ⨅ α : Fin N → ℝ, SmoothAttain.risk0 L R α := by
  apply le_antisymm
  · apply le_iInf
    intro α
    apply iInf_le_of_le ⟨zeroIncrement N,zeroIncrement_mem N 0⟩
    apply iInf_le_of_le (fun j => -α j)
    exact (zero_increment_risk α).le
  · apply le_iInf
    intro T
    apply le_iInf
    intro d
    have hT : T.val = zeroIncrement N := (mem_memory_zero_iff T.val).mp T.property
    rw [hT]
    apply iInf_le_of_le (fun j => -d j)
    have h := zero_increment_risk (L:=L) (R:=R) (fun j => -d j)
    simpa only [neg_neg] using h.symm.le

/-- The paper's performance test uses finite Gram data, without an unknown risk value. -/
theorem performance_iff_gram (hL : 0 < L) (hR : 0 ≤ R)
    (T : RealizationCore.StrictIncrement N) (γ : ℝ) :
    T ∈ MemoryDecision.performance (feasible N L R) (loss N) γ ↔
      ∃ d : Fin N → ℝ, ∃ b : ℝ, b < γ ∧
        ∀ M φ, SmoothGramModel.Feasible (RealizationCore.W_of N d T.val) L R M φ →
          φ (Fin.last N) ≤ b := by
  change (∃ d, ∃ b, b < γ ∧ ∀ z, feasible N L R d T z → loss N d T z ≤ b) ↔ _
  constructor
  · rintro ⟨d,b,hb,h⟩
    exact ⟨d,b,hb,(SmoothGramModel.uniform_bound_iff N _ L R b hL hR).mp h⟩
  · rintro ⟨d,b,hb,h⟩
    exact ⟨d,b,hb,(SmoothGramModel.uniform_bound_iff N _ L R b hL hR).mpr h⟩

end SmoothOperational
