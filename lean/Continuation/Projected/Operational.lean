module
public import Continuation.Projected.LossModel
public import Continuation.Projected.UpperBound
public import RealizationCore.Coordinates
public import Decision.ExactThresholds
@[expose] public section
noncomputable section
open Set
namespace ProjectedOperational
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {K : Set E}
variable (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)

def feasible (N : ℕ) (B : Set E) (R : ℝ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (z : ℝ) : Prop :=
  z ∈ ProjectedLossModel.actualLossSet (B:=B) hK hcK hneK (RealizationCore.W_of N d T.val) R

def loss (N : ℕ) (_d : Fin N → ℝ) (_T : RealizationCore.StrictIncrement N) (z : ℝ) : ℝ := z

def memory (N m : ℕ) : Set (RealizationCore.StrictIncrement N) :=
  {T | MemoryRank.Incremental.Q N m T.val}

def zeroIncrement (N : ℕ) : RealizationCore.StrictIncrement N := ⟨0,by intros; rfl⟩

lemma zeroIncrement_mem (N m : ℕ) : zeroIncrement N ∈ memory N m :=
  MemoryRank.Incremental.zero_mem_Q N m

/-- The operational memory constraint is exactly realizability of the actual projected recurrence. -/
theorem mem_memory_iff_projected (hKn : K.Nontrivial) (N m : ℕ)
    (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N) :
    T ∈ memory N m ↔ Continuation.Projected.HasProjectedRealization hK hcK hneK
      (RealizationCore.W_of N d T.val) (m+1) := by
  rw [Continuation.Projected.projected_realization_iff_ordinary hK hcK hneK hKn]
  exact (RealizationCore.realization_iff_coordinates N m d T).symm

/-- The independent minimax infimum can equivalently quantify over actual projected register programs. -/
theorem value_eq_inf_projected (hKn : K.Nontrivial) (N m : ℕ) (B : Set E) (R : ℝ) :
    MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m =
      ⨅ d : Fin N → ℝ, ⨅ T : RealizationCore.StrictIncrement N,
        ⨅ _ : Continuation.Projected.HasProjectedRealization hK hcK hneK
          (RealizationCore.W_of N d T.val) (m+1),
        MemoryDecision.risk (feasible hK hcK hneK N B R) (loss N) d T := by
  apply le_antisymm
  · apply le_iInf
    intro d
    apply le_iInf
    intro T
    apply le_iInf
    intro h
    exact iInf_le_of_le ⟨T,(mem_memory_iff_projected hK hcK hneK hKn N m d T).mpr h⟩
      (iInf_le _ d)
  · apply le_iInf
    intro T
    apply le_iInf
    intro d
    exact iInf_le_of_le d (iInf_le_of_le T.val (iInf_le _
      ((mem_memory_iff_projected hK hcK hneK hKn N m d T.val).mp T.property)))

/-- The displayed finite projected interpolation formula is precisely the actual performance set. -/
theorem mem_performance_iff_model (N : ℕ) (B : Set E) (R : ℝ)
    (hB0 : (0:E) ∈ B) (hR : 0 ≤ R) (T : RealizationCore.StrictIncrement N) (γ : ℝ) :
    T ∈ MemoryDecision.performance (feasible hK hcK hneK N B R) (loss N) γ ↔
      ∃ d : Fin N → ℝ, ∃ b : ℝ, b < γ ∧
        ∀ xStar x g φ, ProjectedLossModel.Feasible (RealizationCore.W_of N d T.val) K B R
          xStar x g φ → φ (Fin.last N) ≤ b := by
  constructor
  · rintro ⟨d,b,hb,h⟩
    refine ⟨d,b,hb,?_⟩
    intro xStar x g φ hF
    apply h
    change φ (Fin.last N) ∈ ProjectedLossModel.actualLossSet hK hcK hneK _ R
    rw [ProjectedLossModel.lossSet_eq hK hcK hneK hB0 hR]
    exact ⟨xStar,x,g,φ,hF,rfl⟩
  · rintro ⟨d,b,hb,h⟩
    refine ⟨d,b,hb,?_⟩
    intro z hz
    change z ∈ ProjectedLossModel.actualLossSet hK hcK hneK _ R at hz
    rw [ProjectedLossModel.lossSet_eq hK hcK hneK hB0 hR] at hz
    rcases hz with ⟨xStar,x,g,φ,hF,rfl⟩
    exact h xStar x g φ hF

theorem threshold_iff_value_lt (N m : ℕ) (B : Set E) (R γ : ℝ) :
    γ ∈ MemoryDecision.thresholds (feasible hK hcK hneK N B R) (loss N) (memory N) m ↔
      MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m < (γ:EReal) :=
  MemoryDecision.threshold_iff_value_lt _ _ _ _ _

theorem thresholds_eq_ray (N m : ℕ) (B : Set E) (R v : ℝ)
    (hv : MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m = (v:EReal)) :
    MemoryDecision.thresholds (feasible hK hcK hneK N B R) (loss N) (memory N) m = Set.Ioi v :=
  MemoryDecision.thresholds_eq_ray_of_value_eq _ _ _ _ _ hv

theorem thresholds_empty_iff (N m : ℕ) (B : Set E) (R : ℝ) :
    MemoryDecision.thresholds (feasible hK hcK hneK N B R) (loss N) (memory N) m = ∅ ↔
      MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m = ⊤ :=
  MemoryDecision.thresholds_empty_iff_value_top _ _ _ _

lemma zero_loss_mem (N : ℕ) (B : Set E) (R : ℝ) (hB0 : (0:E) ∈ B) (hR : 0 ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    0 ∈ ProjectedLossModel.actualLossSet (B:=B) hK hcK hneK W R := by
  obtain ⟨a,ha⟩ := hneK
  let I : ProjectedLossModel.Instance K B R :=
    { f := fun _ => 0
      convex := convexOn_const 0 hK
      subgrad := fun x _ => ⟨0,hB0,by intro y hy; simp⟩
      x0 := a
      xStar := a
      hx0 := ha
      hxStar := ha
      isMin := by intro y hy; simp
      near := by simpa using hR }
  refine ⟨I,(fun _ => 0),?_,by simp [ProjectedLossModel.terminalLoss,I]⟩
  intro k
  exact ⟨hB0,by intro y hy; simp [I]⟩

lemma feasible_nonneg (N : ℕ) (B : Set E) (R : ℝ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (z : ℝ)
    (hz : feasible hK hcK hneK N B R d T z) : 0 ≤ z := by
  rcases hz with ⟨I,g,hadm,rfl⟩
  apply sub_nonneg.mpr
  exact I.isMin (ProjectedLossModel.direct_mem hK hcK hneK _ I.x0 I.hx0 g N le_rfl)

theorem value_nonneg (N m : ℕ) (B : Set E) (R : ℝ) (hB0 : (0:E) ∈ B) (hR : 0 ≤ R) :
    0 ≤ MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m := by
  exact MemoryDecision.value_nonneg _ _ _ _
    (fun d T => ⟨0,zero_loss_mem hK hcK hneK N B R hB0 hR _⟩)
    (feasible_nonneg hK hcK hneK N B R)

/-- A bounded relative-subgradient oracle gives a finite actual minimax value at every budget. -/
theorem bounded_value_bounds (N m : ℕ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    0 ≤ MemoryDecision.value (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
      (loss N) (memory N) m ∧
    MemoryDecision.value (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
      (loss N) (memory N) m ≤ ((M*R:ℝ):EReal) := by
  refine ⟨value_nonneg hK hcK hneK N m _ R (Metric.mem_closedBall_self hM) hR,?_⟩
  have hv : MemoryDecision.value (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
      (loss N) (memory N) m ≤
      MemoryDecision.risk (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
        (loss N) (0 : Fin N → ℝ) (zeroIncrement N) := by
    unfold MemoryDecision.value
    exact iInf_le_of_le ⟨zeroIncrement N,zeroIncrement_mem N m⟩ (iInf_le _ (0 : Fin N → ℝ))
  apply hv.trans
  apply (MemoryDecision.risk_le_iff _ _ _ _ _).mpr
  rintro z ⟨I,g,hadm,rfl⟩
  have hz : RealizationCore.W_of N (0 : Fin N → ℝ) (zeroIncrement N).val = 0 := by
    ext i j
    simp [RealizationCore.W_of,RealizationCore.extendedIncrement,zeroIncrement]
  change ProjectedLossModel.terminalLoss hK hcK hneK I _ g ≤ M*R
  rw [hz]
  exact ProjectedLossModel.bounded_zero_loss hK hcK hneK I g

theorem bounded_value_finite (N m : ℕ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ M*R ∧
      MemoryDecision.value (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
        (loss N) (memory N) m = (v:EReal) := by
  let V := MemoryDecision.value (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
    (loss N) (memory N) m
  obtain ⟨hl,hu⟩ := bounded_value_bounds hK hcK hneK N m M R hM hR
  have ht : V ≠ ⊤ := ne_of_lt (hu.trans_lt (EReal.coe_lt_top _))
  have hb : V ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe 0).trans_le hl)
  have he : V = (V.toReal:EReal) := (EReal.coe_toReal ht hb).symm
  refine ⟨V.toReal,?_,?_,he⟩
  · exact EReal.coe_le_coe_iff.mp (by simpa only [← he,EReal.coe_zero] using hl)
  · exact EReal.coe_le_coe_iff.mp (by simpa only [← he] using hu)

end ProjectedOperational
