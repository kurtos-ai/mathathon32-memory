module
public import Continuation.Projected.Operational
@[expose] public section
noncomputable section
open Set
namespace ProjectedOperational
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {K : Set E}
variable (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)

lemma memory_saturated (N m : ℕ) (hm : N/2 ≤ m) : memory N m = Set.univ := by
  apply Set.eq_univ_of_forall
  intro T k hk hkN
  have hw := MemoryRank.Incremental.S_k_rank_le_width N k T.val
  have hh := MemoryRank.Incremental.S_k_rank_le_height N k T.val
  omega

/-- The full projected family has no register restriction. -/
def unrestrictedValue (N : ℕ) (B : Set E) (R : ℝ) : EReal :=
  ⨅ T : RealizationCore.StrictIncrement N, ⨅ d : Fin N → ℝ,
    MemoryDecision.risk (feasible hK hcK hneK N B R) (loss N) d T

/-- The finite memory bound exhausts every projected coefficient map. -/
theorem value_eq_unrestricted (N m : ℕ) (B : Set E) (R : ℝ) (hm : N/2 ≤ m) :
    MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m =
      unrestrictedValue hK hcK hneK N B R := by
  apply le_antisymm
  · apply le_iInf
    intro T
    apply le_iInf
    intro d
    have ht : T ∈ memory N m := by rw [memory_saturated N m hm]; trivial
    exact iInf_le_of_le ⟨T,ht⟩ (iInf_le _ d)
  · apply le_iInf
    intro T
    apply le_iInf
    intro d
    exact iInf_le_of_le T.val (iInf_le _ d)

/-- A least sufficient budget exists among the finitely many budgets in the report. -/
theorem least_sufficient_budget (N : ℕ) (B : Set E) (R : ℝ) :
    ∃ m ≤ N/2, IsLeast {m | MemoryDecision.value (feasible hK hcK hneK N B R)
      (loss N) (memory N) m = unrestrictedValue hK hcK hneK N B R} m := by
  have hex : ∃ m, MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m =
      unrestrictedValue hK hcK hneK N B R :=
    ⟨N/2,value_eq_unrestricted hK hcK hneK N (N/2) B R le_rfl⟩
  refine ⟨Nat.find hex,Nat.find_min' hex (value_eq_unrestricted hK hcK hneK N (N/2) B R le_rfl),
    Nat.find_spec hex,?_⟩
  intro n hn
  exact Nat.find_min' hex hn

theorem strict_gain_iff (N m : ℕ) (B : Set E) (R : ℝ) :
    (MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) (m+1) <
      MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m) ↔
    (MemoryDecision.thresholds (feasible hK hcK hneK N B R) (loss N) (memory N) (m+1) \
      MemoryDecision.thresholds (feasible hK hcK hneK N B R) (loss N) (memory N) m).Nonempty :=
  MemoryDecision.gain_iff _ _ _ _

theorem strict_gain_rational_threshold (N m : ℕ) (B : Set E) (R : ℝ)
    (h : MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) (m+1) <
      MemoryDecision.value (feasible hK hcK hneK N B R) (loss N) (memory N) m) :
    ∃ q : ℚ, (q:ℝ) ∈
      MemoryDecision.thresholds (feasible hK hcK hneK N B R) (loss N) (memory N) (m+1) \
      MemoryDecision.thresholds (feasible hK hcK hneK N B R) (loss N) (memory N) m :=
  MemoryDecision.gain_has_rational_witness _ _ _ _ h

/-- Every bounded-oracle threshold set has one finite endpoint in [0,MR]. -/
theorem bounded_thresholds_eq_ray (N m : ℕ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ M*R ∧
      MemoryDecision.value (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
        (loss N) (memory N) m = (v:EReal) ∧
      MemoryDecision.thresholds (feasible hK hcK hneK N (Metric.closedBall (0:E) M) R)
        (loss N) (memory N) m = Set.Ioi v := by
  obtain ⟨v,hv0,hvM,hv⟩ := bounded_value_finite hK hcK hneK N m M R hM hR
  exact ⟨v,hv0,hvM,hv,thresholds_eq_ray hK hcK hneK N m _ R v hv⟩

end ProjectedOperational
