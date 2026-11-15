module
public import Continuation.Semialgebraic.SmoothProcedureInput
public import Continuation.Semialgebraic.EffectiveProcedure
public import Continuation.GJP.OperationalGap
@[expose] public section
namespace MemorySemialgebraic.SmoothProcedure
open SymbolicQE

@[irreducible] def endpoint (N m : ℕ) (L R : ℚ) : EndpointSelection.Output :=
  EffectiveProcedure.methodEndpoint N m (SmoothProcedureInput.input N L R)

def strictGain (N m : ℕ) (L R : ℚ) : Bool :=
  EffectiveProcedure.strictGain N m (SmoothProcedureInput.input N L R)

def leastSufficientMemory (N : ℕ) (L R : ℚ) : Option ℕ :=
  EffectiveProcedure.leastSufficientMemory N (SmoothProcedureInput.input N L R)

/-- The returned isolating code denotes the independent actual smooth minimax value. -/
theorem endpoint_correct (N m : ℕ) (L R : ℚ) (hL : 0 < (L:ℝ)) (hR : 0 ≤ (R:ℝ)) :
    (endpoint N m L R).Denotes
      (MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
        (SmoothOperational.memory N) m) := by
  unfold endpoint
  exact EffectiveProcedure.methodEndpoint_correct N m _ _ (SmoothProcedureInput.input_correct N L R hL hR)

/-- For every positive additional-memory budget, the program returns the sharp smooth benchmark. -/
theorem endpoint_sharp (N m : ℕ) (L R : ℚ)
    (hL : 0 < (L:ℝ)) (hR : 0 < (R:ℝ)) (hm : 1 ≤ m) :
    (endpoint N m L R).Denotes
      ((((L:ℝ)*(R:ℝ)^2/(2*(SmoothBenchmark.theta N N)^2)) : ℝ) : EReal) := by
  have h := endpoint_correct N m L R hL hR.le
  rwa [SmoothDrori.operational_value_eq_all_queries N m L R hL hR hm] at h

/-- The zero-query endpoint is exact even with no additional register. -/
theorem endpoint_zero_query (m : ℕ) (L R : ℚ) (hL : 0 < (L:ℝ)) (hR : 0 < (R:ℝ)) :
    (endpoint 0 m L R).Denotes (((L:ℝ)*(R:ℝ)^2/2 : ℝ) : EReal) := by
  have h := endpoint_correct 0 m L R hL hR.le
  rwa [SmoothDrori.operational_value_zero_query m L R hL hR] at h

/-- The one-query endpoint is exact at every memory budget. -/
theorem endpoint_one_query (m : ℕ) (L R : ℚ) (hL : 0 < (L:ℝ)) (hR : 0 < (R:ℝ)) :
    (endpoint 1 m L R).Denotes (((L:ℝ)*(R:ℝ)^2/8 : ℝ) : EReal) := by
  have h := endpoint_correct 1 m L R hL hR.le
  rwa [SmoothDrori.operational_value_one_query m L R hL hR] at h

/-- The executable gain decision recovers the full smooth memory-separation classification. -/
theorem strictGain_correct (N m : ℕ) (L R : ℚ) (hL : 0 < (L:ℝ)) (hR : 0 < (R:ℝ)) :
    strictGain N m L R = true ↔ m=0 ∧ 2 ≤ N := by
  have h := EffectiveProcedure.strictGain_correct N m (SmoothProcedureInput.input N L R)
    (SmoothOperational.feasible N L R) (SmoothProcedureInput.input_correct N L R hL hR.le)
  exact h.trans (GJP.operational_strict_gain_iff m L R hL hR)

/-- The least sufficient budget is established independently from the computed scan. -/
theorem least_budget (N : ℕ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    IsLeast {j : ℕ | MemoryDecision.value (SmoothOperational.feasible N L R)
      (SmoothOperational.loss N) (SmoothOperational.memory N) j =
        MemorySelection.unrestrictedValue (SmoothOperational.feasible N L R) (SmoothOperational.loss N)}
      (if N ≤ 1 then 0 else 1) := by
  have hfull (m : ℕ) (hm : N/2 ≤ m) :
      MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
        (SmoothOperational.memory N) m =
          MemorySelection.unrestrictedValue (SmoothOperational.feasible N L R) (SmoothOperational.loss N) :=
    MemorySelection.value_eq_unrestricted _ _ m hm
  by_cases hN : N ≤ 1
  · rw [ite_eq_left hN]
    exact ⟨hfull 0 (by omega),fun _ _ => Nat.zero_le _⟩
  · rw [ite_eq_right hN]
    have h1 : MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
        (SmoothOperational.memory N) 1 =
          MemorySelection.unrestrictedValue (SmoothOperational.feasible N L R) (SmoothOperational.loss N) := by
      rw [← hfull (N/2) le_rfl,
        SmoothDrori.operational_value_eq_all_queries N 1 L R hL hR le_rfl,
        SmoothDrori.operational_value_eq_all_queries N (N/2) L R hL hR (by omega)]
    refine ⟨h1,?_⟩
    intro j hj
    by_contra hjn
    have hj0 : j=0 := by omega
    subst j
    have hg := GJP.operational_strict_gain L R (show 2 ≤ N by omega) hL hR
    rw [h1,hj] at hg
    exact lt_irrefl _ hg

/-- The actual finite scan returns zero for at most one query, and one thereafter. -/
theorem leastSufficientMemory_correct (N : ℕ) (L R : ℚ) (hL : 0 < (L:ℝ)) (hR : 0 < (R:ℝ)) :
    leastSufficientMemory N L R = if N ≤ 1 then some 0 else some 1 := by
  obtain ⟨m,hm,hout,hmin⟩ := EffectiveProcedure.leastSufficientMemory_correct N
    (SmoothProcedureInput.input N L R) (SmoothOperational.feasible N L R)
    (SmoothProcedureInput.input_correct N L R hL hR.le)
  have hleast := least_budget N L R hL hR
  have heq : m=(if N ≤ 1 then 0 else 1) := le_antisymm (hmin.2 hleast.1) (hleast.2 hmin.1)
  change EffectiveProcedure.leastSufficientMemory N (SmoothProcedureInput.input N L R) = _
  rw [hout,heq]
  split <;> rfl

end MemorySemialgebraic.SmoothProcedure
