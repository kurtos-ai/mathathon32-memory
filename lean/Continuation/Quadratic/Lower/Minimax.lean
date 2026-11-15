module
public import Continuation.Quadratic.Lower.Alternation
public import Continuation.Quadratic.Lower.Schedule
public import Decision.ExactThresholds
@[expose] public section
noncomputable section

/-!
# Exact one-register risk and the quadratic lower bound at every method

`history_risk_value` (Schedule) is an existential: some maximiser `μ` with the
`historyLossSet` supremum expressed through `μ`. This file removes the existential and
states the constant explicitly, then instantiates the alternation lower bound at the
coefficient polynomial of an **arbitrary** method `(d, T)`.
-/
namespace QuadraticLower
open Polynomial QuadraticFoundations QuadraticSpectral

/-- Explicit constant risk of the one-register Chebyshev schedule. -/
theorem historyLossSet_schedD_sSup (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    sSup (historyLossSet N (schedD N L)
        ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R)
      = R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) := by
  have h := historyLossSet_schedD_isGreatest N L R hL
  exact h.isLUB.csSup_eq ⟨_, h.1⟩

/-- The same value, written as the paper's `L R² / (2 (2N+1)²)`. -/
theorem historyLossSet_schedD_sSup_eq_quadMinimaxValue (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    sSup (historyLossSet N (schedD N L)
        ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R)
      = L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) := by
  rw [historyLossSet_schedD_sSup N L R hL]
  have hM : (2 * (N : ℝ) + 1) ≠ 0 := ne_of_gt (M_pos N)
  field_simp

/-- For every coefficient recurrence, some point in [0,L] has scalar weight at least L/(2N+1)². -/
theorem pIter_lower_bound (N : ℕ) (L : ℝ) (hL : 0 < L)
    (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) :
    ∃ x ∈ Set.Icc 0 L,
      L / (2 * (N : ℝ) + 1) ^ 2 ≤ x * (pIter N d T N).eval x ^ 2 :=
  quadratic_lower_bound N L hL (pIter N d T N)
    (pIter_natDegree_le N d T N (le_refl N)) (pIter_eval_zero N d T N (le_refl N))

/-- Every coefficient recurrence has an attainable scalar quadratic loss at least the schedule's worst-case value. -/
theorem quad_minimax_lower (N : ℕ) (L R : ℝ) (hL : 0 < L)
    (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) :
    R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) ≤
      sSup (lossSet L R (pIter N d T N)) := by
  obtain ⟨x, hx, hbound⟩ := pIter_lower_bound N L hL d T
  have hmem : R ^ 2 / 2 * (x * (pIter N d T N).eval x ^ 2)
      ∈ lossSet L R (pIter N d T N) := scalar_loss_mem L R _ x hx
  refine le_trans ?_ (le_csSup ?_ hmem)
  · have hR : 0 ≤ R ^ 2 / 2 := by positivity
    exact mul_le_mul_of_nonneg_left hbound hR
  · -- the loss set is bounded above by the scalar supremum, in particular by a
    -- bound of the form `R²/2 * B` when `x p(x)² ≤ B` on `[0,L]`; for our purpose it
    -- suffices to note the set is bounded by its own `IsGreatest` witness.
    obtain ⟨μ, hμ, _, hgreat⟩ := spectral_risk_attained L R hL.le (pIter N d T N)
    exact ⟨_, fun y hy => hgreat.2 hy⟩

/-- The coefficient space: an arbitrary predetermined method `(d, T)`. -/
abbrev Coeff (N : ℕ) : Type := (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ

/-- Independent risk definition: the supremum of attainable terminal losses over all
positive finite dimensions and all admissible quadratic instances, computed from the
method's own error polynomial. No minimax value is substituted. -/
noncomputable def riskOf (N : ℕ) (L R : ℝ) (c : Coeff N) : ℝ :=
  sSup (lossSet L R (pIter N c.1 c.2 N))

lemma bddAbove_lossSet (N : ℕ) (L R : ℝ) (hL : 0 < L) (c : Coeff N) :
    BddAbove (lossSet L R (pIter N c.1 c.2 N)) := by
  obtain ⟨μ, -, -, hg⟩ := spectral_risk_attained L R hL.le (pIter N c.1 c.2 N)
  exact ⟨_, fun y hy => hg.2 hy⟩

/-- **Lower half.** Every coefficient map's risk is at least the one-register value. -/
theorem risk_ge_constant (N : ℕ) (L R : ℝ) (hL : 0 < L) (c : Coeff N) :
    L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) ≤ riskOf N L R c := by
  show L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) ≤ sSup (lossSet L R (pIter N c.1 c.2 N))
  have hbase : R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) ≤
      sSup (lossSet L R (pIter N c.1 c.2 N)) := quad_minimax_lower N L R hL c.1 c.2
  have heq : R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) =
      L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) := by
    have hM : (2 * (N : ℝ) + 1) ≠ 0 := ne_of_gt (M_pos N)
    field_simp
  rwa [heq] at hbase

/-- **Upper half.** The Chebyshev schedule attains the constant. -/
theorem risk_schedD_le_constant (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    riskOf N L R (schedD N L, schedT N) ≤
      L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) := by
  show sSup (lossSet L R (pIter N (schedD N L) (schedT N) N)) ≤
    L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2)
  have hp : pIter N (schedD N L) (schedT N) N = p_star N L := by
    have := schedD_pN_eq_p_star N L hL
    simpa [QuadraticFoundations.pN] using this
  rw [hp, ← historyLossSet_schedD_sSup_eq_quadMinimaxValue N L R hL]
  have hgreat := p_star_lossSet_isGreatest N L R hL
  have hs : sSup (lossSet L R (p_star N L)) = R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) :=
    hgreat.isLUB.csSup_eq ⟨_, hgreat.1⟩
  have hhist : sSup (historyLossSet N (schedD N L)
      ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R) =
      R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) :=
    historyLossSet_schedD_sSup N L R hL
  rw [hhist]
  exact (hs ▸ le_rfl)

/-- The schedule's risk is exactly the constant. -/
theorem risk_schedD_eq_constant (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    riskOf N L R (schedD N L, schedT N) =
      L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) :=
  le_antisymm (risk_schedD_le_constant N L R hL) (risk_ge_constant N L R hL _)

/-- **The quadratic minimax value.** The infimum of the risk over *all* coefficient maps
is exactly `L R² / (2 (2N+1)²)`, and the one-register Chebyshev schedule attains it. -/
theorem sInf_risk_eq (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    sInf (Set.range (riskOf N L R)) = L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) := by
  have hbdd : ∀ a ∈ Set.range (riskOf N L R),
      L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) ≤ a := by
    rintro a ⟨c, rfl⟩
    exact risk_ge_constant N L R hL c
  refine le_antisymm ?_ (le_csInf (Set.range_nonempty (riskOf N L R)) hbdd)
  have hsched : riskOf N L R (schedD N L, schedT N) =
      L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) := risk_schedD_eq_constant N L R hL
  have hmem : L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) ∈ Set.range (riskOf N L R) :=
    ⟨(schedD N L, schedT N), hsched⟩
  exact csInf_le (a := L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2)) ⟨_, hbdd⟩ hmem


/-! ### Memory admissibility and the threshold sets -/

/-- `T = 0` satisfies every memory budget `m` (including `m = 0`): all `S_k` blocks are
zero, so all ranks are `0 ≤ m`. This is the `m+1`-register admissibility of the
one-register schedule for every budget. -/
theorem schedT_in_Q (N m : ℕ) : MemoryRank.Incremental.Q N m (schedT N) := by
  intro k hk1 hk2
  have hS : MemoryRank.Incremental.S_k N k (schedT N) = 0 := by
    ext i j
    simp [MemoryRank.Incremental.S_k, schedT]
  rw [hS, Matrix.rank_zero]
  exact Nat.zero_le m

/-- **Every** coefficient map obeys the constant lower bound; hence no method at any
memory budget can reach a strictly smaller risk. -/
theorem all_methods_lower_bound (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    ∀ c : Coeff N, L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) ≤ riskOf N L R c :=
  fun c => risk_ge_constant N L R hL c

/-- The minimum is attained *inside every memory locus*: the one-register schedule is
`Q`-admissible for each `m` and realises the constant. -/
theorem minimax_attained_in_Q (N : ℕ) (L R : ℝ) (hL : 0 < L) (m : ℕ) :
    ∃ c : Coeff N, MemoryRank.Incremental.Q N m c.2 ∧
      riskOf N L R c = L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) :=
  ⟨(schedD N L, schedT N), schedT_in_Q N m, risk_schedD_eq_constant N L R hL⟩

/-- The performance threshold set `{γ | some budget-`m` method has risk < γ}` is exactly
the open ray above the constant. `mem_performance_iff` style: membership iff `γ` exceeds
the minimax value. -/
theorem threshold_set_eq_Ioi (N : ℕ) (L R : ℝ) (hL : 0 < L) (m : ℕ) :
    {γ : ℝ | ∃ c : Coeff N, MemoryRank.Incremental.Q N m c.2 ∧ riskOf N L R c < γ}
      = Set.Ioi (L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2)) := by
  ext γ
  constructor
  · rintro ⟨c, _, hc⟩
    exact lt_of_le_of_lt (risk_ge_constant N L R hL c) hc
  · intro hγ
    exact ⟨(schedD N L, schedT N), schedT_in_Q N m,
      (risk_schedD_eq_constant N L R hL) ▸ hγ⟩

end QuadraticLower

