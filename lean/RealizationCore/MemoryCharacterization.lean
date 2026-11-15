module
public import RealizationCore.RealizationTheorem
public import MemoryRank.ZeroLocus
@[expose] public section
noncomputable section

namespace RegisterMachine

/-- Operational realizability is characterized by the independently defined
maximum cut rank. -/
theorem realization_iff_maxCutRank (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) :
    HasRealization N W s ↔ MemoryRank.CutRank.memRank N W ≤ s := by
  constructor
  · exact maxCutRank_le_registers N s W
  · intro hs
    apply (realization_iff_rank_all W s).mpr
    intro k hk
    have hcut : (MemoryRank.CutRank.H_k N k hk W).rank ≤
        MemoryRank.CutRank.memRank N W := by
      exact Finset.le_sup (f := fun q : Fin (N+1) =>
        (MemoryRank.CutRank.H_k N q.val (by omega) W).rank)
        (Finset.mem_univ (⟨k, by omega⟩ : Fin (N+1)))
    exact le_trans (by simpa [H_k, MemoryRank.CutRank.H_k] using hcut) hs

/-- The maximum cut rank is the least number of registers among actual
recursive implementations; it is not used as the definition of realizability. -/
theorem isLeast_registerCount (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    IsLeast {s : ℕ | HasRealization N W s} (MemoryRank.CutRank.memRank N W) := by
  constructor
  · exact (realization_iff_maxCutRank N W _).mpr le_rfl
  · intro s hs
    exact (realization_iff_maxCutRank N W s).mp hs

/-- The increment rank locus is exactly the locus of maps realizable with
`m+1` total registers. The omitted endpoint blocks have rank zero. -/
theorem realization_iff_incrementLocus (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (m : ℕ) :
    HasRealization N W (m+1) ↔
      MemoryRank.Incremental.Q N m (RealizationCore.T_of N W) := by
  have hS : ∀ k, RealizationCore.S_k_of N k W =
      MemoryRank.Incremental.S_k N k (RealizationCore.T_of N W) := by
    intro k
    rfl
  constructor
  · intro hr k hk1 hkN
    have h := increment_rank_lower_bound N (m+1) W k (by omega) hr
    rw [hS] at h
    omega
  · intro hQ
    apply (realization_iff_rank_all W (m+1)).mpr
    intro k hk
    rw [cutMatrix_eq, RealizationCore.rank_H_eq_one_add_rank_S, hS]
    by_cases hk0 : k = 0
    · subst k
      have h := MemoryRank.Incremental.S_k_rank_le_width N 0 (RealizationCore.T_of N W)
      omega
    · by_cases hkN : k = N
      · subst k
        have h := MemoryRank.Incremental.S_k_rank_le_height N N (RealizationCore.T_of N W)
        omega
      · have h := hQ k (by omega) (by omega)
        omega

/-- One total register is possible exactly when all strict-history increments
vanish, including the horizons with no interior cuts. -/
theorem one_register_iff_zero_increment (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    HasRealization N W 1 ↔ RealizationCore.T_of N W = 0 := by
  have htri : ∀ i j, i.val ≤ j.val → RealizationCore.T_of N W i j = 0 := by
    intro i j hij
    dsimp only [RealizationCore.T_of, Matrix.of_apply]
    split_ifs with h
    · omega
    · rfl
  exact (realization_iff_incrementLocus N W 0).trans
    (MemoryRank.Incremental.Q_zero_iff N (RealizationCore.T_of N W) htri)

end RegisterMachine
