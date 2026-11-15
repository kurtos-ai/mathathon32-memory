module
public import Mathlib
public import MemoryRank.IncrementalRank
@[expose] public section
noncomputable section
namespace MemoryRank.Incremental

theorem matrix_eq_zero_of_rank_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (h : A.rank = 0) : A = 0 := by
  have hspan : Submodule.span ℝ (Set.range A.col) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    simpa only [Matrix.rank_eq_finrank_span_cols] using h
  ext i j
  have hc : A.col j ∈ Submodule.span ℝ (Set.range A.col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [hspan] at hc
  have hc0 : A.col j = 0 := hc
  exact congrFun hc0 i

/-- On the strictly lower triangular coefficient space, zero memory
increments are precisely the zero matrix. -/
theorem Q_zero_iff (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ)
    (htri : ∀ i j, i.val ≤ j.val → T i j = 0) :
    Q N 0 T ↔ T = 0 := by
  constructor
  · intro hQ
    ext i j
    by_cases hij : i.val ≤ j.val
    · exact htri i j hij
    · have hkN : j.val + 1 < N := by omega
      have hk : j.val + 1 ≤ N := by omega
      have hr : (S_k N (j.val + 1) T).rank = 0 :=
        Nat.eq_zero_of_le_zero (hQ _ (by omega) hkN)
      have hz := matrix_eq_zero_of_rank_zero _ hr
      have he := congrFun (congrFun hz
        (⟨i.val - (j.val + 1), by omega⟩ : Fin (N - (j.val + 1))))
        (⟨j.val, by omega⟩ : Fin (j.val + 1))
      simpa [S_k, hk, Nat.add_sub_of_le (show j.val + 1 ≤ i.val by omega)] using he
  · rintro rfl
    exact zero_mem_Q N 0

#print axioms Q_zero_iff
end MemoryRank.Incremental
