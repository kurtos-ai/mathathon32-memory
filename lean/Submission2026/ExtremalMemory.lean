module

public import RealizationCore.Coordinates
public import RealizationCore.VectorRealization

@[expose] public section
noncomputable section

/-!
# Exact memory of the four-query extremal path family

The coefficient map is defined explicitly and proved to satisfy the path
recurrence from Appendix I.  The assumptions below concern its positive path
parameters, diagonal slack, and adjacent stationarity.  They do not assume a
determinant or rank conclusion.  This file does not prove that those parameters
are optimal, or that they attain any stated rate.
-/

namespace ExtremalMemory

open Matrix
open scoped BigOperators

/-- Cumulative positive path weights. -/
def D (δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => δ 0
  | i + 1 => D δ i + δ (i + 1)

/-- The telescoped form of the paper's unit-diagonal recurrence, with
`P i j = ν i * ν j`. -/
def omegaEntry (δ ν : ℕ → ℝ) (r : ℝ) (i j : ℕ) : ℝ :=
  if j < i then
    (D δ j + δ j / r * (D δ i - D δ j) +
      2 * ν j * ∑ l ∈ Finset.Ico (j + 1) (i + 1), ν l) / D δ i
  else if j = i then 1 else 0

@[simp] theorem omegaEntry_diagonal (δ ν : ℕ → ℝ) (r : ℝ) (i : ℕ) :
    omegaEntry δ ν r i i = 1 := by simp [omegaEntry]

/-- The defined entries satisfy the actual coefficient recurrence. -/
theorem omegaEntry_recurrence (δ ν : ℕ → ℝ) (r : ℝ) (k j : ℕ)
    (hjk : j ≤ k) (hDk : D δ k ≠ 0) (hDk1 : D δ (k + 1) ≠ 0) :
    D δ (k + 1) * omegaEntry δ ν r (k + 1) j =
      D δ k * omegaEntry δ ν r k j + δ (k + 1) * δ j / r +
        2 * ν (k + 1) * ν j := by
  by_cases h : j = k
  · subst j
    simp only [omegaEntry, Nat.lt_succ_self, ite_true, lt_self_iff_false,
      Finset.sum_Ico_succ_top (by omega : k + 1 ≤ k + 1),
      Finset.Ico_self, Finset.sum_empty, zero_add, ite_false]
    rw [mul_div_cancel₀ _ hDk1]
    simp only [D]
    ring
  · have hjk' : j < k := by omega
    simp only [omegaEntry, hjk', show j < k + 1 by omega, ite_true]
    rw [mul_div_cancel₀ _ hDk1, mul_div_cancel₀ _ hDk,
      Finset.sum_Ico_succ_top (by omega : j + 1 ≤ k + 1)]
    simp only [D]
    ring

theorem D_pos (δ : ℕ → ℝ) (n : ℕ) (hδ : ∀ i ≤ n, 0 < δ i) :
    ∀ i ≤ n, 0 < D δ i := by
  intro i hi
  induction i with
  | zero => exact hδ 0 (by omega)
  | succ i ih => exact add_pos (ih (by omega)) (hδ (i + 1) hi)

/-- Parameters supplied by the separate path-stationarity argument. -/
structure PathConditions4 (δ ν : ℕ → ℝ) (r : ℝ) : Prop where
  rate_pos : 0 < r
  weight_pos : ∀ i ≤ 4, 0 < δ i
  slack_pos : ∀ i ≤ 4, 0 < ν i
  normalized : D δ 4 = 1
  diagonal : ∀ i ≤ 4,
    ν i ^ 2 = D δ i - δ i ^ 2 / (2 * r) - if i = 4 then 1 / 2 else 0
  adjacent : ∀ i < 4, δ i * ν (i + 1) - δ (i + 1) * ν i = r * ν (i + 1)

/-- The signed strict history used by the register-machine definitions. -/
def coefficients (N : ℕ) (δ ν : ℕ → ℝ) (r : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j =>
  if j.val < i.val then -omegaEntry δ ν r i.val j.val else 0

theorem coefficients_strict (N : ℕ) (δ ν : ℕ → ℝ) (r : ℝ)
    (i j : Fin (N + 1)) (hij : i.val ≤ j.val) :
    coefficients N δ ν r i j = 0 := by
  simp [coefficients, show ¬ j.val < i.val by omega]

def history (N : ℕ) (δ ν : ℕ → ℝ) (r : ℝ) : RealizationCore.StrictHistory N :=
  ⟨coefficients N δ ν r, coefficients_strict N δ ν r⟩

/-- The determinant displayed in the paper, before imposing stationarity. -/
def determinant4 (δ ν : ℕ → ℝ) (r : ℝ) : ℝ :=
  (omegaEntry δ ν r 3 0 - omegaEntry δ ν r 2 0) *
    (omegaEntry δ ν r 4 1 - omegaEntry δ ν r 2 1) -
  (omegaEntry δ ν r 3 1 - omegaEntry δ ν r 2 1) *
    (omegaEntry δ ν r 4 0 - omegaEntry δ ν r 2 0)

/-- The two-dimensional wedge that appears after eliminating the first column. -/
def wedge2 (δ ν : ℕ → ℝ) (r : ℝ) : ℝ :=
  (omegaEntry δ ν r 2 0 - δ 0 / r) * ν 1 -
    (omegaEntry δ ν r 2 1 - δ 1 / r) * ν 0

theorem wedge2_cancellation (δ ν : ℕ → ℝ) (r : ℝ)
    (hr : r ≠ 0) (hD : D δ 2 ≠ 0)
    (hdiag : ν 1 ^ 2 = D δ 1 - δ 1 ^ 2 / (2 * r))
    (hadj : δ 0 * ν 1 - δ 1 * ν 0 = r * ν 1) :
    wedge2 δ ν r = D δ 1 * ν 0 / D δ 2 := by
  have hslack : 2 * r * ν 1 ^ 2 = 2 * r * D δ 1 - δ 1 ^ 2 := by
    rw [hdiag]
    field_simp
  unfold wedge2
  norm_num [omegaEntry, Finset.sum_Ico_succ_top]
  field_simp
  simp only [D] at hslack ⊢
  linear_combination ν 0 * hslack - δ 0 * hadj

theorem determinant4_factorization (δ ν : ℕ → ℝ) (r : ℝ)
    (hD2 : D δ 2 ≠ 0) (hD3 : D δ 3 ≠ 0) (hD4 : D δ 4 ≠ 0) :
    determinant4 δ ν r =
      -2 * (δ 3 * ν 4 - δ 4 * ν 3) * wedge2 δ ν r / (D δ 3 * D δ 4) := by
  unfold determinant4 wedge2
  norm_num [omegaEntry, Finset.sum_Ico_succ_top]
  field_simp
  simp only [D]
  ring

theorem determinant4_eq (δ ν : ℕ → ℝ) (r : ℝ) (h : PathConditions4 δ ν r) :
    determinant4 δ ν r = -2 * r * D δ 1 * ν 0 * ν 4 / (D δ 2 * D δ 3) := by
  have hD := D_pos δ 4 h.weight_pos
  rw [determinant4_factorization δ ν r (ne_of_gt (hD 2 (by omega)))
    (ne_of_gt (hD 3 (by omega))) (ne_of_gt (hD 4 (by omega))),
    wedge2_cancellation δ ν r (ne_of_gt h.rate_pos) (ne_of_gt (hD 2 (by omega)))
      (by simpa using h.diagonal 1 (by omega)) (h.adjacent 0 (by omega)),
    h.adjacent 3 (by omega), h.normalized]
  ring

theorem determinant4_neg (δ ν : ℕ → ℝ) (r : ℝ) (h : PathConditions4 δ ν r) :
    determinant4 δ ν r < 0 := by
  rw [determinant4_eq δ ν r h]
  have hD := D_pos δ 4 h.weight_pos
  have hnum : 0 < 2 * r * D δ 1 * ν 0 * ν 4 := by
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) h.rate_pos)
      (hD 1 (by omega))) (h.slack_pos 0 (by omega))) (h.slack_pos 4 (by omega))
  have hden : 0 < D δ 2 * D δ 3 := mul_pos (hD 2 (by omega)) (hD 3 (by omega))
  calc
    _ = -(2 * r * D δ 1 * ν 0 * ν 4 / (D δ 2 * D δ 3)) := by ring
    _ < 0 := neg_neg_of_pos (div_pos hnum hden)

theorem cut2_det (δ ν : ℕ → ℝ) (r : ℝ) :
    (MemoryRank.CutRank.H_k 4 2 (by omega) (coefficients 4 δ ν r)).det =
      determinant4 δ ν r := by
  simp [MemoryRank.CutRank.H_k, coefficients, Matrix.det_fin_three, determinant4]
  ring

theorem cut2_rank (δ ν : ℕ → ℝ) (r : ℝ) (h : PathConditions4 δ ν r) :
    (MemoryRank.CutRank.H_k 4 2 (by omega) (coefficients 4 δ ν r)).rank = 3 := by
  have hd : (MemoryRank.CutRank.H_k 4 2 (by omega) (coefficients 4 δ ν r)).det ≠ 0 := by
    rw [cut2_det]
    exact ne_of_lt (determinant4_neg δ ν r h)
  simpa using Matrix.rank_of_det_ne_zero hd

theorem memory_rank_eq_three (δ ν : ℕ → ℝ) (r : ℝ) (h : PathConditions4 δ ν r) :
    MemoryRank.CutRank.memRank 4 (coefficients 4 δ ν r) = 3 := by
  have hu := MemoryRank.CutRank.memRank_le 4 (coefficients 4 δ ν r)
  have hl := Finset.le_sup (f := fun k : Fin 5 =>
      (MemoryRank.CutRank.H_k 4 k.val (by omega) (coefficients 4 δ ν r)).rank)
    (Finset.mem_univ (2 : Fin 5))
  change (MemoryRank.CutRank.H_k 4 2 (by omega) (coefficients 4 δ ν r)).rank ≤
    MemoryRank.CutRank.memRank 4 (coefficients 4 δ ν r) at hl
  rw [cut2_rank δ ν r h] at hl
  omega

theorem has_three_register_realization (δ ν : ℕ → ℝ) (r : ℝ)
    (h : PathConditions4 δ ν r) :
    RegisterMachine.HasRealization 4 (coefficients 4 δ ν r) 3 := by
  apply (RegisterMachine.realization_iff_maxCutRank 4 _ 3).mpr
  rw [memory_rank_eq_three δ ν r h]

theorem no_two_register_realization (δ ν : ℕ → ℝ) (r : ℝ)
    (h : PathConditions4 δ ν r) :
    ¬ RegisterMachine.HasRealization 4 (coefficients 4 δ ν r) 2 := by
  rw [RegisterMachine.realization_iff_maxCutRank, memory_rank_eq_three δ ν r h]
  omega

theorem vector_memory_exact (δ ν : ℕ → ℝ) (r : ℝ) (h : PathConditions4 δ ν r) :
    IsLeast {s : ℕ | RegisterMachine.HasVectorRealization 4 (coefficients 4 δ ν r) s} 3 := by
  have hm := RegisterMachine.isLeast_vectorRegisterCount 4 (coefficients 4 δ ν r)
  rwa [memory_rank_eq_three δ ν r h] at hm

#print axioms omegaEntry_recurrence
#print axioms determinant4_eq
#print axioms determinant4_neg
#print axioms memory_rank_eq_three
#print axioms vector_memory_exact

end ExtremalMemory
