module
public import RealizationCore.MemoryCharacterization
@[expose] public section
noncomputable section
namespace RealizationCore

/-- The coefficient space: entries on or above the diagonal vanish. -/
def StrictHistory (N : ℕ) :=
  {W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ // ∀ i j, i.val ≤ j.val → W i j = 0}

def StrictIncrement (N : ℕ) :=
  {T : Matrix (Fin N) (Fin N) ℝ // ∀ i j, i.val ≤ j.val → T i j = 0}

/-- First subdiagonal coefficients, not diagonal entries. -/
def d_of (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (j : Fin N) : ℝ :=
  W j.succ j.castSucc

/-- Zero extension used only to write the finite telescoping sum with natural indices. -/
def extendedIncrement {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (i j : ℕ) : ℝ :=
  if h : i < N ∧ j < N then T ⟨i,h.1⟩ ⟨j,h.2⟩ else 0

/-- Inverse coefficient formula from the paper; the interval excludes both endpoints. -/
def W_of (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i j =>
  if h : j.val < i.val then
    d ⟨j.val,by omega⟩ + ∑ l ∈ Finset.Ico (j.val+1) i.val, extendedIncrement T l j.val
  else 0

theorem W_of_strict (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin (N+1)) (h : i.val ≤ j.val) : W_of N d T i j = 0 := by
  simp [W_of, show ¬ j.val < i.val by omega]

theorem d_of_W_of (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) :
    d_of N (W_of N d T) = d := by
  funext j
  simp [d_of, W_of]

theorem T_of_W_of (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ)
    (hT : ∀ i j, i.val ≤ j.val → T i j = 0) : T_of N (W_of N d T) = T := by
  ext i j
  by_cases h : j.val < i.val
  · simp only [T_of, Matrix.of_apply, h, dite_true]
    simp only [W_of, h, show j.val < i.val + 1 by omega, dite_true]
    rw [Finset.sum_Ico_succ_top (show j.val+1 ≤ i.val by omega)]
    simp [extendedIncrement, i.isLt, j.isLt]
  · simp only [T_of, Matrix.of_apply, dite_eq_right h]
    exact (hT i j (by omega)).symm

private theorem W_of_recover_entry (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hW : ∀ i j, i.val ≤ j.val → W i j = 0) :
    ∀ (i : ℕ) (hi : i < N+1) (j : Fin (N+1)),
      W_of N (d_of N W) (T_of N W) ⟨i,hi⟩ j = W ⟨i,hi⟩ j := by
  intro i
  induction i with
  | zero =>
    intro hi j
    have hz : (⟨0, hi⟩ : Fin (N+1)).val ≤ j.val := Nat.zero_le _
    rw [W_of_strict N _ _ _ _ hz, hW _ _ hz]
  | succ i ih =>
    intro hi j
    by_cases hj : j.val < i+1
    · by_cases hji : j.val < i
      · have hi' : i < N+1 := by omega
        have prev := ih hi' j
        simp only [W_of, hji, dite_true] at prev
        simp only [W_of, hj, dite_true]
        rw [Finset.sum_Ico_succ_top (show j.val+1 ≤ i by omega)]
        have hiN : i < N := by omega
        have hjN : j.val < N := by omega
        have hinc : extendedIncrement (T_of N W) i j.val =
            W ⟨i+1,hi⟩ j - W ⟨i,hi'⟩ j := by
          change (if h : i < N ∧ j.val < N then
            T_of N W ⟨i,h.1⟩ ⟨j.val,h.2⟩ else 0) = _
          rw [dite_eq_left ⟨hiN,hjN⟩]
          simp only [T_of, Matrix.of_apply, hji, dite_true]
        rw [hinc, ← add_assoc, prev]
        ring
      · have he : j.val = i := by omega
        simp only [W_of, dite_true, he, Nat.lt_succ_self,
          Finset.Ico_self, Finset.sum_empty, add_zero, d_of]
        congr 1
        apply Fin.ext
        exact he.symm
    · have hz : (⟨i+1,hi⟩ : Fin (N+1)).val ≤ j.val := by
        change i+1 ≤ j.val
        omega
      rw [W_of_strict N _ _ _ _ hz, hW _ _ hz]

theorem W_of_dT_of (N : ℕ) (W : StrictHistory N) :
    W_of N (d_of N W.val) (T_of N W.val) = W.val := by
  ext i j
  exact W_of_recover_entry N W.val W.property i.val i.isLt j

/-- The paper's coefficient change is a genuine bijection, with both inverse laws. -/
def coordinateEquiv (N : ℕ) : StrictHistory N ≃ (Fin N → ℝ) × StrictIncrement N where
  toFun W := (d_of N W.val, ⟨T_of N W.val, by
    intro i j hij
    simp only [T_of, Matrix.of_apply, dite_eq_right (show ¬ j.val < i.val by omega)]⟩)
  invFun p := ⟨W_of N p.1 p.2.val, W_of_strict N p.1 p.2.val⟩
  left_inv W := Subtype.ext (W_of_dT_of N W)
  right_inv p := by
    apply Prod.ext
    · exact d_of_W_of N p.1 p.2.val
    · exact Subtype.ext (T_of_W_of N p.1 p.2.val p.2.property)

/-- In coefficient coordinates, the operational memory constraint depends only on T. -/
theorem realization_iff_coordinates (N m : ℕ) (d : Fin N → ℝ)
    (T : StrictIncrement N) :
    RegisterMachine.HasRealization N (W_of N d T.val) (m+1) ↔
      MemoryRank.Incremental.Q N m T.val := by
  rw [RegisterMachine.realization_iff_incrementLocus,
    T_of_W_of N d T.val T.property]

end RealizationCore
