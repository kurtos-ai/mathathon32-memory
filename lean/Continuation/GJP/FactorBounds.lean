module
public import Continuation.GJP.MassStability
public import Mathlib.Topology.Instances.Matrix

@[expose] public section
noncomputable section
open Matrix Filter Topology
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma offdiag_entry_lower (f : n → ℝ) (i j : n) (hij : j ≠ i) (D : ℝ)
    (hdiag : f i ≤ D) (hsum : 0 ≤ ∑ k, f k) (hsign : ∀ k, k ≠ i → f k ≤ 0) : -D ≤ f j := by
  have hji : j ∈ Finset.univ.erase i := by simp [hij]
  have hrest : (∑ k ∈ (Finset.univ.erase i).erase j, f k) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    exact hsign k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hsplit₁ := Finset.sum_erase_add (s := Finset.univ) (f := f) (Finset.mem_univ i)
  have hsplit₂ := Finset.sum_erase_add (s := Finset.univ.erase i) (f := f) hji
  linarith

variable [LinearOrder n]

lemma TCAdmissible.upper_entry_bounds {last : n} {T C : Matrix n n ℝ}
    (h : TCAdmissible last T C) (D : ℝ) (hD : 0 ≤ D) (hd : ∀ i, T i i ≤ D) (i j : n) :
    -D ≤ T i j ∧ T i j ≤ D := by
  by_cases hij : i = j
  · subst j
    exact ⟨by linarith [h.diagNonneg i], hd i⟩
  · have hsign : ∀ k, k ≠ j → T k j ≤ 0 := by
      intro k hkj
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · exact h.upperNonpos k j hlt
      · rw [h.upper hgt]
    exact ⟨offdiag_entry_lower (fun k => T k j) j i hij D (hd j) (h.colsum_nonneg j) hsign,
      (hsign i hij).trans hD⟩

lemma UnitLower.entry_bounds {C : Matrix n n ℝ} (h : UnitLower C)
    (hs : ∀ i j, j < i → C i j ≤ 0) (hrow : ∀ i, 0 ≤ (C *ᵥ (fun _ => (1:ℝ))) i)
    (i j : n) : -1 ≤ C i j ∧ C i j ≤ 1 := by
  by_cases hij : i = j
  · subst j; rw [h.2 i]; norm_num
  · have hsign : ∀ k, k ≠ i → C i k ≤ 0 := by
      intro k hki
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · exact hs i k hlt
      · rw [h.1 hgt]
    have hsum : 0 ≤ ∑ k, C i k := by simpa [Matrix.mulVec, dotProduct] using hrow i
    exact ⟨offdiag_entry_lower (fun k => C i k) i j (Ne.symm hij) 1 (by rw [h.2 i]) hsum hsign,
      (hsign j (Ne.symm hij)).trans (by norm_num)⟩

variable {N : ℕ}

/-- Once the projection masses exceed one half, all actual factor entries lie in fixed boxes. -/
theorem factors_bounded_of_mass (T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hTC : TCAdmissible (Fin.last N) T C) (b : Fin (N+1) → ℝ)
    (hTb : T *ᵥ b = Pi.single (Fin.last N) 1) (hb : ∀ i, 0 ≤ b i)
    (hbhalf : ∀ i, (1/2:ℝ) ≤ b i)
    (hbC : ∀ i, T i i ≠ 0 → b i ≤ (C *ᵥ (fun _ => 1)) i)
    (hbzero : ∀ i, T i i = 0 → b i = 0) :
    (∀ i j, -2 ≤ T i j ∧ T i j ≤ 2) ∧ (∀ i j, -1 ≤ C i j ∧ C i j ≤ 1) := by
  have hΔ := flowDelta_simplex T b hTC.colsum_nonneg hb hTb
  have hd : ∀ i, T i i ≤ 2 := by
    intro i
    have hprod : T i i*b i ≤ 1 := by
      by_cases hi : i.val < N
      · have hp := flowDelta_prefix_bound T b hTC.upper hTC.upperNonpos hb hTb i hi
        have hs := S_mono N (flowDelta T b) hΔ.1 (a := i.val) (b := N) (by omega)
        rw [S_eq_total N (flowDelta T b) N le_rfl, hΔ.2] at hs
        exact hp.trans hs
      · have hiLast : i = Fin.last N := Fin.ext (by simp; omega)
        subst i
        exact (upper_terminal_row (Fin.last N) (fun j => Fin.le_last j) T hTC.upper b hTb).le
    nlinarith [mul_nonneg (hTC.diagNonneg i) (sub_nonneg.mpr (hbhalf i))]
  refine ⟨hTC.upper_entry_bounds 2 (by norm_num) hd, hTC.unitLower.entry_bounds hTC.lowerNonpos ?_⟩
  intro i
  have hne : T i i ≠ 0 := by
    intro hi
    have hz := hbzero i hi
    have hh := hbhalf i
    linarith
  exact (hb i).trans (hbC i hne)

end GJP
