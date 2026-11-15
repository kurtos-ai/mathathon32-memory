module
public import Continuation.GJP.FactorEquality

@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {N : ℕ}

/-- The diagonal specified in equation (17). -/
def optimalFactorDiag (N : ℕ) (i : Fin (N+1)) : ℝ :=
  if i.val < N then 2*rOGM N*(SmoothBenchmark.theta N i.val)^2 else 1

/-- The upper bidiagonal factor `T_F^⋆` in equation (17). -/
def optimalFactorT (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  fun i j => if i = j then optimalFactorDiag N i
    else if j.val = i.val+1 then -optimalFactorDiag N i else 0

lemma upper_successor_entry (T : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hT : T.IsUpperTriangular)
    (hfar : ∀ i j, i.val+1 < j.val → T i j = 0)
    (hrow : T *ᵥ (fun _ => (1:ℝ)) = Pi.single (Fin.last N) 1)
    (i j : Fin (N+1)) (hij : j.val = i.val+1) : T i j = -T i i := by
  have hji : j ≠ i := by intro h; have := congrArg Fin.val h; omega
  have hiLast : i ≠ Fin.last N := by intro h; have := congrArg Fin.val h; simp at this; omega
  have htotal : ∑ k, T i k = 0 := by
    have hi := congrFun hrow i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hiLast] using hi
  have hErase : (∑ k ∈ Finset.univ.erase i, T i k) = T i j := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      have hki := (Finset.mem_erase.mp hk).1
      by_cases hlt : k < i
      · exact hT hlt
      · apply hfar
        have hki' : k.val ≠ i.val := fun h => hki (Fin.ext h)
        have hkj' : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        change ¬ k.val < i.val at hlt
        omega
    · intro hnot; exact False.elim (hnot (by simp [hji]))
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hErase] at htotal
  linarith

/-- The equality case of Lemma 3.4 identifies both actual triangular factors. -/
theorem equation15_optimal_factors (W T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hW : UnitLower W) (hTC : TCAdmissible (Fin.last N) T C)
    (hPSD : (equation15Matrix (Fin.last N) W T C (rOGM N)).PosSemidef) :
    T = optimalFactorT N ∧ C = 1 ∧
      (∀ i, (∑ j, T j i)^2/(2*rOGM N) = T i i - (C⁻¹ (Fin.last N) i)^2/2) := by
  obtain ⟨hC, hrow, hcol, hdiag, hlast, htight⟩ := equation15_optimal_equalities W T C hW hTC hPSD
  have hprefix (i : Fin (N+1)) (hi : i.val < N) :
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ∑ k, T k j) = T i i := by
    simp_rw [hcol]
    rw [Finset.sum_filter]
    change S N (deltaStar N) i.val = T i i
    exact (hdiag i hi).symm
  have hfar : ∀ i j : Fin (N+1), i.val+1 < j.val → T i j = 0 := by
    intro i j hij
    let k : Fin (N+1) := ⟨i.val+1, by omega⟩
    have hk : k.val < N := by dsimp [k]; omega
    exact upper_prefix_tight_zero (Fin.last N) T hTC.upper hTC.upperNonpos hrow k
      (by change k.val < N; exact hk) (hprefix k hk) i j (by change i.val < k.val; simp [k])
      (by change k.val < j.val; exact hij)
  have hdiagonal : ∀ i, T i i = optimalFactorDiag N i := by
    intro i
    by_cases hi : i.val < N
    · rw [hdiag i hi, deltaStar_S_eq N i.val hi]
      simp [optimalFactorDiag, hi]
    · have hiLast : i = Fin.last N := Fin.ext (by simp; omega)
      subst i
      simpa [optimalFactorDiag] using hlast
  refine ⟨?_, hC, htight⟩
  funext i j
  unfold optimalFactorT
  by_cases hij : i = j
  · subst j; simpa using hdiagonal i
  · simp only [hij, ↓reduceIte]
    by_cases hnext : j.val = i.val+1
    · rw [if_pos hnext, upper_successor_entry T hTC.upper hfar hrow i j hnext, hdiagonal i]
    · rw [if_neg hnext]
      by_cases hlt : j < i
      · exact hTC.upper hlt
      · apply hfar
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        change ¬(j.val < i.val) at hlt
        omega

lemma optimalFactorDiag_pos (N : ℕ) (i : Fin (N+1)) : 0 < optimalFactorDiag N i := by
  unfold optimalFactorDiag
  split
  · have ht := SmoothBenchmark.theta_pos N i.val (by omega)
    have hr := rOGM_pos N
    positivity
  · norm_num

lemma optimalFactorT_upper (N : ℕ) : (optimalFactorT N).IsUpperTriangular := by
  intro i j hij
  have hne : i ≠ j := ne_of_gt hij
  have hnot : j.val ≠ i.val+1 := by change j.val < i.val at hij; omega
  simp [optimalFactorT, hne, hnot]

lemma optimalFactorT_diag (N : ℕ) (i : Fin (N+1)) :
    optimalFactorT N i i = optimalFactorDiag N i := by simp [optimalFactorT]

lemma optimalFactorT_isUnit (N : ℕ) : IsUnit (optimalFactorT N) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  apply (optimalFactorT_upper N).det_ne_zero_iff.mpr
  intro i
  simpa only [Matrix.diag_apply, optimalFactorT_diag] using ne_of_gt (optimalFactorDiag_pos N i)

/-- Any two actual optimal feasible tuples in (15) have the same method matrix.
This is certificate uniqueness; obtaining certificates or limiting certificates for every
risk-optimal method is a separate strong-duality step. -/
theorem equation15_optimal_method_unique
    (W₁ T₁ C₁ W₂ T₂ C₂ : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hW₁ : UnitLower W₁) (hW₂ : UnitLower W₂)
    (hTC₁ : TCAdmissible (Fin.last N) T₁ C₁) (hTC₂ : TCAdmissible (Fin.last N) T₂ C₂)
    (hPSD₁ : (equation15Matrix (Fin.last N) W₁ T₁ C₁ (rOGM N)).PosSemidef)
    (hPSD₂ : (equation15Matrix (Fin.last N) W₂ T₂ C₂ (rOGM N)).PosSemidef) : W₁ = W₂ := by
  obtain ⟨hT₁, hC₁, htight⟩ := equation15_optimal_factors W₁ T₁ C₁ hW₁ hTC₁ hPSD₁
  obtain ⟨hT₂, hC₂, _⟩ := equation15_optimal_factors W₂ T₂ C₂ hW₂ hTC₂ hPSD₂
  have hTeq : T₂ = T₁ := hT₂.trans hT₁.symm
  have hCeq : C₂ = C₁ := hC₂.trans hC₁.symm
  rw [hTeq, hCeq] at hPSD₂
  apply equation15_tight_unique (Fin.last N) (rOGM N) (rOGM_pos N) hW₁ hW₂
    hTC₁.upper hTC₁.unitLower _ hPSD₁ hPSD₂ htight
  rw [hT₁]
  exact optimalFactorT_isUnit N

end GJP
