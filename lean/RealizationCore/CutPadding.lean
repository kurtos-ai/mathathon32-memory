module
public import RealizationCore.CanonicalChain
@[expose] public section

/-!
# The padded cut matrix has exactly the same rank as the paper's `H_k`

The pad is an injective linear map on the entire future-output space, and maps the
original `H_k` range onto the padded `cH` range. Their matrix ranks are therefore equal.
-/

namespace RegisterMachine

noncomputable section
open Matrix Finset BigOperators

/-- Put a vector with rows `k..N` into the ambient uniform output space. -/
def cPad {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    (Fin (N-k+1) → ℝ) →ₗ[ℝ] (Fin (N+1) → ℝ) where
  toFun v i := if h : k ≤ i.val then v ⟨i.val-k, by omega⟩ else 0
  map_add' x y := by
    funext i
    by_cases h : k ≤ i.val <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : k ≤ i.val <;> simp [h]

lemma cPad_injective {N : ℕ} (k : ℕ) (hk : k ≤ N) : Function.Injective (cPad k hk) := by
  intro x y hxy
  funext i
  have h := congrFun hxy ⟨k+i.val, by omega⟩
  simpa [cPad, Fin.ext_iff] using h

lemma cH_eq_cPad_mulVec {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (k : ℕ) (hk : k ≤ N) (u : Fin (k+1) → ℝ) :
    cH W k hk *ᵥ u = cPad k hk (H_k N k hk W *ᵥ u) := by
  funext i
  by_cases hi : k ≤ i.val
  · simp [cH, cPad, Matrix.mulVec, dotProduct, H_k, hi]
  · simp [cH, cPad, Matrix.mulVec, dotProduct, hi]

lemma cPad_range_Hk {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : ℕ) (hk : k ≤ N) :
    Submodule.map (cPad k hk) (H_k N k hk W).mulVecLin.range = (cH W k hk).mulVecLin.range := by
  rw [← LinearMap.range_comp]
  congr 1
  apply LinearMap.ext
  intro u
  simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply] using (cH_eq_cPad_mulVec W k hk u).symm

/-- The padding map restricted to the original `H_k` range, with the padded range as codomain. -/
noncomputable def cPadRange {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : ℕ) (hk : k ≤ N) :
    (H_k N k hk W).mulVecLin.range →ₗ[ℝ] (cH W k hk).mulVecLin.range :=
  LinearMap.codRestrict _ ((cPad k hk).domRestrict (H_k N k hk W).mulVecLin.range) (by
    intro z
    obtain ⟨u, hu⟩ := z.2
    refine ⟨u, ?_⟩
    rw [Matrix.mulVecLin_apply]
    change cH W k hk *ᵥ u = cPad k hk z
    rw [cH_eq_cPad_mulVec W k hk u]
    congr)

lemma cPadRange_surjective {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (k : ℕ) (hk : k ≤ N) : Function.Surjective (cPadRange W k hk) := by
  intro z
  obtain ⟨u, hu⟩ := z.2
  refine ⟨⟨H_k N k hk W *ᵥ u, ⟨u, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change cPad k hk (H_k N k hk W *ᵥ u) = z
  rw [← cH_eq_cPad_mulVec W k hk u]
  exact hu

lemma cPadRange_injective {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (k : ℕ) (hk : k ≤ N) : Function.Injective (cPadRange W k hk) := by
  intro x y hxy
  apply Subtype.ext
  exact cPad_injective k hk (congrArg Subtype.val hxy)

/-- `rank cH_k = rank H_k`, for every cut including k=0 and k=N. -/
theorem cH_rank_eq_Hk_rank {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (k : ℕ) (hk : k ≤ N) : (cH W k hk).rank = (H_k N k hk W).rank := by
  exact (LinearEquiv.ofBijective (cPadRange W k hk)
    ⟨cPadRange_injective W k hk, cPadRange_surjective W k hk⟩).finrank_eq.symm

#print axioms cPad_injective
#print axioms cH_eq_cPad_mulVec
#print axioms cPad_range_Hk
#print axioms cH_rank_eq_Hk_rank

end
end RegisterMachine
