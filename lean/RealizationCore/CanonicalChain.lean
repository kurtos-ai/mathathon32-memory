module
public import RealizationCore.CoordinateEmbedding
@[expose] public section

/-!
# Canonical realization from the padded cut-matrix rank bounds

The initial-range diagonal embedding is defined separately. All positive cuts use
`coordJ`/`coordL`, so the left inverse remains explicit and computable up to basis
representation rather than being an unproved existence assumption.
-/

namespace RegisterMachine

noncomputable section
open Matrix Finset BigOperators

/-- The one-dimensional diagonal embedding of the cut-zero range into registers. -/
def initJ {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) :
    (cH W 0 (Nat.zero_le N)).mulVecLin.range →ₗ[ℝ] (Fin s → ℝ) where
  toFun z q := if q.val = 0 then z.val 0 else 0
  map_add' x y := by
    funext q
    by_cases h : q.val = 0 <;> simp [h]
  map_smul' a x := by
    funext q
    by_cases h : q.val = 0 <;> simp [h]

/-- Evaluate a register vector at coordinate 0 and lay it on the cut-zero diagonal. -/
def initL {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) {s : ℕ} (hs : 0 < s) :
    (Fin s → ℝ) →ₗ[ℝ] (cH W 0 (Nat.zero_le N)).mulVecLin.range where
  toFun z := ⟨fun _ => z ⟨0, hs⟩, by
    refine ⟨fun _ => z ⟨0, hs⟩, ?_⟩
    funext i
    simp [cH, Matrix.mulVec, dotProduct]⟩
  map_add' x y := by exact Subtype.ext rfl
  map_smul' a x := by exact Subtype.ext rfl

lemma initL_initJ {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) {s : ℕ} (hs : 0 < s)
    (z : (cH W 0 (Nat.zero_le N)).mulVecLin.range) :
    initL W hs (initJ W s z) = z := by
  obtain ⟨z, u, rfl⟩ := z
  apply Subtype.ext
  funext i
  simp [initL, initJ, cH, Matrix.mulVec, dotProduct]

lemma cH_rank_zero {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    (cH W 0 (Nat.zero_le N)).rank = 1 := by
  apply le_antisymm
  · have h := Matrix.rank_le_width (A := cH W 0 (Nat.zero_le N))
    simpa using h
  · let sub : Matrix (Fin 1) (Fin 1) ℝ := (cH W 0 (Nat.zero_le N)).submatrix (fun _ => 0) id
    have hs : sub = 1 := by
      ext i j
      have hi : i = j := by ext; simp
      subst hi
      simp [sub, cH, Matrix.one_apply, Matrix.submatrix_apply]
    calc
      1 = sub.rank := by rw [hs]; simp
      _ ≤ _ := Matrix.rank_submatrix_le _ _ _

/-- Canonical compatible family of future-output subspaces. -/
def canonicalChain {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) {s : ℕ} (hs : 0 < s)
    (hrank : ∀ (k : ℕ) (hk : k ≤ N), (cH W k hk).rank ≤ s) : CompatibleChain N s where
  E k := (cH W k.val (by omega)).mulVecLin.range
  J := Fin.cases (initJ W s) (fun k : Fin N => coordJ s)
  L := Fin.cases (initL W hs) (fun k : Fin N => coordL s (hrank (k.val+1) (by omega)))
  D k := LinearMap.codRestrict _ ((cdrop k).domRestrict
    ((cH W k.val (by omega)).mulVecLin.range)) (fun v => cdrop_range W k v v.2)
  h k := ⟨ch W k, ch_range W k⟩
  obs k := (cobs k).domRestrict ((cH W k.val (by omega)).mulVecLin.range)

lemma canonicalChain_left {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) {s : ℕ}
    (hs : 0 < s) (hrank : ∀ (k : ℕ) (hk : k ≤ N), (cH W k hk).rank ≤ s) :
    ∀ k (z : (canonicalChain W hs hrank).E k),
      (canonicalChain W hs hrank).L k ((canonicalChain W hs hrank).J k z) = z := by
  intro k
  refine Fin.cases ?_ (fun k : Fin N => ?_) k
  · intro z
    exact initL_initJ W hs z
  · intro z
    exact coordL_coordJ s (hrank (k.val+1) (by omega)) z

/-- Canonical future-output state within its range. -/
def canonicalState {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) :
    (cH W k.val (by omega)).mulVecLin.range :=
  ⟨cv W x0 g k, by
    refine ⟨inputVec N x0 g k.val (by omega), ?_⟩
    exact cH_mulVec_eq_cv W x0 g k⟩

lemma canonical_correct {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) {s : ℕ}
    (hs : 0 < s) (hrank : ∀ (k : ℕ) (hk : k ≤ N), (cH W k hk).rank ≤ s)
    (x0 : ℝ) (g : Fin N → ℝ) :
    ChainStateCorrect (canonicalChain W hs hrank) W (canonicalState W) x0 g := by
  refine ⟨?_, ?_, ?_⟩
  · have hcv : cv W x0 g 0 = fun _ => x0 := by
      funext r
      change x0 + ∑ j : Fin 0, W r ⟨j.val, by omega⟩ * g ⟨j.val, by omega⟩ = x0
      simp
    funext i
    change initJ W s (canonicalState W x0 g 0) i = e1 s i * x0
    by_cases hi : i.val = 0 <;> simp [initJ, canonicalState, e1, hi, hcv]
  · intro k
    exact Subtype.ext (cv_succ W x0 g k)
  · intro k
    exact cv_obs W x0 g k

/-- Sufficiency in terms of padded cut-matrix rank bounds. -/
theorem realization_of_cH_rank {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    {s : ℕ} (hs : 0 < s) (hrank : ∀ (k : ℕ) (hk : k ≤ N), (cH W k hk).rank ≤ s) :
    HasRealization N W s := by
  refine ⟨chainMachine (canonicalChain W hs hrank), ?_⟩
  exact chain_realizes (canonicalChain W hs hrank) W (canonicalState W)
    (canonicalChain_left W hs hrank) hs (canonical_correct W hs hrank)

#print axioms initL_initJ
#print axioms canonicalChain_left
#print axioms canonical_correct
#print axioms realization_of_cH_rank
#print axioms cH_rank_zero

end
end RegisterMachine
