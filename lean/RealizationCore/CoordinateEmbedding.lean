module
public import RealizationCore.CanonicalCore
@[expose] public section

/-!
# Explicit coordinates for a finite-dimensional real vector space

Choose a finite basis and pad its coordinates into ℝ^s. The unpadding map is a
left inverse, not merely a map asserted to exist by Classical.choice.
-/

namespace RegisterMachine

noncomputable section
open Matrix Finset BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]

/-- Pad the coordinates of any finite-dimensional real vector space into ℝ^s. -/
def coordJ (s : ℕ) : E →ₗ[ℝ] (Fin s → ℝ) where
  toFun z i := if hi : i.val < Module.finrank ℝ E then
    (Module.finBasis ℝ E).equivFun z ⟨i.val, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : i.val < Module.finrank ℝ E <;> simp [hi]
  map_smul' a x := by
    funext i
    by_cases hi : i.val < Module.finrank ℝ E <;> simp [hi]

/-- Reconstruct an element from padded coordinates. -/
def coordL (s : ℕ) (hs : Module.finrank ℝ E ≤ s) : (Fin s → ℝ) →ₗ[ℝ] E where
  toFun z := (Module.finBasis ℝ E).equivFun.symm (fun i => z ⟨i.val, by omega⟩)
  map_add' x y := by simp [Module.Basis.equivFun_symm_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Module.Basis.equivFun_symm_apply, smul_sum, mul_smul]

/-- The explicit left-inverse equation. -/
lemma coordL_coordJ (s : ℕ) (hs : Module.finrank ℝ E ≤ s) (z : E) :
    coordL s hs (coordJ s z) = z := by
  apply (Module.finBasis ℝ E).equivFun.injective
  funext i
  simp [coordJ, coordL, i.isLt]

end
end RegisterMachine
