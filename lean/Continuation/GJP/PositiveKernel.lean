module
public import Continuation.GJP.Elimination
@[expose] public section
noncomputable section
open Matrix
namespace GJPDual


lemma psd_column_zero {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℝ} (hG : G.PosSemidef) (i : n) (hi : G i i = 0) :
    ∀ j, G j i = 0 := by
  have hq : star (Pi.single i (1 : ℝ)) ⬝ᵥ G *ᵥ Pi.single i 1 = 0 := by
    simpa using hi
  have hz := hG.dotProduct_mulVec_zero_iff.mp hq
  intro j
  simpa using congrFun hz j

/-- A triangular history cannot support a nonzero positive Gram matrix with zero
initial radius and nonnegative diagonal interpolation slacks. -/
theorem triangular_positive_kernel {N : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hW : GJP.UnitLower W)
    (G : Matrix (Unit ⊕ Fin (N+1)) (Unit ⊕ Fin (N+1)) ℝ)
    (hG : G.PosSemidef) (hzero : G (Sum.inl ()) (Sum.inl ()) = 0)
    (hdiag : ∀ i, 0 ≤ G (Sum.inl ()) (Sum.inr i) -
      ∑ j, W i j * G (Sum.inr j) (Sum.inr i)) : G = 0 := by
  have hcol0 := psd_column_zero hG (Sum.inl ()) hzero
  have hrow0 (i : Fin (N+1)) : G (Sum.inl ()) (Sum.inr i) = 0 := by
    have hs := hG.isHermitian.apply (Sum.inl ()) (Sum.inr i)
    simpa [hcol0] using hs.symm
  have hd (i : Fin (N+1)) : G (Sum.inr i) (Sum.inr i) = 0 := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hsum : (∑ j, W i j * G (Sum.inr j) (Sum.inr i)) =
          G (Sum.inr i) (Sum.inr i) := by
        rw [Finset.sum_eq_single i]
        · rw [hW.2]; ring
        · intro j _ hji
          rcases lt_or_gt_of_ne hji with hj | hj
          · have hz := psd_column_zero hG (Sum.inr j) (ih j hj)
            have hs := hG.isHermitian.apply (Sum.inr j) (Sum.inr i)
            have he : G (Sum.inr j) (Sum.inr i) = 0 := by simpa [hz] using hs.symm
            rw [he,mul_zero]
          · rw [hW.1 hj,zero_mul]
        · simp
      have hi := hdiag i
      rw [hrow0,hsum] at hi
      have hp := hG.diag_nonneg (i := Sum.inr i)
      linarith
  apply GJP.posSemidef_eq_zero_of_diagonal hG
  rintro (⟨⟩ | i)
  · exact hzero
  · exact hd i

end GJPDual
