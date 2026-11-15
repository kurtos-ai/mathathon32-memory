module
/-
A genuine finite Neumann-series fixed point proof for the explicit constants
in Appendix K.  No small-gain or spectral-radius assumption is used.
-/
public import Submission2026.NearQuadratic.ExplicitConstants

@[expose] public section

namespace NearQuadratic

open Finset BigOperators

variable {N : ℕ}

/-- The finite Neumann sum solves the forced lower-triangular recursion.
The proof is the finite telescoping identity, not an appeal to invertibility. -/
lemma neumannSum'_fixedPoint {J : Fin N → Fin N → ℝ}
    (hJ : IsStrictLowerTri' J) (v : Fin N → ℝ) (i : Fin N) :
    neumannSum' J v i = v i + matVecMul' J (neumannSum' J v) i := by
  let w : ℕ → Fin N → ℝ := fun k => JpowVec' k J v
  have hw0 : w 0 i = v i := rfl
  have hwN : w N i = 0 := by
    have h := congrFun (JpowVec'_N_zero hJ v) i
    exact h
  have hshift : (∑ k ∈ Finset.range N, w (k + 1) i) =
      (∑ k ∈ Finset.range N, w k i) - w 0 i + w N i := by
    have hfirst := Finset.sum_range_succ' (fun k => w k i) N
    have hlast := Finset.sum_range_succ (fun k => w k i) N
    linarith
  have hlinear : matVecMul' J (neumannSum' J v) i =
      ∑ k ∈ Finset.range N, w (k + 1) i := by
    unfold matVecMul' neumannSum'
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rfl
  rw [hlinear, hshift]
  have hsum : neumannSum' J v i = ∑ k ∈ Finset.range N, w k i := rfl
  rw [hsum, hw0, hwN]
  ring

/-- The source majorant solves `h = 1 + L |A| h`; its inverse is merely the
finite Neumann sum, with no convergence hypothesis. -/
lemma hA_of_recurrence (A : Fin N → Fin N → ℝ) (L : ℝ)
    (hA : IsStrictLowerTri' A) (i : Fin N) :
    hA_of A L i = 1 + ∑ j : Fin N, L * |A i j| * hA_of A L j := by
  have hscaled : IsStrictLowerTri' (fun i j => L * |A i j|) := by
    intro i j hij
    change L * |A i j| = 0
    rw [hA i j hij]
    simp
  simpa only [hA_of, matVecMul'] using
    neumannSum'_fixedPoint hscaled (fun _ => (1 : ℝ)) i

/-- The source Neumann sum has exactly `N` terms. -/
lemma hA_of_eq_explicit (A : Fin N → Fin N → ℝ) (L : ℝ) (i : Fin N) :
    hA_of A L i =
      ∑ k ∈ Finset.range N,
        JpowVec' k (fun a b => L * |A a b|) (fun _ => (1 : ℝ)) i := rfl

end NearQuadratic

namespace NearQuadratic

/-- Multiplication by a strictly lower-triangular matrix only needs the
strictly earlier entries of the vector. -/
lemma matVecMul'_eq_causal {J : Fin N → Fin N → ℝ}
    (hJ : IsStrictLowerTri' J) (v : Fin N → ℝ) (i : Fin N) :
    matVecMul' J v i = ∑ j : Fin i.val, J i ⟨j.val, by omega⟩ * v ⟨j.val, by omega⟩ := by
  let F : ℕ → ℝ := fun j => if hj : j < N then J i ⟨j, hj⟩ * v ⟨j, hj⟩ else 0
  have hbig : (∑ j : Fin N, J i j * v j) = ∑ j ∈ Finset.range N, F j := by
    rw [← Fin.sum_univ_eq_sum_range F N]
    apply Finset.sum_congr rfl
    intro j _
    simp [F, j.isLt]
  have hsmall : (∑ j : Fin i.val, J i ⟨j.val, by omega⟩ * v ⟨j.val, by omega⟩) =
      ∑ j ∈ Finset.range i.val, F j := by
    rw [← Fin.sum_univ_eq_sum_range F i.val]
    apply Finset.sum_congr rfl
    intro j _
    have hj : j.val < N := by omega
    simp [F, hj]
  unfold matVecMul'
  rw [hbig, hsmall]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt i.isLt))
  intro j hjN hjNot
  have hj : i.val ≤ j := by
    simp only [Finset.mem_range] at hjN hjNot
    omega
  have hjN' : j < N := by simpa only [Finset.mem_range] using hjN
  have hzero : J i ⟨j, hjN'⟩ = 0 := hJ i ⟨j, hjN'⟩ (by omega)
  simp [F, hjN', hzero]

/-- Pointwise source-indexed recurrence for `h_A`. -/
lemma hA_of_eq_causal_recurrence (A : Fin N → Fin N → ℝ) (L : ℝ)
    (hA : IsStrictLowerTri' A) (i : Fin N) :
    hA_of A L i = 1 + ∑ j : Fin i.val,
      L * |A i ⟨j.val, by omega⟩| * hA_of A L ⟨j.val, by omega⟩ := by
  rw [hA_of_recurrence A L hA i]
  have hscaled : IsStrictLowerTri' (fun i j => L * |A i j|) := by
    intro a b hab
    change L * |A a b| = 0
    rw [hA a b hab]
    simp
  change 1 + matVecMul' (fun a b => L * |A a b|) (hA_of A L) i = _
  rw [matVecMul'_eq_causal hscaled (hA_of A L) i]

end NearQuadratic

namespace NearQuadratic

/-- Generic causal form of the finite Neumann fixed point. -/
lemma neumannSum'_eq_causal_recurrence {J : Fin N → Fin N → ℝ}
    (hJ : IsStrictLowerTri' J) (v : Fin N → ℝ) (i : Fin N) :
    neumannSum' J v i = v i + ∑ j : Fin i.val,
      J i ⟨j.val, by omega⟩ * neumannSum' J v ⟨j.val, by omega⟩ := by
  rw [neumannSum'_fixedPoint hJ v i]
  rw [matVecMul'_eq_causal hJ (neumannSum' J v) i]

end NearQuadratic
