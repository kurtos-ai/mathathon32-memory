module
public import Submission2026.NearQuadratic.PolynomialResponse
public import Continuation.Quadratic.Lower.Schedule

@[expose] public section
noncomputable section
namespace NearQuadratic.PolynomialResponse
open Polynomial
open scoped BigOperators

lemma pPoly_eq_one_add_sum (A : ℕ → ℕ → ℝ) (n : ℕ) :
    pPoly A n = 1 + ∑ j : Fin n, C (A n j.val) * X * pPoly A j.val := by
  cases n with
  | zero => simp [pPoly]
  | succ n => simp only [pPoly]

/-- The history-response polynomial is the canonical increment polynomial. -/
theorem pPoly_W_of {N : ℕ} (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N)
    (n : ℕ) (hn : n ≤ N) :
    pPoly (ResponseBridge.extend (RealizationCore.W_of N d T.val)) n =
      QuadraticFoundations.pIter N d T.val n := by
  let W := RealizationCore.W_of N d T.val
  let A := ResponseBridge.extend W
  have hext (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
      A i j = W ⟨i,by omega⟩ ⟨j,by omega⟩ := by simp [A, ResponseBridge.extend, hi, hj]
  change pPoly A n = _
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => simp only [pPoly, QuadraticFoundations.pIter]
    | succ n =>
      have hlt : n < N := by omega
      have hdiag : A (n+1) n = d ⟨n,hlt⟩ := by
        rw [hext (n+1) n hn (by omega)]
        exact congrFun (RealizationCore.d_of_W_of N d T.val) ⟨n,hlt⟩
      have hinc (j : Fin n) : A (n+1) j.val = A n j.val + T.val ⟨n,hlt⟩ ⟨j.val,by omega⟩ := by
        rw [hext (n+1) j.val hn (by omega), hext n j.val (by omega) (by omega)]
        have h := congrFun (congrFun (RealizationCore.T_of_W_of N d T.val T.property)
          ⟨n,hlt⟩) ⟨j.val,by omega⟩
        simp only [RealizationCore.T_of, Matrix.of_apply, j.isLt, dite_true] at h
        change W ⟨n+1,by omega⟩ ⟨j.val,by omega⟩ - W ⟨n,by omega⟩ ⟨j.val,by omega⟩ = _ at h
        linarith
      have ihj (j : Fin n) : pPoly A j.val = QuadraticFoundations.pIter N d T.val j.val :=
        ih j.val (by omega) (by omega) hext
      have ihn := ih n (by omega) (by omega) hext
      have hprev := pPoly_eq_one_add_sum A n
      rw [ihn] at hprev
      simp_rw [ihj] at hprev
      rw [pPoly_eq_one_add_sum A (n+1), Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hdiag, ihn]
      simp_rw [hinc, ihj, map_add, add_mul]
      rw [Finset.sum_add_distrib]
      rw [QuadraticFoundations.pIter, dite_eq_left hlt]
      dsimp only
      rw [Finset.mul_sum]
      have hsum : (∑ j : Fin n, C (T.val ⟨n,hlt⟩ ⟨j.val,by omega⟩) * X *
          QuadraticFoundations.pIter N d T.val j.val) =
          ∑ j : Fin n, X * (C (T.val ⟨n,hlt⟩ ⟨j.val,by omega⟩) *
          QuadraticFoundations.pIter N d T.val j.val) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hsum]
      rw [show C (1:ℝ) = (1:ℝ[X]) from C_1]
      linear_combination -hprev

/-- The one-register canonical schedule has exactly the proved Chebyshev polynomial. -/
theorem pPoly_schedD (N : ℕ) (L : ℝ) (hL : 0 < L) :
    pPoly (ResponseBridge.extend (RealizationCore.W_of N (QuadraticLower.schedD N L) 0)) N =
      QuadraticFoundations.p_star N L := by
  rw [pPoly_W_of (QuadraticLower.schedD N L)
    (⟨0, by intro i j h; rfl⟩ : RealizationCore.StrictIncrement N) N (le_refl N)]
  exact QuadraticLower.schedD_pN_eq_p_star N L hL

section Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Weighted scalar bounds control the quadratic response energy. -/
theorem quadratic_aeval_le (Q : V →L[ℝ] V) (hSym : Q.toLinearMap.IsSymmetric)
    (L B : ℝ) (hpos : ∀ v, 0 ≤ @inner ℝ V _ (Q v) v)
    (hbound : ∀ v, ‖Q v‖ ≤ L * ‖v‖) (p : ℝ[X])
    (hb : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 ≤ B) (v : V) :
    quadForm Q ((aeval Q p) v) ≤ (B / 2) * ‖v‖ ^ 2 := by
  let b := hSym.eigenvectorBasis rfl
  let lam := hSym.eigenvalues rfl
  have hdiag (w : V) (i) : b.repr (Q w) i = lam i * b.repr w i :=
    hSym.eigenvectorBasis_apply_self_apply rfl w i
  have he (w : V) : @inner ℝ V _ (Q w) w = ∑ i, lam i * (b.repr w i) ^ 2 := by
    rw [← b.sum_inner_mul_inner (Q w) w]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (b i) (Q w), ← b.repr_apply_apply, ← b.repr_apply_apply, hdiag]
    ring
  have henergy : @inner ℝ V _ (Q ((aeval Q p) v)) ((aeval Q p) v) ≤ B * ‖v‖ ^ 2 := by
    rw [he]
    have hv : ‖v‖ ^ 2 = ∑ i, b.repr v i ^ 2 := by
      rw [← b.repr.norm_map v, EuclideanSpace.real_norm_sq_eq]
    rw [hv, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [repr_aeval b Q lam hdiag, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (hb _ (eigenvalues_mem_Icc Q hSym L hpos hbound i)) (sq_nonneg _)
  unfold quadForm
  linarith

variable [CompleteSpace V]

/-- The canonical one-register Chebyshev schedule has the quadratic benchmark
plus the explicit perturbation allowance on every actual finite-dimensional instance. -/
theorem schedule_terminal_le (N : ℕ)
    (Q : V →L[ℝ] V) (f : V → ℝ) (r : V → V) (xStar x0 : V)
    (L0 ε ε0 R : ℝ) (hL : 0 < L0)
    (hData : PerturbedQuadraticData V Q xStar f r L0 ε)
    (hSymm : ∀ u v : V, @inner ℝ V _ (Q u) v = @inner ℝ V _ u (Q v))
    (hε_le : ε ≤ ε0) (hε0 : 0 ≤ ε0) (hR : 0 ≤ R)
    (hR0 : ‖x0-xStar‖ ≤ R) :
    let A := RealizationCore.W_of N (QuadraticLower.schedD N L0) 0
    let πA := pi_of_poly (pPoly (ResponseBridge.extend A) N) L0
    let rho := fun j => pi_of_poly (rPoly (ResponseBridge.extend A) N j) L0
    f (xStar + Trajectory.error A Q r xStar x0 N) - f xStar ≤
      R ^ 2 / 2 * (L0 / (2 * (N:ℝ) + 1) ^ 2) +
      ε * R ^ 2 * kappa_const (hA_of A (L0+ε0) ⟨N, by omega⟩) πA
        (betaCoeff N rho (ResponseBridge.hSeq A (L0+ε0))) L0 ε0 := by
  let A := RealizationCore.W_of N (QuadraticLower.schedD N L0) 0
  have hStrict : IsStrictLowerTri' A := RealizationCore.W_of_strict N _ _
  have hgap := terminal_gap A hStrict Q f r xStar x0 L0 ε ε0 R hData hSymm hε_le hε0 hR hR0
  have hquad := quadratic_aeval_le Q hSymm L0 (L0 / (2 * (N:ℝ) + 1) ^ 2)
    hData.hQ_nonneg hData.hQ_bound (QuadraticFoundations.p_star N L0)
    (QuadraticFoundations.p_star_weight_le N L0 hL) (x0-xStar)
  have hpoly : pOp (ResponseBridge.extend A) Q N =
      aeval Q (QuadraticFoundations.p_star N L0) := by
    rw [pOp_eq_aeval, pPoly_schedD N L0 hL]
  rw [← hpoly] at hquad
  have hsq : ‖x0-xStar‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hR0
  have hm := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ (L0 / (2 * (N:ℝ) + 1) ^ 2) / 2 by positivity)
  have hu := (le_abs_self _).trans hgap
  dsimp only at hu ⊢
  linarith

end Energy
end NearQuadratic.PolynomialResponse
