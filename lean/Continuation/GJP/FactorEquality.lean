module
public import Continuation.GJP.Projection

@[expose] public section
noncomputable section
open Matrix
namespace GJP

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- A unit lower triangular Z-matrix preserving the ones vector is the identity. -/
lemma UnitLower.eq_one_of_row_sum {C : Matrix n n ℝ} (hC : UnitLower C)
    (hs : ∀ i j, j < i → C i j ≤ 0) (hrow : C *ᵥ (fun _ => (1:ℝ)) = (fun _ => 1)) : C = 1 := by
  funext i j
  by_cases hij : i = j
  · subst j; simpa using hC.2 i
  · have hnonpos : ∀ k ∈ Finset.univ.erase i, C i k ≤ 0 := by
      intro k hk
      rcases lt_or_gt_of_ne (Finset.mem_erase.mp hk).1 with h | h
      · exact hs i k h
      · rw [hC.1 h]
    have hsum : (∑ k ∈ Finset.univ.erase i, C i k) = 0 := by
      have hi := congrFun hrow i
      change (∑ k, C i k * 1) = 1 at hi
      simp only [mul_one] at hi
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hC.2 i] at hi
      linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum j (by simp [Ne.symm hij])
    simpa [Matrix.one_apply, hij] using hzero

/-- Equality in the prefix-flow bound removes every arc crossing strictly over that prefix's end. -/
lemma upper_prefix_tight_zero (last : n) (T : Matrix n n ℝ)
    (hT : T.IsUpperTriangular) (hs : ∀ i j, i < j → T i j ≤ 0)
    (hrow : T *ᵥ (fun _ => (1:ℝ)) = Pi.single last 1)
    (i : n) (hi : i < last)
    (htight : (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ∑ k, T k j) = T i i)
    (k j : n) (hki : k < i) (hij : i < j) : T k j = 0 := by
  let s := Finset.univ.filter (fun j : n => j ≤ i)
  let R : n → ℝ := fun a => ∑ t ∈ s, T a t
  have hRnonneg : ∀ a, 0 ≤ R a := by
    intro a
    by_cases ha : a ≤ i
    · have haLast : a ≠ last := ne_of_lt (lt_of_le_of_lt ha hi)
      have htotal : ∑ t, T a t = 0 := by
        have h := congrFun hrow a
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply, haLast] using h
      have hrest : (∑ t ∈ Finset.univ.filter (fun t => ¬t ≤ i), T a t) ≤ 0 := by
        apply Finset.sum_nonpos
        intro t ht
        exact hs a t (lt_of_le_of_lt ha (lt_of_not_ge (Finset.mem_filter.mp ht).2))
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : n => t ≤ i)
        (fun t => T a t)
      dsimp [R, s]
      linarith
    · apply le_of_eq
      symm
      apply Finset.sum_eq_zero
      intro t ht
      exact hT (lt_of_le_of_lt (Finset.mem_filter.mp ht).2 (lt_of_not_ge ha))
  have hRi : R i = T i i := by
    apply Finset.sum_eq_single i
    · intro t ht hti
      exact hT (lt_of_le_of_ne (Finset.mem_filter.mp ht).2 hti)
    · intro hnot; exact False.elim (hnot (by simp [s]))
  have hsumR : ∑ a, R a = T i i := by
    rw [show (∑ a, R a) = ∑ t ∈ s, ∑ a, T a t from Finset.sum_comm]
    exact htight
  have hsumErase : (∑ a ∈ Finset.univ.erase i, R a) = 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hRi] at hsumR
    linarith
  have hRk : R k = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hRnonneg a)).mp
    hsumErase k (by simp [ne_of_lt hki])
  have hkLast : k ≠ last := ne_of_lt (lt_trans hki hi)
  have htotal : ∑ t, T k t = 0 := by
    have h := congrFun hrow k
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hkLast] using h
  have hrestZero : (∑ t ∈ Finset.univ.filter (fun t => ¬t ≤ i), T k t) = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : n => t ≤ i)
      (fun t => T k t)
    dsimp [R, s] at hRk
    linarith
  apply (Finset.sum_eq_zero_iff_of_nonpos (fun t ht =>
    hs k t (lt_trans hki (lt_of_not_ge (Finset.mem_filter.mp ht).2)))).mp hrestZero j
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, not_le.mpr hij⟩

variable {N : ℕ}

lemma deltaStar_pos (N : ℕ) (i : Fin (N+1)) : 0 < deltaStar N i := by
  unfold deltaStar
  split
  · exact mul_pos (mul_pos (by norm_num) (rOGM_pos N))
      (SmoothBenchmark.theta_pos N i.val (by omega))
  · exact Real.sqrt_pos.mpr (rOGM_pos N)

/-- At the optimal rate the exact projection forces `b = 1`, `C = I`, all pivot
values and every Schur diagonal inequality to be tight. -/
theorem equation15_optimal_equalities (W T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hW : UnitLower W) (hTC : TCAdmissible (Fin.last N) T C)
    (hPSD : (equation15Matrix (Fin.last N) W T C (rOGM N)).PosSemidef) :
    C = 1 ∧ T *ᵥ (fun _ => (1:ℝ)) = Pi.single (Fin.last N) 1 ∧
      (∀ i, (∑ j, T j i) = deltaStar N i) ∧
      (∀ i, i.val < N → T i i = S N (deltaStar N) i.val) ∧
      T (Fin.last N) (Fin.last N) = 1 ∧
      (∀ i, (∑ j, T j i)^2/(2*rOGM N) = T i i - (C⁻¹ (Fin.last N) i)^2/2) := by
  have hr := rOGM_pos N
  obtain ⟨b, hTb, hb, hb1, hbC, hbzero, hΔ, hPhi⟩ :=
    equation15_projects_simplex W T C (rOGM N) hr hW hTC hPSD
  have hPhiEq : Phi N (flowDelta T b) = rOGM N :=
    le_antisymm hPhi (rOGM_leq_Phi N _ hΔ)
  have hdelta : flowDelta T b = deltaStar N := funext (uniqueness N _ hΔ hPhiEq)
  have hdiag := equation15_diagonal_necessary (Fin.last N) (rOGM N) hr hW hTC.upper hTC.unitLower hPSD
  have hnonterminal (i : Fin (N+1)) (hi : i.val < N) :
      b i = 1 ∧ T i i = S N (flowDelta T b) i.val ∧ C⁻¹ (Fin.last N) i = 0 ∧
        (∑ j, T j i)^2/(2*rOGM N) = T i i := by
    apply projected_fraction_equality (rOGM N) (T i i) (∑ j, T j i)
      (C⁻¹ (Fin.last N) i) (b i) (S N (flowDelta T b) i.val) hr (hTC.diagNonneg i)
      (hb i) (hb1 i) (S_nonneg N _ hΔ.1 _)
      (flowDelta_prefix_bound T b hTC.upper hTC.upperNonpos hb hTb i hi) (hdiag i)
    have heq : phiTerm N (flowDelta T b) i = rOGM N := by
      rw [hdelta]; exact phiTerm_tied N i
    simpa [phiTerm, partialSum, hi, flowDelta] using heq
  have hterminal : b (Fin.last N) = 1 ∧ T (Fin.last N) (Fin.last N) = 1 ∧
      (∑ j, T j (Fin.last N))^2/(2*rOGM N) = T (Fin.last N) (Fin.last N)-1/2 := by
    apply projected_terminal_equality (rOGM N) (T (Fin.last N) (Fin.last N))
      (∑ j, T j (Fin.last N)) (b (Fin.last N)) hr (hb _)
      (upper_terminal_row (Fin.last N) (fun j => Fin.le_last j) T hTC.upper b hTb)
    · simpa only [hTC.unitLower.inv.2 (Fin.last N), one_pow] using hdiag (Fin.last N)
    · have heq : phiTerm N (flowDelta T b) (Fin.last N) = rOGM N := by
        rw [hdelta]; exact phiTerm_tied N (Fin.last N)
      simpa [phiTerm, flowDelta] using heq
  have hbOne : b = (fun _ => 1) := by
    funext i
    by_cases hi : i.val < N
    · exact (hnonterminal i hi).1
    · have hiLast : i = Fin.last N := Fin.ext (by simp; omega)
      simpa [hiLast] using hterminal.1
  have hpivot : ∀ i, T i i ≠ 0 := by
    intro i hi
    have := hbzero i hi
    rw [hbOne] at this
    norm_num at this
  have hCrows : C *ᵥ (fun _ => (1:ℝ)) = (fun _ => 1) := by
    funext i
    apply le_antisymm (hTC.unitLower.row_sum_le_one hTC.lowerNonpos i)
    simpa [hbOne] using hbC i (hpivot i)
  refine ⟨hTC.unitLower.eq_one_of_row_sum hTC.lowerNonpos hCrows,
    by simpa [hbOne] using hTb, ?_, ?_, hterminal.2.1, ?_⟩
  · intro i
    have hi := congrFun hdelta i
    simpa [flowDelta, hbOne] using hi
  · intro i hi
    simpa [hdelta] using (hnonterminal i hi).2.1
  · intro i
    by_cases hi : i.val < N
    · rw [(hnonterminal i hi).2.2.1]
      simpa using (hnonterminal i hi).2.2.2
    · have hiLast : i = Fin.last N := Fin.ext (by simp; omega)
      subst i
      simpa only [hTC.unitLower.inv.2 (Fin.last N), one_pow] using hterminal.2.2

end GJP
