module
public import Continuation.Smooth.DroriDualFormula
public import Continuation.Smooth.DroriGeometry
public import Continuation.Smooth.DroriTail
@[expose] public section
noncomputable section
open scoped InnerProductSpace

namespace DroriTail

def quad {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) : ℝ :=
  ∑ j, (z j.val-z (j.val+1))*(t j)^2

def prefixQuad {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) : ℝ :=
  ∑ j, if j.val < k then (z j.val-z (j.val+1))*(t j)^2 else 0

def tailQuad {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) : ℝ :=
  ∑ j, if k < j.val then (z j.val-z (j.val+1))*(t j)^2 else 0

lemma quad_split {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) (hk : k ≤ N) :
    quad z t = prefixQuad z t k+(z k-z (k+1))*(t ⟨k,by omega⟩)^2+tailQuad z t k := by
  classical
  have hs : (∑ j : Fin (N+1), if j.val = k then (z j.val-z (j.val+1))*(t j)^2 else 0) =
      (z k-z (k+1))*(t ⟨k,by omega⟩)^2 := by
    rw [Finset.sum_eq_single (⟨k,by omega⟩ : Fin (N+1))]
    · simp
    · intro b _ hb
      have hbk : b.val ≠ k := by intro he; apply hb; exact Fin.ext he
      simp [hbk]
    · simp
  rw [← hs]
  simp only [quad,prefixQuad,tailQuad,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hlt : j.val < k
  · simp [hlt,show j.val ≠ k by omega,show ¬ k < j.val by omega]
  · by_cases he : j.val = k
    · simp [he]
    · simp [hlt,he,show k < j.val by omega]

lemma quad_candidate {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) (hk : k ≤ N) (a : ℝ) :
    quad z (candidate t k a) = prefixQuad z t k+(z k-z (k+1))*a^2 := by
  rw [quad_split z (candidate t k a) k hk]
  have hp : prefixQuad z (candidate t k a) k = prefixQuad z t k := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · simp [candidate,hj]
    · rfl
  have ht : tailQuad z (candidate t k a) k = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : k < j.val
    · simp [hj,candidate,show ¬j.val<k by omega,show j.val≠k by omega]
    · simp [hj]
  rw [hp,ht]
  simp [candidate]

lemma tailQuad_nonneg {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ)
    (hz : ∀ j ≤ N, z (j+1) ≤ z j) (k : ℕ) : 0 ≤ tailQuad z t k := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (sub_nonneg.mpr (hz j.val (by omega))) (sq_nonneg _)
  · exact le_rfl

lemma quad_candidate_zero_le {N : ℕ} (z : ℕ → ℝ) (t : Fin (N+1) → ℝ)
    (hz : ∀ j ≤ N, z (j+1) ≤ z j) (k : ℕ) (hk : k ≤ N) :
    quad z (candidate t k 0) ≤ quad z t := by
  rw [quad_candidate z t k hk 0,quad_split z t k hk]
  have hd := mul_nonneg (sub_nonneg.mpr (hz k hk)) (sq_nonneg (t ⟨k,by omega⟩))
  have ht := tailQuad_nonneg z t hz k
  nlinarith

end DroriTail

namespace SmoothDrori

lemma inner_unscale_candidate (N : ℕ) (L R : ℝ) (p : Space N) (k : ℕ)
    (hp : p ∈ prefixSpace N k) (t : Fin (N+1) → ℝ) (a : ℝ) :
    ⟪p,hardUnscale N L R (DroriTail.candidate t k a)⟫_ℝ = ⟪p,hardUnscale N L R t⟫_ℝ := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · simp only [hardUnscale_apply,DroriTail.candidate,hj,ite_true]
  · simp [RCLike.inner_apply,hp j (by omega)]

lemma hardDual_unscale_ge (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (i : ℕ) (hi : i ≤ N+1) (t : Fin (N+1) → ℝ) :
    L/2*DroriTail.quad (zetaStar N R) t - L*DroriTail.B N (zetaStar N R) t i ≤
      hardDual N L R (hardUnscale N L R t) := by
  have h := SmoothDual.H_ge_Hi
    (x:=fun a : Fin (N+2) => hardX N R a.val)
    (g:=fun a : Fin (N+2) => hardG N L R a.val)
    (f:=fun a : Fin (N+2) => hardF N L R a.val)
    (L:=L) (hardUnscale N L R t) ⟨i,by omega⟩
  rw [hardHi_unscale N L R hN hL hR] at h
  exact h

lemma hardDual_unscale_eq_piece (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (t : Fin (N+1) → ℝ) : ∃ i ≤ N+1,
      hardDual N L R (hardUnscale N L R t) =
        L/2*DroriTail.quad (zetaStar N R) t - L*DroriTail.B N (zetaStar N R) t i := by
  obtain ⟨i,hi⟩ := SmoothDual.H_exists_eq
    (x:=fun a : Fin (N+2) => hardX N R a.val)
    (g:=fun a : Fin (N+2) => hardG N L R a.val)
    (f:=fun a : Fin (N+2) => hardF N L R a.val) (L:=L) (hardUnscale N L R t)
  refine ⟨i.val,by omega,?_⟩
  rw [hardHi_unscale N L R hN hL hR] at hi
  exact hi

lemma hardUnscale_candidate_mem_prefix (N : ℕ) (L R : ℝ) (t : Fin (N+1) → ℝ) (k : ℕ) (a : ℝ) :
    hardUnscale N L R (DroriTail.candidate t k a) ∈ prefixSpace N (k+1) := by
  intro j hj
  simp [hardUnscale_apply,DroriTail.candidate,show ¬j.val<k by omega,show j.val≠k by omega]

/-- A tail candidate with no greater dual cost must equal the actual conjugate
    maximizer, because its linear pairing with a prefix-supported query is unchanged. -/
lemma hardGradient_eq_tail_candidate (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (p : Space N) (k : ℕ) (hp : p ∈ prefixSpace N k) (a : ℝ) (ha : 0 ≤ a)
    (hcost : hardDual N L R (hardUnscale N L R (DroriTail.candidate
      (hardScale N L R (hardGradient N L R hN hL hR p)) k a)) ≤
      hardDual N L R (hardGradient N L R hN hL hR p)) :
    hardGradient N L R hN hL hR p = hardUnscale N L R (DroriTail.candidate
      (hardScale N L R (hardGradient N L R hN hL hR p)) k a) := by
  let q := hardGradient N L R hN hL hR p
  let t := hardScale N L R q
  let r := hardUnscale N L R (DroriTail.candidate t k a)
  have hs := hardGradient_spec N L R hN hL hR
  have hK : r ∈ orthant N := hardUnscale_mem_orthant N L R hL _
    (DroriTail.candidate_nonneg t (hardScale_nonneg N L R hL q (hs.1 p)) k a ha)
  have hinner : ⟪p,r⟫_ℝ = ⟪p,q⟫_ℝ := by
    dsimp [r,t]
    rw [inner_unscale_candidate N L R p k hp,
      hardUnscale_hardScale N L R hN hL hR]
  apply ConstrainedConjugate.maximizer_unique (one_div_pos.mpr hL)
    (hardDual_strongConvex N L R) p q r (hs.1 p) hK (hs.2.1 p)
  intro u hu
  have hv := hs.2.1 p u hu
  simp only [inner_sub_right] at hv ⊢
  change hardDual N L R r ≤ hardDual N L R q at hcost
  change hardDual N L R q+ (⟪p,u⟫_ℝ-⟪p,q⟫_ℝ) ≤ hardDual N L R u at hv
  rw [hinner]
  linarith

end SmoothDrori
