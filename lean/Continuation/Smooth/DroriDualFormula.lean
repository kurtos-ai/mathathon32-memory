module
public import Continuation.Smooth.DroriOracle
@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace
namespace SmoothDrori

def hardShift (N : ℕ) (L R : ℝ) (i : ℕ) : Space N :=
  -hardX N R i+(1/L) • hardG N L R i

lemma hardShift_apply (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (i : ℕ) (j : Fin (N+1)) :
    hardShift N L R i j = if j.val ≤ i then
      (zetaStar N R j.val-zetaStar N R (i+1))/
        Real.sqrt (zetaStar N R j.val-zetaStar N R (j.val+1)) else 0 := by
  have hd : 0 < zetaStar N R j.val-zetaStar N R (j.val+1) :=
    sub_pos.mpr (zetaStar_strictAnti N R hN hR j.val (by omega))
  have hs := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hL0 := ne_of_gt hL
  change -(hardX N R i j)+(1/L)*(hardG N L R i j) = _
  rw [hardX_apply,hardG_apply]
  by_cases hji : j.val < i
  · have hne : j.val ≠ i := by omega
    simp only [hji,hne,hji.le,ite_true,ite_false,mul_zero,add_zero]
    ring
  · by_cases he : j.val = i
    · subst i
      simp only [lt_self_iff_false,ite_false,le_refl,ite_true,neg_zero,zero_add]
      have heq := Real.sq_sqrt hd.le
      field_simp
      nlinarith [heq]
    · have hn : ¬ j.val ≤ i := by omega
      simp [hji,he,hn]

lemma hardHi_eq_shift (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (i : Fin (N+2)) (q : Space N) :
    SmoothDual.Hi (fun a : Fin (N+2) => hardX N R a.val)
      (fun a : Fin (N+2) => hardG N L R a.val)
      (fun a : Fin (N+2) => hardF N L R a.val) L i q =
      1/(2*L)*‖q‖^2 - ⟪hardShift N L R i.val,q⟫_ℝ-L*zetaStar N R (i.val+1) := by
  rw [SmoothDual.Hi_eq,norm_sub_sq_real]
  have hf := hardF_sub_norm N L R hN hL hR i.val (by omega)
  simp only [hardShift,inner_add_left,inner_neg_left,real_inner_smul_left]
  rw [real_inner_comm q (hardG N L R i.val)]
  linear_combination -hf

/-- Normalize the dual gradient coordinates by the hard-data diagonal. -/
def hardScale (N : ℕ) (L R : ℝ) (q : Space N) : Fin (N+1) → ℝ :=
  fun j => q j/(L*Real.sqrt (zetaStar N R j.val-zetaStar N R (j.val+1)))

def hardUnscale (N : ℕ) (L R : ℝ) (t : Fin (N+1) → ℝ) : Space N :=
  WithLp.toLp 2 (fun j => L*Real.sqrt (zetaStar N R j.val-zetaStar N R (j.val+1))*t j)

lemma hardUnscale_apply (N : ℕ) (L R : ℝ) (t : Fin (N+1) → ℝ) (j : Fin (N+1)) :
    hardUnscale N L R t j =
      L*Real.sqrt (zetaStar N R j.val-zetaStar N R (j.val+1))*t j := rfl

lemma hardUnscale_hardScale (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (q : Space N) : hardUnscale N L R (hardScale N L R q) = q := by
  ext j
  have hd : 0 < zetaStar N R j.val-zetaStar N R (j.val+1) :=
    sub_pos.mpr (zetaStar_strictAnti N R hN hR j.val (by omega))
  have hs := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hL0 := ne_of_gt hL
  simp only [hardUnscale_apply,hardScale]
  field_simp

lemma hardScale_hardUnscale (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (t : Fin (N+1) → ℝ) : hardScale N L R (hardUnscale N L R t) = t := by
  funext j
  have hd : 0 < zetaStar N R j.val-zetaStar N R (j.val+1) :=
    sub_pos.mpr (zetaStar_strictAnti N R hN hR j.val (by omega))
  have hs := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hL0 := ne_of_gt hL
  simp [hardUnscale_apply,hardScale,hL0,hs]

lemma hardScale_nonneg (N : ℕ) (L R : ℝ) (hL : 0 < L) (q : Space N)
    (hq : q ∈ orthant N) (j : Fin (N+1)) : 0 ≤ hardScale N L R q j := by
  exact div_nonneg (hq j) (mul_nonneg hL.le (Real.sqrt_nonneg _))

lemma hardUnscale_mem_orthant (N : ℕ) (L R : ℝ) (hL : 0 < L)
    (t : Fin (N+1) → ℝ) (ht : ∀ j, 0 ≤ t j) : hardUnscale N L R t ∈ orthant N := by
  intro j
  exact mul_nonneg (mul_nonneg hL.le (Real.sqrt_nonneg _)) (ht j)

lemma hardUnscale_norm_sq (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (t : Fin (N+1) → ℝ) :
    ‖hardUnscale N L R t‖^2 =
      L^2*∑ j : Fin (N+1), (zetaStar N R j.val-zetaStar N R (j.val+1))*(t j)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hardUnscale_apply,mul_pow,mul_pow,Real.sq_sqrt (sub_nonneg.mpr
    (zetaStar_strictAnti N R hN hR j.val (by omega)).le)]
  ring

lemma hardShift_inner_unscale (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (i : ℕ) (t : Fin (N+1) → ℝ) :
    ⟪hardShift N L R i,hardUnscale N L R t⟫_ℝ =
      L*∑ j : Fin (N+1), if j.val ≤ i then
        (zetaStar N R j.val-zetaStar N R (i+1))*t j else 0 := by
  rw [PiLp.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hardShift_apply N L R hN hL hR,hardUnscale_apply]
  simp only [RCLike.inner_apply,conj_trivial]
  split_ifs with hji
  · have hd : 0 < zetaStar N R j.val-zetaStar N R (j.val+1) :=
      sub_pos.mpr (zetaStar_strictAnti N R hN hR j.val (by omega))
    have hs := ne_of_gt (Real.sqrt_pos.mpr hd)
    field_simp
  · ring

/-- Exact scalar formula for each quadratic piece of the hard dual. -/
lemma hardHi_unscale (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (i : Fin (N+2)) (t : Fin (N+1) → ℝ) :
    SmoothDual.Hi (fun a : Fin (N+2) => hardX N R a.val)
      (fun a : Fin (N+2) => hardG N L R a.val)
      (fun a : Fin (N+2) => hardF N L R a.val) L i (hardUnscale N L R t) =
      L/2*(∑ j : Fin (N+1), (zetaStar N R j.val-zetaStar N R (j.val+1))*(t j)^2) -
      L*(zetaStar N R (i.val+1)+∑ j : Fin (N+1), if j.val ≤ i.val then
        (zetaStar N R j.val-zetaStar N R (i.val+1))*t j else 0) := by
  rw [hardHi_eq_shift N L R hN hL hR,hardUnscale_norm_sq N L R hN hR,
    hardShift_inner_unscale N L R hN hL hR]
  have hL0 := ne_of_gt hL
  field_simp
  ring

end SmoothDrori
