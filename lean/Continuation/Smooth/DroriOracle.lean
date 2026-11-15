module
public import Continuation.Smooth.DroriRadius
public import Continuation.Smooth.ConstrainedConjugateRegularity
public import Continuation.Smooth.Attain.Instances
public import Continuation.OracleTrajectory
@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace
namespace SmoothDrori

lemma hardX_zero (N : ℕ) (R : ℝ) : hardX N R 0 = 0 := by
  ext j
  simp [hardX_apply]

abbrev Space (N : ℕ) := EuclideanSpace ℝ (Fin (N+1))

def orthant (N : ℕ) : Set (Space N) := {q | ∀ j, 0 ≤ q j}

def hardDual (N : ℕ) (L R : ℝ) : Space N → ℝ :=
  SmoothDual.H (fun i : Fin (N+2) => hardX N R i.val)
    (fun i : Fin (N+2) => hardG N L R i.val)
    (fun i : Fin (N+2) => hardF N L R i.val) L

lemma orthant_closed (N : ℕ) : IsClosed (orthant N) := by
  have he : orthant N = ⋂ j : Fin (N+1), {q : Space N | 0 ≤ q j} := by
    ext q; simp [orthant]
  rw [he]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin (N+1) => ℝ) j))

lemma orthant_convex (N : ℕ) : Convex ℝ (orthant N) := by
  intro x hx y hy a b ha hb hab j
  change 0 ≤ a*x j+b*y j
  exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))

lemma hardG_mem_orthant (N : ℕ) (L R : ℝ) (hL : 0 < L) (i : ℕ) :
    hardG N L R i ∈ orthant N := by
  intro j
  rw [hardG_apply]
  split_ifs <;> positivity

lemma hardDual_strongConvex (N : ℕ) (L R : ℝ) :
    StrongConvexOn (orthant N) (1/L) (hardDual N L R) := by
  refine ⟨orthant_convex N, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (SmoothDual.H_strongConvex
    (x:=fun i : Fin (N+2) => hardX N R i.val)
    (g:=fun i : Fin (N+2) => hardG N L R i.val)
    (f:=fun i : Fin (N+2) => hardF N L R i.val) (L:=L)).2
      (mem_univ x) (mem_univ y) ha hb hab

lemma hardDual_continuous (N : ℕ) (L R : ℝ) : Continuous (hardDual N L R) :=
  SmoothDual.H_continuous _ _ _

lemma hardDual_support (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L)
    (hR : 0 < R) (i : ℕ) (hi : i ≤ N+1) (u : Space N) :
    hardDual N L R (hardG N L R i) +
      ⟪hardX N R i,u-hardG N L R i⟫_ℝ ≤ hardDual N L R u := by
  exact SmoothDual.H_subgradient_weak
    (x:=fun i : Fin (N+2) => hardX N R i.val)
    (g:=fun i : Fin (N+2) => hardG N L R i.val)
    (f:=fun i : Fin (N+2) => hardF N L R i.val) hL
    (fun i j => hardData_interpolation N L R hN hL hR i.val j.val (by omega) (by omega))
    ⟨i,by omega⟩ u

lemma hardDual_contact (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L)
    (hR : 0 < R) (i : ℕ) (hi : i ≤ N+1) :
    hardDual N L R (hardG N L R i) =
      ⟪hardG N L R i,hardX N R i⟫_ℝ-hardF N L R i := by
  exact SmoothDual.H_contact'
    (x:=fun i : Fin (N+2) => hardX N R i.val)
    (g:=fun i : Fin (N+2) => hardG N L R i.val)
    (f:=fun i : Fin (N+2) => hardF N L R i.val)
    (fun i j => hardData_interpolation N L R hN hL hR i.val j.val (by omega) (by omega))
    ⟨i,by omega⟩

lemma exists_orthant_hardGradient (N : ℕ) (L R : ℝ) (hN : 1 ≤ N)
    (hL : 0 < L) (hR : 0 < R) :
    ∃ G : Space N → Space N, (∀ p, G p ∈ orthant N) ∧
      (∀ p u, u ∈ orthant N → hardDual N L R (G p)+⟪p,u-G p⟫_ℝ ≤ hardDual N L R u) ∧
      (∀ p, HasGradientAt (ConstrainedConjugate.value (hardDual N L R) G) (G p) p) ∧
      ConvexOn ℝ univ (ConstrainedConjugate.value (hardDual N L R) G) ∧
      LipschitzWith (Real.toNNReal L) G := by
  obtain ⟨G,hK,hVI,hGrad,hConv,hLip⟩ :=
    ConstrainedConjugate.exists_smooth_conjugate (one_div_pos.mpr hL)
      (orthant_closed N) (hardDual_strongConvex N L R)
      (hardDual_continuous N L R).continuousOn (hardX N R 0) (hardG N L R 0)
      (hardG_mem_orthant N L R hL 0)
      (fun u _ => hardDual_support N L R hN hL hR 0 (by omega) u)
  refine ⟨G,hK,hVI,hGrad,hConv,?_⟩
  simpa only [one_div,inv_inv] using hLip

/-- The actual gradient selected from the orthant-constrained conjugate problem. -/
def hardGradient (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    Space N → Space N := (exists_orthant_hardGradient N L R hN hL hR).choose

/-- Drori's orthant-constrained smooth hard function, defined everywhere. -/
def hardFunction (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    Space N → ℝ := ConstrainedConjugate.value (hardDual N L R) (hardGradient N L R hN hL hR)

lemma hardGradient_spec (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    (∀ p, hardGradient N L R hN hL hR p ∈ orthant N) ∧
    (∀ p u, u ∈ orthant N → hardDual N L R (hardGradient N L R hN hL hR p)+
      ⟪p,u-hardGradient N L R hN hL hR p⟫_ℝ ≤ hardDual N L R u) ∧
    (∀ p, HasGradientAt (hardFunction N L R hN hL hR) (hardGradient N L R hN hL hR p) p) ∧
    ConvexOn ℝ univ (hardFunction N L R hN hL hR) ∧
    LipschitzWith (Real.toNNReal L) (hardGradient N L R hN hL hR) :=
  (exists_orthant_hardGradient N L R hN hL hR).choose_spec

lemma hardGradient_at_data (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (i : ℕ) (hi : i ≤ N+1) :
    hardGradient N L R hN hL hR (hardX N R i) = hardG N L R i := by
  have hs := hardGradient_spec N L R hN hL hR
  exact ConstrainedConjugate.maximizer_unique (one_div_pos.mpr hL)
    (hardDual_strongConvex N L R) (hardX N R i) _ _ (hs.1 _) (hardG_mem_orthant N L R hL i)
    (hs.2.1 _) (fun u _ => hardDual_support N L R hN hL hR i hi u)

lemma hardFunction_at_data (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (i : ℕ) (hi : i ≤ N+1) :
    hardFunction N L R hN hL hR (hardX N R i) = hardF N L R i := by
  dsimp only [hardFunction,ConstrainedConjugate.value,ConjugateRegularity.value]
  rw [hardGradient_at_data N L R hN hL hR i hi,hardDual_contact N L R hN hL hR i hi]
  rw [real_inner_comm (hardX N R i) (hardG N L R i)]
  ring

lemma hardFunction_minimizer (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    IsMinOn (hardFunction N L R hN hL hR) univ (hardX N R (N+1)) := by
  intro y _
  have hs := hardGradient_spec N L R hN hL hR
  have ht := SmoothNecessary.tangent_lower hs.2.2.1 hs.2.2.2.1 (hardX N R (N+1)) y
  rw [hardGradient_at_data N L R hN hL hR (N+1) le_rfl] at ht
  simpa [hardG] using ht

/-- The concrete hard function is a genuine smooth-convex instance of radius R. -/
def hardInstance (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R) :
    SmoothAttain.Instance (N+1) L R where
  f := hardFunction N L R hN hL hR
  G := hardGradient N L R hN hL hR
  hasGrad := (hardGradient_spec N L R hN hL hR).2.2.1
  convex := (hardGradient_spec N L R hN hL hR).2.2.2.1
  lip := Real.toNNReal L
  lip_eq := Real.coe_toNNReal _ hL.le
  lipschitz := (hardGradient_spec N L R hN hL hR).2.2.2.2
  x0 := 0
  xStar := hardX N R (N+1)
  isMin := hardFunction_minimizer N L R hN hL hR
  near := by simpa [hardX_minimizer_norm N R hN hR] using (le_refl R)

/-- Vectors supported in the first k coordinates. -/
def prefixSpace (N k : ℕ) : Submodule ℝ (Space N) where
  carrier := {x | ∀ j : Fin (N+1), k ≤ j.val → x j = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb j hj; simp [ha j hj,hb j hj]
  smul_mem' := by intro a b hb j hj; simp [hb j hj]

lemma prefixSpace_mono (N : ℕ) : Monotone (prefixSpace N) := by
  intro i j hij x hx k hk
  exact hx k (hij.trans hk)

lemma hardFunction_lower_on_prefix (N : ℕ) (L R : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hR : 0 < R)
    (k : ℕ) (hk : k ≤ N) (y : Space N) (hy : y ∈ prefixSpace N k) :
    hardF N L R k ≤ hardFunction N L R hN hL hR y := by
  have hs := hardGradient_spec N L R hN hL hR
  have ht := SmoothNecessary.tangent_lower hs.2.2.1 hs.2.2.2.1 (hardX N R k) y
  rw [hardGradient_at_data N L R hN hL hR k (by omega),
    hardFunction_at_data N L R hN hL hR k (by omega),inner_sub_right,
    hardG_inner N L R k hk,hardG_inner_hardX N L R hN hR k k hk] at ht
  have hyk := hy ⟨k,by omega⟩ le_rfl
  simpa only [hyk,mul_zero,lt_self_iff_false,ite_false,sub_zero,add_zero] using ht

end SmoothDrori
