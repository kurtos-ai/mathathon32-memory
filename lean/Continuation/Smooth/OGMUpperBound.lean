module
public import Continuation.Smooth.OGM
public import Continuation.Smooth.Energy
public import Continuation.GJP.Simplex
public import Continuation.OracleTrajectory
public import Continuation.Smooth.ActualInterpolation

@[expose] public section
open SmoothBenchmark SmoothOGM
noncomputable section
namespace OGMVerified
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Y (N:ℕ) (L:ℝ) (x:E) (g:ℕ→E) (k:ℕ) : E :=
  x + ∑ j : Fin k, ogmACoeff N L k j.val • g j.val

def Eta (N:ℕ) (L:ℝ) (g:ℕ→E) (k:ℕ) : E :=
  ∑ j : Fin k, ogmECoeff N L k j.val • g j.val

lemma Y_succ (N:ℕ) (L:ℝ) (x:E) (g:ℕ→E) (k:ℕ) (hk:k<N) :
    Y N L x g (k+1) = Y N L x g k + (1 / theta N (k+1)) • Eta N L g k +
      (-(1+(2*theta N k-1)/theta N (k+1))/L) • g k := by
  unfold Y Eta
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, aCoeff_succ_eq N L k hk]
  simp_rw [aCoeff_succ_lt N L k _ hk (Fin.isLt _), add_smul, mul_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]
  module

lemma Eta_succ (N:ℕ) (L:ℝ) (g:ℕ→E) (k:ℕ) (hk:k<N) :
    Eta N L g (k+1) = (1 - 1/theta N (k+1)) • Eta N L g k +
      (-(2*theta N k-1)*(1-1/theta N (k+1))/L) • g k := by
  unfold Eta
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, eCoeff_succ_eq N L k hk]
  simp_rw [eCoeff_succ_lt N L k _ hk (Fin.isLt _), mul_smul]
  rw [← Finset.smul_sum]

def Z (N:ℕ) (L:ℝ) (x:E) (g:ℕ→E) (k:ℕ) := Y N L x g k + Eta N L g k

def A (N k:ℕ) : ℝ := if k<N then 2*theta N k^2 else theta N k^2

def B (N k:ℕ) : ℝ := if k<N then 2*theta N k else theta N k

lemma A_succ (N k:ℕ) (hk:k<N) : A N (k+1) = A N k + B N (k+1) := by
  unfold A B
  simp only [hk, ite_true]
  by_cases h:k+1<N
  · simp only [h, ite_true]
    have ht := GJP.theta_sq_standard N (k+1) (by omega) h
    simp only [Nat.add_sub_cancel] at ht
    linarith
  · have hkn:k+1=N := by omega
    simp only [h, ite_false]
    have ht := GJP.theta_sq_final N (by omega)
    have hn:N-1=k := by omega
    rw [hn] at ht
    have ht' : theta N (k+1)^2 = theta N (k+1) + 2*theta N k^2 := by simpa only [hkn] using ht
    linarith

lemma A_div_theta (N k:ℕ) (hk:k≤N) : A N k / theta N k = B N k := by
  have ht := ne_of_gt (theta_pos N k hk)
  unfold A B
  split_ifs <;> field_simp

lemma Z_succ (N:ℕ) (L:ℝ) (x:E) (g:ℕ→E) (k:ℕ) (hk:k<N) :
    Z N L x g (k+1) = Z N L x g k - (B N k/L) • g k := by
  unfold Z
  rw [Y_succ N L x g k hk, Eta_succ N L g k hk]
  simp only [B, hk, ite_true]
  module

def V (N:ℕ) (L:ℝ) (x:E) (g:ℕ→E) (k:ℕ) := Z N L x g k - (B N k/L) • g k

lemma V_succ (N:ℕ) (L:ℝ) (x:E) (g:ℕ→E) (k:ℕ) (hk:k<N) :
    V N L x g (k+1) = V N L x g k - (B N (k+1)/L) • g (k+1) := by
  unfold V
  rw [Z_succ N L x g k hk]

lemma Y_weighted (N:ℕ) (L:ℝ) (x:E) (g:ℕ→E) (k:ℕ) (hk:k<N) :
    A N (k+1) • Y N L x g (k+1) = A N k • Y N L x g k +
      B N (k+1) • V N L x g k - (A N k/L) • g k := by
  have ha := A_succ N k hk
  have hb := A_div_theta N (k+1) (by omega)
  have hb0 : B N k = 2*theta N k := by simp [B,hk]
  have hc : A N (k+1)*(1/theta N (k+1)) = B N (k+1) := by simpa [div_eq_mul_inv] using hb
  have hd : A N (k+1)* (-(1+(2*theta N k-1)/theta N (k+1))/L) =
      -(B N (k+1)*B N k + A N k)/L := by
    rw [hb0]
    calc _ = -(A N (k+1) + (2*theta N k-1)*(A N (k+1)/theta N (k+1)))/L := by ring
      _ = _ := by rw [hb,ha]; ring
  rw [Y_succ N L x g k hk]
  simp only [smul_add, smul_smul]
  rw [hc,hd]
  unfold V Z
  rw [ha]
  module

def query {n N:ℕ} {L R:ℝ} (I:SmoothAttain.Instance n L R) (k:ℕ) : EuclideanSpace ℝ (Fin n) :=
  if h:k≤N then OracleTrajectory.run (ogmW N L) I.G I.x0 ⟨k, by omega⟩ else I.x0

def grad {n N:ℕ} {L R:ℝ} (I:SmoothAttain.Instance n L R) (k:ℕ) := I.G (query (N:=N) I k)

lemma Y_query {n N:ℕ} {L R:ℝ} (I:SmoothAttain.Instance n L R) (k:ℕ) (hk:k≤N) :
    Y N L I.x0 (grad (N:=N) I) k = query (N:=N) I k := by
  rw [query, dite_eq_left hk, OracleTrajectory.run_eq]
  unfold Y
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hw : ogmW N L ⟨k,by omega⟩ ⟨j.val,by omega⟩ = ogmACoeff N L k j.val := by
    change (if j.val<k then ogmACoeff N L k j.val else 0) = _
    simp [j.isLt]
  rw [hw]
  have hj : j.val≤N := by omega
  simp [grad,query,hj]

lemma Y_shift {n N:ℕ} {L R:ℝ} (I:SmoothAttain.Instance n L R) (k:ℕ) (hk:k≤N) :
    Y N L (I.x0-I.xStar) (grad (N:=N) I) k = query (N:=N) I k - I.xStar := by
  rw [← Y_query I k hk]
  unfold Y
  module

open scoped InnerProductSpace

theorem actual_upper_bound {n N:ℕ} {L R:ℝ} (I:SmoothAttain.Instance n L R)
    (hL:0<L) :
    I.f (OracleTrajectory.run (ogmW N L) I.G I.x0 (Fin.last N)) - I.f I.xStar ≤
      L*R^2/(2*theta N N^2) := by
  let g := grad (N:=N) I
  let y := Y N L (I.x0-I.xStar) g
  let v := V N L (I.x0-I.xStar) g
  let f := fun k => I.f (query (N:=N) I k)
  have hr : ∀ k<N, 0 ≤ f k-f (k+1)-⟪g (k+1),y k-y (k+1)⟫_ℝ -
      (1/(2*L))*‖g k-g (k+1)‖^2 := by
    intro k hk
    have hy : y k-y (k+1) = query (N:=N) I k-query (N:=N) I (k+1) := by
      dsimp [y,g]
      rw [Y_shift I k (by omega), Y_shift I (k+1) (by omega)]
      abel
    rw [hy]
    exact I.interpolation_necessary hL _ _
  have hs : ∀ k≤N, 0 ≤ I.f I.xStar-f k+⟪g k,y k⟫_ℝ - (1/(2*L))*‖g k‖^2 := by
    intro k hk
    have h := I.interpolation_necessary hL I.xStar (query (N:=N) I k)
    have hy : y k = query (N:=N) I k-I.xStar := Y_shift I k hk
    have hn : I.xStar-query (N:=N) I k = -(query (N:=N) I k-I.xStar) := by abel
    rw [I.gradient_at_minimizer,zero_sub,norm_neg,hn,inner_neg_right,sub_neg_eq_add] at h
    rw [hy]
    exact h
  have ht := theta_pos N N le_rfl
  have he := OGMEnergy.objective_bound_scaled N L hL (I.x0-I.xStar) (I.f I.xStar)
    f (A N) (B N) y g v
    (by simp [y,Y])
    (by unfold A B; split_ifs <;> simp [theta_zero])
    (by simp [v,V,Z,Y,Eta])
    (A_succ N)
    (by intro k hk; simp only [A,B,hk,ite_true]; ring)
    (by simp [A,B])
    (V_succ N L (I.x0-I.xStar) g)
    (Y_weighted N L (I.x0-I.xStar) g)
    (by simp only [A,lt_self_iff_false,ite_false]; positivity)
    (by intro k hk; simp only [A,hk,ite_true]; positivity)
    (by intro k hk; have ht := theta_pos N k hk; unfold B; split_ifs <;> positivity)
    hr hs
  have hsq : ‖I.x0-I.xStar‖^2 ≤ R^2 := by nlinarith [I.near,norm_nonneg (I.x0-I.xStar)]
  have hbound : L*‖I.x0-I.xStar‖^2/(2*A N N) ≤ L*R^2/(2*theta N N^2) := by
    simp only [A,lt_self_iff_false,ite_false]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hL.le) (by positivity)
  have he' := le_trans he hbound
  change I.f (query (N:=N) I N) - I.f I.xStar ≤ L*R^2/(2*theta N N^2) at he'
  have hq : query (N:=N) I N = OracleTrajectory.run (ogmW N L) I.G I.x0 (Fin.last N) := by
    unfold query
    rw [dite_eq_left (show N≤N from le_rfl)]
    apply congrArg (OracleTrajectory.run (ogmW N L) I.G I.x0)
    exact Fin.ext rfl
  rw [hq] at he'
  exact he' 

end OGMVerified

end
