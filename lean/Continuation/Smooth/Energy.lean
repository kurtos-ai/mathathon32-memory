module
public import Mathlib
/-! Algebraic energy certificate used for OGM. The theorem assumes explicit
weight and vector recurrences and interpolation residual inequalities, and
proves the objective bound by telescoping. Identification of the actual OGM
coefficients with these recurrences is a separate obligation. -/
@[expose] public section

open scoped InnerProductSpace
namespace OGMEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def R (f0 f1 : ℝ) (g0 g1 y0 y1 : E) : ℝ :=
  f0-f1-⟪g1,y0-y1⟫_ℝ-(1/2:ℝ)*‖g0-g1‖^2

noncomputable def S (fs f : ℝ) (g y : E) : ℝ := fs-f+⟪g,y⟫_ℝ-(1/2:ℝ)*‖g‖^2

theorem energy_step (a b A fs f0 f1 : ℝ) (y0 y1 g0 g1 v0 v1 : E)
    (hA : A=a+b) (hv : v1=v0-b•g1)
    (hy : A•y1=a•y0+b•v0-a•g0) :
    a*R f0 f1 g0 g1 y0 y1+b*S fs f1 g1 y1+
        (1/2:ℝ)*‖v1‖^2+((A-b^2)/2)*‖g1‖^2 -
        ((1/2:ℝ)*‖v0‖^2-(a/2)*‖g0‖^2) =
      a*(f0-fs)-A*(f1-fs) := by
  subst A
  have hi := congrArg (fun z : E => ⟪g1,z⟫_ℝ) hy
  simp only [inner_add_right,inner_sub_right,real_inner_smul_right] at hi
  simp only [R,S,hv,← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm g0 g1,real_inner_comm v0 g1] at hi
  rw [real_inner_comm g0 g1,real_inner_comm v0 g1]
  nlinarith [hi]

theorem energy_base (b fs f : ℝ) (x g : E) :
    b*S fs f g x+(1/2:ℝ)*‖x-b•g‖^2+((b-b^2)/2)*‖g‖^2 =
      (1/2:ℝ)*‖x‖^2-b*(f-fs) := by
  simp only [S,← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm x g]
  ring

/-- A purely algebraic identity for each prefix; the final gradient correction
vanishes for the terminal OGM weights. -/
theorem prefix_identity (N : ℕ) (x : E) (fs : ℝ) (f a b : ℕ → ℝ) (y g v : ℕ → E)
    (hy0 : y 0=x) (ha0 : a 0=b 0) (hv0 : v 0=x-b 0•g 0)
    (ha : ∀ k<N, a (k+1)=a k+b (k+1))
    (hb : ∀ k<N, b k^2=2*a k)
    (hv : ∀ k<N, v (k+1)=v k-b (k+1)•g (k+1))
    (hy : ∀ k<N, a (k+1)•y (k+1)=a k•y k+b (k+1)•v k-a k•g k) :
    (∑ k ∈ Finset.range N, a k*R (f k) (f (k+1)) (g k) (g (k+1)) (y k) (y (k+1)))+
      (∑ k ∈ Finset.range (N+1), b k*S fs (f k) (g k) (y k))+
      (1/2:ℝ)*‖v N‖^2+((a N-b N^2)/2)*‖g N‖^2 =
        (1/2:ℝ)*‖x‖^2-a N*(f N-fs) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,Finset.sum_range_succ,zero_add,ha0,hy0,hv0]
    exact energy_base (b 0) fs (f 0) x (g 0)
  | succ N ih =>
    have hi := ih (fun k hk => ha k (by omega)) (fun k hk => hb k (by omega))
      (fun k hk => hv k (by omega)) (fun k hk => hy k (by omega))
    have hs := energy_step (a N) (b (N+1)) (a (N+1)) fs (f N) (f (N+1))
      (y N) (y (N+1)) (g N) (g (N+1)) (v N) (v (N+1))
      (ha N (by omega)) (hv N (by omega)) (hy N (by omega))
    rw [hb N (by omega)] at hi
    rw [Finset.sum_range_succ,Finset.sum_range_succ (n:=N+1)]
    linarith

theorem terminal_identity (N : ℕ) (x : E) (fs : ℝ) (f a b : ℕ → ℝ) (y g v : ℕ → E)
    (hy0 : y 0=x) (ha0 : a 0=b 0) (hv0 : v 0=x-b 0•g 0)
    (ha : ∀ k<N, a (k+1)=a k+b (k+1))
    (hb : ∀ k<N, b k^2=2*a k) (hfinal : b N^2=a N)
    (hv : ∀ k<N, v (k+1)=v k-b (k+1)•g (k+1))
    (hy : ∀ k<N, a (k+1)•y (k+1)=a k•y k+b (k+1)•v k-a k•g k) :
    (∑ k ∈ Finset.range N, a k*R (f k) (f (k+1)) (g k) (g (k+1)) (y k) (y (k+1)))+
      (∑ k ∈ Finset.range (N+1), b k*S fs (f k) (g k) (y k))+
      (1/2:ℝ)*‖v N‖^2 = (1/2:ℝ)*‖x‖^2-a N*(f N-fs) := by
  simpa only [hfinal,sub_self,zero_div,zero_mul,add_zero] using
    prefix_identity N x fs f a b y g v hy0 ha0 hv0 ha hb hv hy

theorem objective_bound (N : ℕ) (x : E) (fs : ℝ) (f a b : ℕ → ℝ) (y g v : ℕ → E)
    (hy0 : y 0=x) (ha0 : a 0=b 0) (hv0 : v 0=x-b 0•g 0)
    (ha : ∀ k<N, a (k+1)=a k+b (k+1))
    (hb : ∀ k<N, b k^2=2*a k) (hfinal : b N^2=a N)
    (hv : ∀ k<N, v (k+1)=v k-b (k+1)•g (k+1))
    (hy : ∀ k<N, a (k+1)•y (k+1)=a k•y k+b (k+1)•v k-a k•g k)
    (hapos : 0<a N) (han : ∀ k<N, 0≤a k) (hbn : ∀ k≤N, 0≤b k)
    (hR : ∀ k<N, 0≤R (f k) (f (k+1)) (g k) (g (k+1)) (y k) (y (k+1)))
    (hS : ∀ k≤N, 0≤S fs (f k) (g k) (y k)) :
    f N-fs ≤ ‖x‖^2/(2*a N) := by
  have hi := terminal_identity N x fs f a b y g v hy0 ha0 hv0 ha hb hfinal hv hy
  have hr : 0≤∑ k ∈ Finset.range N, a k*R (f k) (f (k+1)) (g k) (g (k+1)) (y k) (y (k+1)) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (han k (Finset.mem_range.mp hk)) (hR k (Finset.mem_range.mp hk)))
  have hs : 0≤∑ k ∈ Finset.range (N+1), b k*S fs (f k) (g k) (y k) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hbn k (by simpa using Finset.mem_range.mp hk)) (hS k (by simpa using Finset.mem_range.mp hk)))
  rw [le_div_iff₀ (by positivity : 0<2*a N)]
  nlinarith [sq_nonneg ‖v N‖]

theorem R_scale (L : ℝ) (hL : 0<L) (f0 f1 : ℝ) (g0 g1 y0 y1 : E) :
    R (f0/L) (f1/L) ((1/L)•g0) ((1/L)•g1) y0 y1 =
      (1/L)*(f0-f1-⟪g1,y0-y1⟫_ℝ-(1/(2*L))*‖g0-g1‖^2) := by
  simp only [R,real_inner_smul_left,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hL)]
  field_simp

theorem S_scale (L : ℝ) (hL : 0<L) (fs f : ℝ) (g y : E) :
    S (fs/L) (f/L) ((1/L)•g) y =
      (1/L)*(fs-f+⟪g,y⟫_ℝ-(1/(2*L))*‖g‖^2) := by
  simp only [S,real_inner_smul_left,norm_smul,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hL)]
  field_simp

theorem objective_bound_scaled (N : ℕ) (L : ℝ) (hL : 0<L) (x : E) (fs : ℝ)
    (f a b : ℕ → ℝ) (y g v : ℕ → E)
    (hy0 : y 0=x) (ha0 : a 0=b 0) (hv0 : v 0=x-(b 0/L)•g 0)
    (ha : ∀ k<N, a (k+1)=a k+b (k+1))
    (hb : ∀ k<N, b k^2=2*a k) (hfinal : b N^2=a N)
    (hv : ∀ k<N, v (k+1)=v k-(b (k+1)/L)•g (k+1))
    (hy : ∀ k<N, a (k+1)•y (k+1)=a k•y k+b (k+1)•v k-(a k/L)•g k)
    (hapos : 0<a N) (han : ∀ k<N, 0≤a k) (hbn : ∀ k≤N, 0≤b k)
    (hR : ∀ k<N, 0≤f k-f (k+1)-⟪g (k+1),y k-y (k+1)⟫_ℝ-(1/(2*L))*‖g k-g (k+1)‖^2)
    (hS : ∀ k≤N, 0≤fs-f k+⟪g k,y k⟫_ℝ-(1/(2*L))*‖g k‖^2) :
    f N-fs ≤ L*‖x‖^2/(2*a N) := by
  have hv0' : v 0=x-b 0•((1/L)•g 0) := by simpa only [smul_smul,mul_one_div] using hv0
  have hv' : ∀ k<N, v (k+1)=v k-b (k+1)•((1/L)•g (k+1)) := by
    intro k hk
    simpa only [smul_smul,mul_one_div] using hv k hk
  have hy' : ∀ k<N, a (k+1)•y (k+1)=a k•y k+b (k+1)•v k-a k•((1/L)•g k) := by
    intro k hk
    simpa only [smul_smul,mul_one_div] using hy k hk
  have hr : ∀ k<N, 0≤R (f k/L) (f (k+1)/L) ((1/L)•g k) ((1/L)•g (k+1)) (y k) (y (k+1)) := by
    intro k hk
    rw [R_scale L hL]
    exact mul_nonneg (one_div_pos.mpr hL).le (hR k hk)
  have hs : ∀ k≤N, 0≤S (fs/L) (f k/L) ((1/L)•g k) (y k) := by
    intro k hk
    rw [S_scale L hL]
    exact mul_nonneg (one_div_pos.mpr hL).le (hS k hk)
  have hh := objective_bound N x (fs/L) (fun k => f k/L) a b y (fun k => (1/L)•g k) v
    hy0 ha0 hv0' ha hb hfinal hv' hy' hapos han hbn hr hs
  rw [← sub_div] at hh
  have ht := (div_le_iff₀ hL).mp hh
  convert ht using 1 <;> ring

end OGMEnergy
