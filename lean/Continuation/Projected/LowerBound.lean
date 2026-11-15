module
public import Continuation.Projected.Recurrence
public import RealizationCore.RegisterMachine
public import Mathlib
/-! Projected memory lower bound. On any nontrivial closed convex domain,
small formal-input perturbations in an interior segment recover the ordinary
linear machine after applying an inner-product functional. The complete query
trajectory, rather than only the terminal map, determines the cut-rank bound. -/
@[expose] public section

open Set
open scoped InnerProductSpace
noncomputable section
namespace Continuation.Projected
open Continuation.ProjectedSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {N s : ℕ} {K : Set E}

theorem projection_correction_orthogonal {u x v : E} {ε : ℝ} (hε : 0 < ε)
    (hp : ProjRelation K u x) (hplus : x+ε•v ∈ K) (hminus : x-ε•v ∈ K) :
    ⟪u-x,v⟫_ℝ = 0 := by
  have ha := hp.2 (x+ε•v) hplus
  have hb := hp.2 (x-ε•v) hminus
  have hsub : x-ε•v-x = -(ε•v) := by abel
  simp only [add_sub_cancel_left,real_inner_smul_right] at ha
  rw [hsub,inner_neg_right,real_inner_smul_right] at hb
  nlinarith

theorem segment_coordinate_mem (hK : Convex ℝ K) (q v : E)
    (hminus : q-v ∈ K) (hplus : q+v ∈ K) {t : ℝ} (ht : |t| ≤ 1) : q+t•v ∈ K := by
  have hcomb := hK hminus hplus (show 0 ≤ (1-t)/2 by linarith [(abs_le.mp ht).2])
    (show 0 ≤ (1+t)/2 by linarith [(abs_le.mp ht).1])
    (show (1-t)/2+(1+t)/2=1 by ring)
  have heq : ((1-t)/2) • (q-v)+((1+t)/2) • (q+v) = q+t•v := by module
  rwa [heq] at hcomb

theorem projection_correction_orthogonal_of_interior_segment (hK : Convex ℝ K)
    (q v u : E) (hminus : q-v ∈ K) (hplus : q+v ∈ K)
    {t : ℝ} (ht : |t| < 1) (hp : ProjRelation K u (q+t•v)) :
    ⟪u-(q+t•v),v⟫_ℝ = 0 := by
  let ε : ℝ := (1-|t|)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  apply projection_correction_orthogonal hε hp
  · have heq : q+t•v+ε•v = q+(t+ε)•v := by module
    rw [heq]
    apply segment_coordinate_mem hK q v hminus hplus
    rw [abs_le]
    dsimp [ε]
    constructor <;> linarith [le_abs_self t,neg_abs_le t,abs_nonneg t]
  · have heq : q+t•v-ε•v = q+(t-ε)•v := by module
    rw [heq]
    apply segment_coordinate_mem hK q v hminus hplus
    rw [abs_le]
    dsimp [ε]
    constructor <;> linarith [le_abs_self t,neg_abs_le t,abs_nonneg t]


def ordinary (M : ProjectedMachine K N s) : RegisterMachine.Machine N s where
  F := M.F
  b := M.b
  c := fun k => M.c k.castSucc
  o := M.c (Fin.last N)

theorem target_succ_increment (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (a : ℝ) (g : Fin N → ℝ) (k : Fin N) :
    RegisterMachine.target N W a g k.succ = RegisterMachine.target N W a g k.castSucc +
      W k.succ k.castSucc * g k +
      ∑ j : Fin k.val, (W k.succ ⟨j.val,by omega⟩-W k.castSucc ⟨j.val,by omega⟩) * g ⟨j.val,by omega⟩ := by
  unfold RegisterMachine.target
  simp only [Fin.val_succ,Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,sub_mul,Finset.sum_sub_distrib]
  change a + (_ + W k.succ k.castSucc * g k) = _
  ring

theorem direct_segment (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (q v : E) (a ε : ℝ) (g : Fin N → ℝ)
    (hmem : ∀ k : Fin (N+1), q+(ε*RegisterMachine.target N W a g k)•v ∈ K) :
    ∀ n : ℕ, ∀ hn : n ≤ N,
      directStateAux hK hcK hneK W (q+(ε*a)•v) (fun j => (ε*g j)•v) n =
        q+(ε*RegisterMachine.target N W a g ⟨n,by omega⟩)•v := by
  intro n
  induction n with
  | zero => intro hn; simp [directStateAux,RegisterMachine.target]
  | succ n ih =>
    intro hn
    have hnN : n < N := by omega
    rw [directStateAux,dite_eq_left hnN,ih (by omega)]
    dsimp only
    have ht := target_succ_increment W a g ⟨n,hnN⟩
    simp only [Fin.val_mk,Fin.succ_mk,Fin.castSucc_mk] at ht
    have heq :
        q+(ε*RegisterMachine.target N W a g ⟨n,by omega⟩)•v +
          (W ⟨n+1,by omega⟩ ⟨n,by omega⟩ • ((ε*g ⟨n,hnN⟩)•v) +
          ∑ j : Fin n, (W ⟨n+1,by omega⟩ ⟨j.val,by omega⟩-W ⟨n,by omega⟩ ⟨j.val,by omega⟩) • ((ε*g ⟨j.val,by omega⟩)•v)) =
        q+(ε*RegisterMachine.target N W a g ⟨n+1,by omega⟩)•v := by
      simp only [smul_smul,← Finset.sum_smul]
      rw [ht]
      simp only [mul_add,Finset.mul_sum]
      have hs : (∑ i : Fin n, (W ⟨n+1,by omega⟩ ⟨i.val,by omega⟩-W ⟨n,by omega⟩ ⟨i.val,by omega⟩) * (ε*g ⟨i.val,by omega⟩)) =
          ∑ i : Fin n, ε*((W ⟨n+1,by omega⟩ ⟨i.val,by omega⟩-W ⟨n,by omega⟩ ⟨i.val,by omega⟩) * g ⟨i.val,by omega⟩) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      module
    rw [heq]
    exact piK_of_mem hK hcK hneK (hmem ⟨n+1,by omega⟩)

def rawState (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (g : Fin N → E) (k : Fin N) : Fin s → E :=
  fun r => (∑ j : Fin s, M.F k r j • projStateAux hK hcK hneK M x0 g k.val j) + M.b k r • g k

def correction (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (g : Fin N → E) (k : Fin N) : E :=
  let u := weightedSum (M.c k.succ) (rawState hK hcK hneK M x0 g k)
  piK hK hcK hneK u-u

theorem state_scalarization (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 v : E) (g : Fin N → E)
    (hzero : ∀ k, ⟪correction hK hcK hneK M x0 g k,v⟫_ℝ=0) :
    ∀ n : ℕ, ∀ hn : n ≤ N, ∀ r : Fin s,
      ⟪projStateAux hK hcK hneK M x0 g n r,v⟫_ℝ =
      RegisterMachine.stateNat N s (ordinary M) ⟪x0,v⟫_ℝ (fun j => ⟪g j,v⟫_ℝ) n r := by
  intro n
  induction n with
  | zero =>
    intro _hn r
    by_cases hr : r.val=0 <;> simp [projStateAux,initState,e1Vec,RegisterMachine.stateNat,RegisterMachine.e1,hr]
  | succ n ih =>
    intro hn r
    have hnN : n < N := by omega
    rw [projStateAux_succ hK hcK hneK M x0 g n hnN,
      RegisterMachine.stateNat_succ N s (ordinary M) _ _ n hnN]
    change ⟪rawState hK hcK hneK M x0 g ⟨n,hnN⟩ r +
      M.p ⟨n,hnN⟩ r • correction hK hcK hneK M x0 g ⟨n,hnN⟩,v⟫_ℝ = _
    simp only [inner_add_left,real_inner_smul_left,hzero,mul_zero,add_zero]
    simp only [rawState,inner_add_left,sum_inner,real_inner_smul_left]
    simp only [ih (by omega),ordinary]

theorem query_scalarization (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 v : E) (g : Fin N → E)
    (hzero : ∀ k, ⟪correction hK hcK hneK M x0 g k,v⟫_ℝ=0) (k : Fin (N+1)) :
    ⟪projQuery hK hcK hneK M x0 g k,v⟫_ℝ =
      RegisterMachine.dot (M.c k) (RegisterMachine.stateNat N s (ordinary M) ⟪x0,v⟫_ℝ (fun j => ⟪g j,v⟫_ℝ) k.val) := by
  simp only [projQuery,weightedSum,sum_inner,real_inner_smul_left,RegisterMachine.dot]
  apply Finset.sum_congr rfl
  intro i _
  rw [state_scalarization hK hcK hneK M x0 v g hzero k.val (by omega) i]

theorem state_affine (M : RegisterMachine.Machine N s) (a b c : ℝ) (d e : Fin N → ℝ) (n : ℕ) :
    RegisterMachine.stateNat N s M (a+b*c) (fun j => d j+b*e j) n =
      fun r => RegisterMachine.stateNat N s M a d n r + b*RegisterMachine.stateNat N s M c e n r := by
  induction n with
  | zero => funext r; simp only [RegisterMachine.stateNat]; ring
  | succ n ih =>
    by_cases hn : n < N
    · rw [RegisterMachine.stateNat_succ N s M _ _ n hn,
        RegisterMachine.stateNat_succ N s M a d n hn,
        RegisterMachine.stateNat_succ N s M c e n hn,ih]
      funext r
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_left_comm,
        add_assoc,add_left_comm,add_comm]
    · simp only [RegisterMachine.stateNat,dite_eq_right hn,ih]

theorem dot_affine (u v w : Fin s → ℝ) (b : ℝ) :
    RegisterMachine.dot u (fun r => v r+b*w r) = RegisterMachine.dot u v+b*RegisterMachine.dot u w := by
  simp only [RegisterMachine.dot,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exists_small_scale {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, |ε*f i| < 1 := by
  let ε : ℝ := 1/(‖f‖+1)
  have hd : 0 < ‖f‖+1 := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,fun i => ?_⟩
  rw [abs_mul,abs_of_pos hε]
  have hi : |f i| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm f i
  have hh := mul_le_mul_of_nonneg_left hi hε.le
  have hlt : ε*‖f‖ < 1 := by
    dsimp [ε]
    rw [one_div_mul_eq_div,div_lt_one hd]
    linarith
  exact lt_of_le_of_lt hh hlt

theorem correction_inner_zero_of_segment (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 q v : E) (g : Fin N → E)
    (hminus : q-v ∈ K) (hplus : q+v ∈ K) (t : Fin (N+1) → ℝ)
    (ht : ∀ k, |t k| < 1) (hread : ∀ k, projQuery hK hcK hneK M x0 g k=q+t k•v) :
    ∀ k, ⟪correction hK hcK hneK M x0 g k,v⟫_ℝ=0 := by
  intro k
  have hr := hread k.succ
  change projQuery hK hcK hneK M x0 g ⟨k.val+1,by omega⟩ = _ at hr
  rw [projQuery_succ_eq_piK hK hcK hneK M x0 g k] at hr
  change piK hK hcK hneK (weightedSum (M.c k.succ) (rawState hK hcK hneK M x0 g k)) = q+t k.succ•v at hr
  have hp : ProjRelation K (weightedSum (M.c k.succ) (rawState hK hcK hneK M x0 g k)) (q+t k.succ•v) := by
    apply (proj_graph_correct hK hcK hneK).mpr
    exact hr.symm
  have ho := projection_correction_orthogonal_of_interior_segment hK q v _ hminus hplus (ht k.succ) hp
  change ⟪piK hK hcK hneK (weightedSum (M.c k.succ) (rawState hK hcK hneK M x0 g k)) -
    weightedSum (M.c k.succ) (rawState hK hcK hneK M x0 g k),v⟫_ℝ=0
  rw [hr]
  simp only [inner_sub_left] at ho ⊢
  linarith

/-- Correctness includes every formal gradient sequence and every query, including the terminal output. -/
def ProjectedRealizes (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : ProjectedMachine K N s) : Prop :=
  ∀ x0 ∈ K, ∀ g : Fin N → E, ∀ k : Fin (N+1),
    projQuery hK hcK hneK M x0 g k = directStateAux hK hcK hneK W x0 g k.val

theorem readout_on_segment (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : ProjectedMachine K N s)
    (hR : ProjectedRealizes hK hcK hneK W M)
    (q v : E) (hminus : q-v ∈ K) (hplus : q+v ∈ K)
    (a ε : ℝ) (g : Fin N → ℝ)
    (ht : ∀ k, |ε*RegisterMachine.target N W a g k|<1) (k : Fin (N+1)) :
    RegisterMachine.dot (M.c k)
      (RegisterMachine.stateNat N s (ordinary M) (⟪q,v⟫_ℝ+(ε*⟪v,v⟫_ℝ)*a)
        (fun j => (ε*⟪v,v⟫_ℝ)*g j) k.val) =
      ⟪q,v⟫_ℝ+(ε*⟪v,v⟫_ℝ)*RegisterMachine.target N W a g k := by
  have hmem (i : Fin (N+1)) : q+(ε*RegisterMachine.target N W a g i)•v ∈ K :=
    segment_coordinate_mem hK q v hminus hplus (ht i).le
  have hx0 : q+(ε*a)•v ∈ K := by simpa [RegisterMachine.target] using hmem ⟨0,by omega⟩
  have hr (i : Fin (N+1)) :
      projQuery hK hcK hneK M (q+(ε*a)•v) (fun j => (ε*g j)•v) i =
        q+(ε*RegisterMachine.target N W a g i)•v := by
    rw [hR _ hx0 _ i]
    exact direct_segment hK hcK hneK W q v a ε g hmem i.val (by omega)
  have hz := correction_inner_zero_of_segment hK hcK hneK M (q+(ε*a)•v) q v
    (fun j => (ε*g j)•v) hminus hplus (fun i => ε*RegisterMachine.target N W a g i) ht hr
  have hs := query_scalarization hK hcK hneK M (q+(ε*a)•v) v (fun j => (ε*g j)•v) hz k
  have hi : ⟪q+(ε*a)•v,v⟫_ℝ = ⟪q,v⟫_ℝ+(ε*⟪v,v⟫_ℝ)*a := by
    simp only [inner_add_left,real_inner_smul_left]
    ring
  have hg : (fun j => ⟪(ε*g j)•v,v⟫_ℝ) = (fun j => (ε*⟪v,v⟫_ℝ)*g j) := by
    funext j
    simp only [real_inner_smul_left]
    ring
  rw [hr k,hi,hg] at hs
  simp only [inner_add_left,real_inner_smul_left] at hs
  rw [← hs]
  ring

theorem ordinary_realizes_of_segment (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : ProjectedMachine K N s)
    (hR : ProjectedRealizes hK hcK hneK W M)
    (q v : E) (hv : v ≠ 0) (hminus : q-v ∈ K) (hplus : q+v ∈ K) :
    RegisterMachine.Realizes N s W (ordinary M) := by
  have hs : 0 < s := by
    by_contra h
    have hs0 : s=0 := by omega
    subst s
    have hh := M.c0_e1
    simp at hh
  have hbase (k : Fin (N+1)) :
      RegisterMachine.dot (M.c k) (RegisterMachine.stateNat N s (ordinary M) ⟪q,v⟫_ℝ (fun _ => 0) k.val) = ⟪q,v⟫_ℝ := by
    have hh := readout_on_segment hK hcK hneK W M hR q v hminus hplus 0 0 (fun _ => 0)
      (by intro i; simp) k
    simpa using hh
  have hcorrect (a : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) :
      RegisterMachine.dot (M.c k) (RegisterMachine.stateNat N s (ordinary M) a g k.val) =
        RegisterMachine.target N W a g k := by
    obtain ⟨ε,hε,ht⟩ := exists_small_scale (RegisterMachine.target N W a g)
    have hh := readout_on_segment hK hcK hneK W M hR q v hminus hplus a ε g ht k
    have hb : ε*⟪v,v⟫_ℝ ≠ 0 := mul_ne_zero hε.ne' (real_inner_self_pos.mpr hv).ne'
    have ha := state_affine (ordinary M) ⟪q,v⟫_ℝ (ε*⟪v,v⟫_ℝ) a (fun _ => 0) g k.val
    simp only [zero_add] at ha
    rw [ha,dot_affine,hbase k] at hh
    exact (mul_left_cancel₀ hb) (by linarith [hh])
  refine ⟨hs,?_,?_,?_⟩
  · intro a g k
    exact hcorrect a g k.castSucc
  · intro a g
    exact hcorrect a g (Fin.last N)
  · intro a g
    rfl

theorem ordinary_realizes_of_nontrivial (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (hKn : K.Nontrivial) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : ProjectedMachine K N s) (hR : ProjectedRealizes hK hcK hneK W M) :
    RegisterMachine.Realizes N s W (ordinary M) := by
  obtain ⟨a,ha,b,hb,hab⟩ := hKn
  let q : E := (1/2 : ℝ) • (a+b)
  let v : E := (1/2 : ℝ) • (b-a)
  have hv : v ≠ 0 := by
    intro hh
    have hba : b-a=0 := (smul_eq_zero.mp hh).resolve_left (by norm_num)
    exact hab (sub_eq_zero.mp hba).symm
  have hm : q-v=a := by dsimp [q,v]; module
  have hp : q+v=b := by dsimp [q,v]; module
  exact ordinary_realizes_of_segment hK hcK hneK W M hR q v hv (hm.symm ▸ ha) (hp.symm ▸ hb)

theorem projected_cut_rank_lower_bound (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (hKn : K.Nontrivial) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : ProjectedMachine K N s) (hR : ProjectedRealizes hK hcK hneK W M)
    (k : ℕ) (hk : k ≤ N) : (RegisterMachine.H_k N k hk W).rank ≤ s :=
  RegisterMachine.necessity_rank_le_unconditional N s W k hk
    ⟨ordinary M,ordinary_realizes_of_nontrivial hK hcK hneK hKn W M hR⟩

theorem projected_memory_lower_bound (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (hKn : K.Nontrivial) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : ProjectedMachine K N s) (hR : ProjectedRealizes hK hcK hneK W M) :
    MemoryRank.CutRank.memRank N W ≤ s :=
  RegisterMachine.maxCutRank_le_registers N s W
    ⟨ordinary M,ordinary_realizes_of_nontrivial hK hcK hneK hKn W M hR⟩

end Continuation.Projected
