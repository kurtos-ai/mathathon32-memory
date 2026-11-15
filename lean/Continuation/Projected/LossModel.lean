module
public import Continuation.Projected.Recurrence
public import Continuation.Projected.ConvexInterpolation
@[expose] public section

open Set
open scoped InnerProductSpace
noncomputable section

namespace ProjectedLossModel
open Continuation.ProjectedSupport FiniteConvexInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Objective values outside K are irrelevant. B specifies permitted oracle returns. -/
structure Instance (K B : Set E) (R : ℝ) where
  f : E → ℝ
  convex : ConvexOn ℝ K f
  subgrad : ∀ x ∈ K, ∃ g ∈ B, RelativeSubgradient K f x g
  x0 : E
  xStar : E
  hx0 : x0 ∈ K
  hxStar : xStar ∈ K
  isMin : IsMinOn f K xStar
  near : ‖x0-xStar‖ ≤ R

variable {N : ℕ} {K B : Set E} {R : ℝ}
variable (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)

def pre (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x g : Fin (N+1) → E) (k : Fin N) : E :=
  x k.castSucc + W k.succ k.castSucc • g k.castSucc +
    ∑ j : Fin k.val, (W k.succ ⟨j.val,by omega⟩ - W k.castSucc ⟨j.val,by omega⟩) •
      g ⟨j.val,by omega⟩

def site (xStar : E) (x : Fin (N+1) → E) : Option (Fin (N+1)) → E
  | none => xStar
  | some i => x i

def slope (g : Fin (N+1) → E) : Option (Fin (N+1)) → E
  | none => 0
  | some i => g i

def val (φ : Fin (N+1) → ℝ) : Option (Fin (N+1)) → ℝ
  | none => 0
  | some i => φ i

/-- Exact finite conditions; projection is expressed by its variational graph. -/
def Feasible (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (K B : Set E) (R : ℝ)
    (xStar : E) (x g : Fin (N+1) → E) (φ : Fin (N+1) → ℝ) : Prop :=
  xStar ∈ K ∧ (∀ i, x i ∈ K) ∧ ‖x 0-xStar‖^2 ≤ R^2 ∧ (∀ i, g i ∈ B) ∧
  (∀ i j : Option (Fin (N+1)), val φ i + ⟪slope g i,site xStar x j-site xStar x i⟫_ℝ ≤ val φ j) ∧
  ∀ k : Fin N, ProjRelation K (pre W x g k) (x k.succ)

def Admissible (I : Instance K B R) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : Fin N → E) : Prop := ∀ k : Fin N, g k ∈ B ∧
      RelativeSubgradient K I.f (directStateAux hK hcK hneK W I.x0 g k.val) (g k)

def terminalLoss (I : Instance K B R) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : Fin N → E) : ℝ := I.f (directStateAux hK hcK hneK W I.x0 g N) - I.f I.xStar

theorem direct_mem (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : E) (hx0 : x0 ∈ K)
    (g : Fin N → E) (k : ℕ) (hk : k ≤ N) :
    directStateAux hK hcK hneK W x0 g k ∈ K := by
  cases k with
  | zero => exact hx0
  | succ k =>
    have hkN : k < N := by omega
    simp only [directStateAux, dite_eq_left hkN]
    exact piK_mem hK hcK hneK _

theorem trajectory_of_feasible (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (xStar : E) (x g : Fin (N+1) → E) (φ : Fin (N+1) → ℝ)
    (hF : Feasible W K B R xStar x g φ) :
    ∀ k : ℕ, ∀ hk : k ≤ N,
      directStateAux hK hcK hneK W (x 0) (fun j => g j.castSucc) k = x ⟨k,by omega⟩ := by
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    rw [directStateAux, dite_eq_left hkN, ih (by omega)]
    have hp := (proj_graph_correct hK hcK hneK).mp (hF.2.2.2.2.2 ⟨k,hkN⟩)
    simpa only [pre, Fin.val_mk, Fin.castSucc_mk, Fin.succ_mk, add_assoc] using hp.symm

/-- Every finite feasible data set is attained by a genuine convex objective and oracle choices. -/
theorem realize_feasible (hB0 : (0:E) ∈ B) (hR : 0 ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (xStar : E) (x g : Fin (N+1) → E) (φ : Fin (N+1) → ℝ)
    (hF : Feasible W K B R xStar x g φ) :
    ∃ I : Instance K B R, ∃ grad : Fin N → E,
      Admissible hK hcK hneK I W grad ∧ terminalLoss hK hcK hneK I W grad = φ (Fin.last N) := by
  let f := envelope (site xStar x) (slope g) (val φ)
  have hsub (i : Option (Fin (N+1))) :
      RelativeSubgradient K f (site xStar x i) (slope g i) := by
    intro y _
    exact envelope_data_subgradient _ _ _ hF.2.2.2.2.1 i y (mem_univ y)
  have hvalue (i : Option (Fin (N+1))) : f (site xStar x i) = val φ i :=
    envelope_at_site _ _ _ hF.2.2.2.2.1 i
  have hmin : IsMinOn f K xStar := by
    intro y hy
    change f xStar ≤ f y
    simpa only [site,slope,inner_zero_left,add_zero] using hsub none y hy
  have hnear : ‖x 0-xStar‖ ≤ R := by nlinarith [hF.2.2.1,norm_nonneg (x 0-xStar)]
  let I : Instance K B R := {
    f := f
    convex := ⟨hK,fun u _ v _ a b ha hb hab =>
      (envelope_convex (site xStar x) (slope g) (val φ)).2 (mem_univ u) (mem_univ v) ha hb hab⟩
    subgrad := by
      intro u hu
      obtain ⟨i,hi⟩ := envelope_subgradient_everywhere (site xStar x) (slope g) (val φ) u
      refine ⟨slope g i,?_,fun y _ => hi y (mem_univ y)⟩
      cases i with
      | none => exact hB0
      | some i => exact hF.2.2.2.1 i
    x0 := x 0
    xStar := xStar
    hx0 := hF.2.1 0
    hxStar := hF.1
    isMin := hmin
    near := hnear }
  refine ⟨I,fun j => g j.castSucc,?_,?_⟩
  · intro k
    refine ⟨hF.2.2.2.1 k.castSucc,?_⟩
    change RelativeSubgradient K f
      (directStateAux hK hcK hneK W (x 0) (fun j => g j.castSucc) k.val) (g k.castSucc)
    rw [trajectory_of_feasible hK hcK hneK W xStar x g φ hF k.val (by omega)]
    exact hsub (some k.castSucc)
  · change f (directStateAux hK hcK hneK W (x 0) (fun j => g j.castSucc) N) - f xStar = _
    rw [trajectory_of_feasible hK hcK hneK W xStar x g φ hF N (le_refl N)]
    have hN : f (x (Fin.last N)) = φ (Fin.last N) := hvalue (some (Fin.last N))
    have hs : f xStar = 0 := hvalue none
    change f (x (Fin.last N))-f xStar = _
    rw [hN,hs,sub_zero]

/-- Actual oracle executions supply all finite inequalities; the terminal slope is auxiliary. -/
theorem actual_feasible (I : Instance K B R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (g : Fin N → E)
    (hadm : Admissible hK hcK hneK I W g) :
    ∃ x grad φ, Feasible W K B R I.xStar x grad φ ∧
      φ (Fin.last N) = terminalLoss hK hcK hneK I W g := by
  let x : Fin (N+1) → E := fun i => directStateAux hK hcK hneK W I.x0 g i.val
  have hx (i : Fin (N+1)) : x i ∈ K := direct_mem hK hcK hneK W I.x0 I.hx0 g i.val (by omega)
  obtain ⟨gN,hgN,hsubN⟩ := I.subgrad (x (Fin.last N)) (hx (Fin.last N))
  let grad : Fin (N+1) → E := Fin.lastCases gN g
  let φ : Fin (N+1) → ℝ := fun i => I.f (x i)-I.f I.xStar
  have hgrad (k : Fin N) : grad k.castSucc = g k := by simp [grad]
  have hdata (i : Fin (N+1)) : grad i ∈ B ∧ RelativeSubgradient K I.f (x i) (grad i) := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa only [grad,Fin.lastCases_last] using And.intro hgN hsubN
    · simpa only [hgrad,x,Fin.val_castSucc] using hadm k
  have hsite (i : Option (Fin (N+1))) : site I.xStar x i ∈ K := by
    cases i with
    | none => exact I.hxStar
    | some i => exact hx i
  have hsub (i : Option (Fin (N+1))) :
      RelativeSubgradient K I.f (site I.xStar x i) (slope grad i) := by
    cases i with
    | none =>
        intro y hy
        have hm : I.f I.xStar ≤ I.f y := I.isMin hy
        simpa only [site,slope,inner_zero_left,add_zero] using hm
    | some i => exact (hdata i).2
  have hval (i : Option (Fin (N+1))) :
      val φ i = I.f (site I.xStar x i)-I.f I.xStar := by
    cases i <;> simp [val,site,φ]
  refine ⟨x,grad,φ,?_,rfl⟩
  refine ⟨I.hxStar,hx,?_,fun i => (hdata i).1,?_,?_⟩
  · have hn := I.near
    change ‖I.x0-I.xStar‖^2 ≤ R^2
    nlinarith [norm_nonneg (I.x0-I.xStar)]
  · intro i j
    rw [hval i,hval j]
    have hs := hsub i (site I.xStar x j) (hsite j)
    linarith
  · intro k
    apply (proj_graph_correct hK hcK hneK).mpr
    change directStateAux hK hcK hneK W I.x0 g (k.val+1) = _
    rw [directStateAux,dite_eq_left k.isLt]
    apply congrArg (piK hK hcK hneK)
    simp only [pre,x,hgrad,Fin.val_castSucc,add_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    have hg : grad ⟨j.val,by omega⟩ = g ⟨j.val,by omega⟩ := hgrad ⟨j.val,by omega⟩
    rw [hg]
    rfl

def actualLossSet (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (R : ℝ) : Set ℝ :=
  {z | ∃ I : Instance K B R, ∃ g : Fin N → E,
    Admissible hK hcK hneK I W g ∧ z = terminalLoss hK hcK hneK I W g}

def modelLossSet (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (K B : Set E) (R : ℝ) : Set ℝ :=
  {z | ∃ xStar x g φ, Feasible W K B R xStar x g φ ∧ z = φ (Fin.last N)}

theorem lossSet_eq (hB0 : (0:E) ∈ B) (hR : 0 ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    actualLossSet (B:=B) hK hcK hneK W R = modelLossSet W K B R := by
  apply Set.Subset.antisymm
  · rintro z ⟨I,g,hadm,rfl⟩
    obtain ⟨x,grad,φ,hF,hval⟩ := actual_feasible hK hcK hneK I W g hadm
    exact ⟨I.xStar,x,grad,φ,hF,hval.symm⟩
  · rintro z ⟨xStar,x,g,φ,hF,rfl⟩
    obtain ⟨I,grad,hadm,hloss⟩ := realize_feasible hK hcK hneK hB0 hR W xStar x g φ hF
    exact ⟨I,grad,hadm,hloss.symm⟩

/-- A zero-increment method stays at its feasible initial point, including N=0. -/
theorem direct_zero (x0 : E) (hx0 : x0 ∈ K) (g : Fin N → E) (k : ℕ) (hk : k ≤ N) :
    directStateAux hK hcK hneK (0 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) x0 g k = x0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkN : k < N := by omega
    simp only [directStateAux,dite_eq_left hkN,ih (by omega),Matrix.zero_apply,
      sub_zero,zero_smul,Finset.sum_const_zero,add_zero]
    exact piK_of_mem hK hcK hneK hx0

theorem bounded_zero_loss {M : ℝ} (I : Instance K (Metric.closedBall (0:E) M) R)
    (g : Fin N → E) :
    terminalLoss hK hcK hneK I (0 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) g ≤ M*R := by
  rw [terminalLoss,direct_zero hK hcK hneK I.x0 I.hx0 g N (le_refl N)]
  obtain ⟨v,hv,hsub⟩ := I.subgrad I.x0 I.hx0
  have hvn : ‖v‖ ≤ M := by simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero] using hv
  have hs := hsub I.xStar I.hxStar
  have hinner : ⟪v,I.xStar-I.x0⟫_ℝ = -⟪v,I.x0-I.xStar⟫_ℝ := by
    rw [← inner_neg_right]
    congr 1
    abel
  rw [hinner] at hs
  have hi := real_inner_le_norm v (I.x0-I.xStar)
  have hm := mul_le_mul hvn I.near (norm_nonneg (I.x0-I.xStar)) ((norm_nonneg v).trans hvn)
  linarith

theorem bounded_lossSet_eq {M : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    actualLossSet (B:=Metric.closedBall (0:E) M) hK hcK hneK W R =
      modelLossSet W K (Metric.closedBall (0:E) M) R :=
  lossSet_eq hK hcK hneK (Metric.mem_closedBall_self hM) hR W

theorem unbounded_lossSet_eq (hR : 0 ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    actualLossSet (B:=Set.univ) hK hcK hneK W R = modelLossSet W K Set.univ R :=
  lossSet_eq hK hcK hneK (Set.mem_univ 0) hR W

end ProjectedLossModel
