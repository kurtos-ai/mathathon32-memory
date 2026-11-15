module
public import Continuation.Projected.LowerBound
public import Continuation.Projected.Singleton
public import Continuation.Normalization.Core
public import RealizationCore.MemoryCharacterization
/-! Projection preserves the least register count on every nontrivial closed
convex domain. The construction uses one scalar coefficient machine in every
finite-dimensional real inner-product space, with the full query trajectory
proved by an explicit vector-state invariant. Singleton domains need one register. -/
@[expose] public section

open Set
open scoped InnerProductSpace
noncomputable section
namespace Continuation.Projected
open Continuation.ProjectedSupport
open RegisterMachine
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {N s : ℕ} {K : Set E}

def readCoeffs (M : Machine N s) : Fin (N+1) → Fin s → ℝ := Fin.lastCases M.o M.c

theorem read_scalar (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s)
    (hR : Realizes N s W M) (a : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) :
    dot (readCoeffs M k) (stateNat N s M a g k.val) = target N W a g k := by
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [readCoeffs,Fin.lastCases_last,Fin.val_last]
    change dot M.o (stateNat N s M a g N) = target N W a g ⟨N,by omega⟩
    exact hR.2.2.1 a g
  · simp only [readCoeffs,Fin.lastCases_castSucc,Fin.val_castSucc]
    change dot (M.c i) (stateNat N s M a g i.val) = target N W a g ⟨i.val,by omega⟩
    exact hR.2.1 a g i

theorem read_q (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s)
    (hR : Realizes N s W M) (k : Fin (N+1)) : dot (readCoeffs M k) (qFin N s M k)=1 := by
  simpa only [qFin,stateFin,target_zero_grad] using read_scalar W M hR 1 (fun _ => 0) k

def vectorState (M : Machine N s) (x0 : E) (g : Fin N → E) : ℕ → Fin s → E
  | 0 => fun r => e1 s r • x0
  | n+1 => if h : n<N then
    fun r => (∑ j : Fin s, M.F ⟨n,h⟩ r j • vectorState M x0 g n j)+M.b ⟨n,h⟩ r • g ⟨n,h⟩
    else vectorState M x0 g n

def vectorHistory (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : E) (g : Fin N → E) (k : Fin (N+1)) : E :=
  x0+∑ j : Fin k.val, W k ⟨j.val,by omega⟩ • g ⟨j.val,by omega⟩

theorem vectorState_inner (M : Machine N s) (x0 v : E) (g : Fin N → E) (n : ℕ) (r : Fin s) :
    ⟪vectorState M x0 g n r,v⟫_ℝ = stateNat N s M ⟪x0,v⟫_ℝ (fun j => ⟪g j,v⟫_ℝ) n r := by
  induction n generalizing r with
  | zero => simp only [vectorState,stateNat,real_inner_smul_left]
  | succ n ih =>
    by_cases hn : n<N
    · simp only [vectorState,stateNat,dite_eq_left hn,inner_add_left,sum_inner,real_inner_smul_left]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]
    · simp only [vectorState,stateNat,dite_eq_right hn,ih]

theorem read_vector (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s)
    (hR : Realizes N s W M) (x0 : E) (g : Fin N → E) (k : Fin (N+1)) :
    weightedSum (readCoeffs M k) (vectorState M x0 g k.val) = vectorHistory W x0 g k := by
  apply ext_inner_right ℝ
  intro v
  simp only [weightedSum,sum_inner,real_inner_smul_left,vectorHistory,inner_add_left]
  simp only [vectorState_inner]
  exact read_scalar W M hR ⟪x0,v⟫_ℝ (fun j => ⟪g j,v⟫_ℝ) k

def projectedLift (K : Set E) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Machine N s) (hR : Realizes N s W M) : ProjectedMachine K N s where
  F := M.F
  b := M.b
  c := readCoeffs M
  p := fun k => qFin N s M k.succ
  c0_e1 := by
    have hh := read_q W M hR ⟨0,by omega⟩
    rw [qFin_zero_eq_e1] at hh
    exact hh
  cp_one := fun k => read_q W M hR k.succ

theorem weightedSum_shift (c q : Fin s → ℝ) (z : Fin s → E) (u : E) :
    weightedSum c (fun r => z r+q r•u) = weightedSum c z+(dot c q)•u := by
  simp only [weightedSum,smul_add,smul_smul,Finset.sum_add_distrib,dot,Finset.sum_smul]

theorem vectorHistory_succ (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x0 : E) (g : Fin N → E) (k : Fin N) :
    vectorHistory W x0 g k.succ = vectorHistory W x0 g k.castSucc +
      W k.succ k.castSucc • g k +
      ∑ j : Fin k.val, (W k.succ ⟨j.val,by omega⟩-W k.castSucc ⟨j.val,by omega⟩) • g ⟨j.val,by omega⟩ := by
  unfold vectorHistory
  simp only [Fin.val_succ,Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,sub_smul,Finset.sum_sub_distrib]
  change x0 + (_ + W k.succ k.castSucc • g k) = _
  abel

theorem projectedLift_invariant (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s)
    (hR : Realizes N s W M) (x0 : E) (g : Fin N → E) :
    ∀ n : ℕ, ∀ hn : n≤N, ∀ r : Fin s,
      projStateAux hK hcK hneK (projectedLift K W M hR) x0 g n r =
        vectorState M x0 g n r+qFin N s M ⟨n,by omega⟩ r •
          (directStateAux hK hcK hneK W x0 g n-vectorHistory W x0 g ⟨n,by omega⟩) := by
  intro n
  induction n with
  | zero =>
    intro hn r
    simp [projStateAux,initState,vectorState,directStateAux,vectorHistory,e1Vec,e1]
  | succ n ih =>
    intro hn r
    have hnN : n<N := by omega
    let k : Fin N := ⟨n,hnN⟩
    let P := projectedLift K W M hR
    let e := directStateAux hK hcK hneK W x0 g n-vectorHistory W x0 g k.castSucc
    have hq (j : Fin s) :
        (∑ i : Fin s, M.F k j i*qFin N s M k.castSucc i)=qFin N s M k.succ j := by
      have hh := congrFun (F_mul_qFin N s M n hnN) j
      simpa only [Matrix.mulVec,dotProduct,k,Fin.castSucc_mk,Fin.succ_mk] using hh
    have hraw : rawState hK hcK hneK P x0 g k =
        fun j => vectorState M x0 g (n+1) j+qFin N s M k.succ j•e := by
      funext j
      change (∑ i : Fin s, M.F k j i • projStateAux hK hcK hneK P x0 g n i)+M.b k j•g k = _
      simp only [P,ih (by omega)]
      change (∑ i : Fin s, M.F k j i • (vectorState M x0 g n i+qFin N s M k.castSucc i•e))+M.b k j•g k = _
      simp only [smul_add,smul_smul,Finset.sum_add_distrib]
      rw [← Finset.sum_smul,hq]
      simp only [vectorState,dite_eq_left hnN]
      change _ = ((∑ i : Fin s, M.F k j i • vectorState M x0 g n i)+M.b k j•g k)+qFin N s M k.succ j•e
      abel
    have hrawread : weightedSum (P.c k.succ) (rawState hK hcK hneK P x0 g k) =
        vectorHistory W x0 g k.succ+e := by
      rw [hraw]
      change weightedSum (readCoeffs M k.succ) (fun j => vectorState M x0 g (n+1) j+qFin N s M k.succ j•e) = _
      rw [weightedSum_shift,read_q W M hR]
      have hh := read_vector W M hR x0 g k.succ
      change weightedSum (readCoeffs M k.succ) (vectorState M x0 g (n+1)) = _ at hh
      rw [hh,one_smul]
    have hdirect : directStateAux hK hcK hneK W x0 g (n+1) =
        piK hK hcK hneK (vectorHistory W x0 g k.succ+e) := by
      rw [directStateAux,dite_eq_left hnN]
      congr 1
      dsimp only
      rw [vectorHistory_succ W x0 g k]
      dsimp only [e,k,Fin.val_mk,Fin.castSucc_mk,Fin.succ_mk]
      abel
    have hcor : correction hK hcK hneK P x0 g k =
        directStateAux hK hcK hneK W x0 g (n+1)-(vectorHistory W x0 g k.succ+e) := by
      unfold correction
      rw [hrawread]
      dsimp only
      rw [← hdirect]
    rw [projStateAux_succ hK hcK hneK (projectedLift K W M hR) x0 g n hnN]
    change rawState hK hcK hneK P x0 g k r+qFin N s M k.succ r•correction hK hcK hneK P x0 g k = _
    rw [hraw,hcor]
    change vectorState M x0 g (n+1) r+qFin N s M k.succ r•e+
      qFin N s M k.succ r•(directStateAux hK hcK hneK W x0 g (n+1)-(vectorHistory W x0 g k.succ+e)) =
      vectorState M x0 g (n+1) r+qFin N s M k.succ r•(directStateAux hK hcK hneK W x0 g (n+1)-vectorHistory W x0 g k.succ)
    module

theorem projectedLift_realizes (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s) (hR : Realizes N s W M) :
    ProjectedRealizes hK hcK hneK W (projectedLift K W M hR) := by
  intro x0 hx0 g k
  unfold projQuery
  have hi : projStateAux hK hcK hneK (projectedLift K W M hR) x0 g k.val =
      fun r => vectorState M x0 g k.val r+qFin N s M k r•
        (directStateAux hK hcK hneK W x0 g k.val-vectorHistory W x0 g k) := by
    funext r
    exact projectedLift_invariant hK hcK hneK W M hR x0 g k.val (by omega) r
  rw [hi]
  change weightedSum (readCoeffs M k) _ = _
  rw [weightedSum_shift,read_vector W M hR,read_q W M hR,one_smul]
  abel

def HasProjectedRealization (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) : Prop :=
  ∃ P : ProjectedMachine K N s, ProjectedRealizes hK hcK hneK W P

theorem projected_realization_of_rank (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ)
    (hr : MemoryRank.CutRank.memRank N W ≤ s) : HasProjectedRealization hK hcK hneK W s := by
  obtain ⟨M,hM⟩ := (RegisterMachine.realization_iff_maxCutRank N W s).mpr hr
  exact ⟨projectedLift K W M hM,projectedLift_realizes hK hcK hneK W M hM⟩

theorem projected_realization_iff_rank (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (hKn : K.Nontrivial) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) :
    HasProjectedRealization hK hcK hneK W s ↔ MemoryRank.CutRank.memRank N W ≤ s := by
  constructor
  · rintro ⟨P,hP⟩
    exact projected_memory_lower_bound hK hcK hneK hKn W P hP
  · exact projected_realization_of_rank hK hcK hneK W s

theorem projected_least_registers (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (hKn : K.Nontrivial) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    IsLeast {s : ℕ | HasProjectedRealization hK hcK hneK W s} (MemoryRank.CutRank.memRank N W) := by
  exact ⟨projected_realization_of_rank hK hcK hneK W _ le_rfl,
    fun _ hs => (projected_realization_iff_rank hK hcK hneK hKn W _).mp hs⟩

theorem projected_realization_iff_ordinary (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (hKn : K.Nontrivial) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) :
    HasProjectedRealization hK hcK hneK W s ↔ HasRealization N W s :=
  (projected_realization_iff_rank hK hcK hneK hKn W s).trans
    (RegisterMachine.realization_iff_maxCutRank N W s).symm

def oneProjected (K : Set E) (N : ℕ) : ProjectedMachine K N 1 where
  F := fun _ => 0
  b := fun _ => 0
  c := fun _ _ => 1
  p := fun _ _ => 1
  c0_e1 := by simp [Fin.sum_univ_one]
  cp_one := by intro k; simp [Fin.sum_univ_one]

theorem projectedMachine_positive (M : ProjectedMachine K N s) : 0<s := by
  by_contra h
  have hs : s=0 := by omega
  subst s
  have hh := M.c0_e1
  simp at hh

theorem singleton_realization (a : E) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    HasProjectedRealization (convex_singleton a) isClosed_singleton ⟨a,rfl⟩ W 1 := by
  refine ⟨oneProjected {a} N,?_⟩
  intro x0 hx0 g k
  have hx : x0=a := hx0
  rw [proj_singleton_a N 1 (oneProjected {a} N) x0 hx g k.val (by omega),
    direct_singleton_a N W x0 hx g k.val]

theorem subsingleton_least_registers (hK : Convex ℝ K) (hcK : IsClosed K) (hneK : K.Nonempty)
    (hKs : K.Subsingleton) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    IsLeast {s : ℕ | HasProjectedRealization hK hcK hneK W s} 1 := by
  constructor
  · obtain ⟨a,ha⟩ := hneK
    have heq : K={a} := by
      ext x
      constructor
      · intro hx
        exact hKs hx ha
      · intro hx
        have hh : x=a := hx
        simpa only [hh] using ha
    subst K
    exact singleton_realization a W
  · rintro s ⟨P,hP⟩
    exact projectedMachine_positive P

end Continuation.Projected
