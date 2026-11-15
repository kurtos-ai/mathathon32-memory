module
public import Continuation.OracleTrajectory

/-! # The displayed ITEM-wf recurrence uses two persistent registers

This module formalizes the scalar schedule and the register implementation in
Appendix D of the submitted report. It proves a memory statement for the actual
displayed recurrence. It does not prove the cited minimax theorem or existence
and optimality of its selected risk coefficient.
-/

@[expose] public section
noncomputable section
namespace Submission2026.StrongConvexMemory
open Matrix RegisterMachine
open scoped BigOperators Matrix

/-- Backward construction of the pair `(a_j,b_j)`, starting at the terminal pair. -/
def backwardPair (κ η : ℝ) : ℕ → ℝ × ℝ
  | 0 => let a := Real.sqrt (κ + (1-κ)*η)
         (a, Real.sqrt (1-κ)*a)
  | j+1 => let p := backwardPair κ η j
           let d := 1-κ+κ*p.1
           let c := Real.sqrt ((1-p.1)*(1+d))
           (d*p.1+c*p.2, -κ*c*p.1+d*p.2)

def a (N : ℕ) (κ η : ℝ) (j : ℕ) : ℝ := (backwardPair κ η (N-j)).1

def b (N : ℕ) (κ η : ℝ) (j : ℕ) : ℝ := (backwardPair κ η (N-j)).2

def c (N : ℕ) (κ η : ℝ) (j : ℕ) : ℝ :=
  if j=1 then b N κ η 1 + Real.sqrt ((1-κ)*η)
  else Real.sqrt ((1-a N κ η j)*(1+(1-κ+κ*a N κ η j)))

def p (N : ℕ) (κ η : ℝ) (k : ℕ) : ℝ :=
  if k<N then a N κ η (k+1)/((1-κ)*(1-a N κ η (k+1))) else 0

def alpha (N : ℕ) (κ η : ℝ) (k : Fin N) : ℝ := c N κ η (k.val+1)/b N κ η (k.val+1)

def t (N : ℕ) (κ η : ℝ) (k : Fin N) : ℝ :=
  alpha N κ η k * κ * p N κ η k.val / (1+p N κ η k.val)

def u (N : ℕ) (κ η : ℝ) (k : Fin N) : ℝ :=
  (1+p N κ η (k.val+1))*(1-a N κ η (k.val+1))

@[simp] theorem a_terminal (N : ℕ) (κ η : ℝ) :
    a N κ η N = Real.sqrt (κ+(1-κ)*η) := by simp [a,backwardPair]

@[simp] theorem b_terminal (N : ℕ) (κ η : ℝ) :
    b N κ η N = Real.sqrt (1-κ)*a N κ η N := by simp [a,b,backwardPair]

@[simp] theorem p_terminal (N : ℕ) (κ η : ℝ) : p N κ η N = 0 := by simp [p]

/-- The backward recursion is exactly the displayed pair of coefficient equations. -/
theorem backward_pair_step (N : ℕ) (κ η : ℝ) (j : ℕ) (hj : 2 ≤ j) (hjN : j ≤ N) :
    (a N κ η (j-1), b N κ η (j-1)) =
      ((1-κ+κ*a N κ η j)*a N κ η j + c N κ η j*b N κ η j,
       -κ*c N κ η j*a N κ η j + (1-κ+κ*a N κ η j)*b N κ η j) := by
  have hn : N-(j-1) = (N-j)+1 := by omega
  have hj1 : j ≠ 1 := by omega
  simp [a,b,c,hn,backwardPair,hj1]

@[simp] theorem c_one (N : ℕ) (κ η : ℝ) :
    c N κ η 1 = b N κ η 1 + Real.sqrt ((1-κ)*η) := by simp [c]

theorem p_before_terminal (N : ℕ) (κ η : ℝ) (k : ℕ) (hk : k < N) :
    p N κ η k = a N κ η (k+1)/((1-κ)*(1-a N κ η (k+1))) := by simp [p,hk]

/-- Eliminating the cited algorithm's `z` state from its current query. -/
theorem query_shift_identity (p y z v : ℝ) (hp : 1+p ≠ 0)
    (hy : y = (1+p)*z-p*v) :
    y-z = p/(1+p)*(y-v) := by
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hp).mpr
  nlinarith [hy]

/-- Substitution into the original `v` update gives the displayed first update. -/
theorem original_v_update (L κ α p y z v g : ℝ) (hp : 1+p ≠ 0)
    (hy : y = (1+p)*z-p*v) :
    v-α*(g/L-κ*(y-z)) =
      (α*κ*p/(1+p))*y + (1-α*κ*p/(1+p))*v - α/L*g := by
  rw [query_shift_identity p y z v hp hy]
  simp only [div_eq_mul_inv]
  ring

/-- Substitution into the next query gives the displayed second update. -/
theorem original_next_query (L a pNext y v g : ℝ) :
    (1+pNext)*((1-a)*(y-g/L)+a*v)-pNext*v =
      ((1+pNext)*(1-a))*(y-1/L*g)+(1-(1+pNext)*(1-a))*v := by
  simp only [div_eq_mul_inv]
  ring

/-- The displayed equation selecting the candidate risk coefficient; not an assumed theorem. -/
def RiskEquation (N : ℕ) (κ η : ℝ) : Prop :=
  a N κ η 1 + η + Real.sqrt (η/(1-κ))*b N κ η 1 = 1

section GenericRecurrence
variable {N : ℕ} (L : ℝ) (α τ υ : Fin N → ℝ)

/-- Coordinates are exactly `(y_k, v_{k-1}-y_k)`, so initialization is `(x0,0)`. -/
def machine : Machine N 2 where
  F k := !![1, (1-υ k)*(1-τ k); 0, υ k*(1-τ k)]
  b k := ![-(υ k+(1-υ k)*α k)/L, υ k*(1-α k)/L]
  c _ := ![1,0]
  o := ![1,0]

/-- The original two-state update, before the change of register coordinates. -/
def step (k : Fin N) (y v g : ℝ) : ℝ × ℝ :=
  let v' := τ k*y+(1-τ k)*v-α k/L*g
  (υ k*(y-1/L*g)+(1-υ k)*v',v')

/-- The explicit matrix is the exact change of coordinates of the displayed recurrence. -/
theorem machine_step (k : Fin N) (y v g : ℝ) :
    (machine L α τ υ).F k *ᵥ ![y,v-y] + g • (machine L α τ υ).b k =
      ![(step L α τ υ k y v g).1,
        (step L α τ υ k y v g).2-(step L α τ υ k y v g).1] := by
  ext i
  fin_cases i <;> simp [machine, step] <;> ring

/-- Run the actual displayed `(y,v)` recurrence on arbitrary formal oracle inputs. -/
def trajectory (x0 : ℝ) (g : Fin N → ℝ) : ℕ → ℝ × ℝ
  | 0 => (x0,x0)
  | k+1 => if h : k<N then
      step L α τ υ ⟨k,h⟩ (trajectory x0 g k).1 (trajectory x0 g k).2 (g ⟨k,h⟩)
    else trajectory x0 g k

theorem stateNat_trajectory (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) :
    stateNat N 2 (machine L α τ υ) x0 g k =
      ![(trajectory L α τ υ x0 g k).1,
        (trajectory L α τ υ x0 g k).2-(trajectory L α τ υ x0 g k).1] := by
  induction k with
  | zero => ext i; fin_cases i <;> simp [stateNat,trajectory,e1]
  | succ k ih =>
    by_cases hk : k<N
    · rw [stateNat_succ N 2 _ _ _ k hk, ih]
      have h := machine_step L α τ υ ⟨k,hk⟩
        (trajectory L α τ υ x0 g k).1 (trajectory L α τ υ x0 g k).2 (g ⟨k,hk⟩)
      ext r
      have hr := congrFun h r
      simpa only [trajectory,hk,dite_true,Matrix.mulVec, dotProduct,Pi.add_apply,
        Pi.smul_apply,smul_eq_mul,mul_comm] using hr
    · simp only [stateNat,trajectory,hk,dite_false,ih]

/-- With no consumed oracle input, the initial-point coefficient remains `(1,0)`. -/
theorem psi_initial (k : ℕ) (hk : k≤N) (r : Fin 2) :
    psi N 2 (machine L α τ υ) k hk r 0 = e1 2 r := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h0 : (0 : Fin (k+2)) = Fin.castSucc (0 : Fin (k+1)) := rfl
    rw [h0,psi_castSucc]
    change (∑ j : Fin 2, (!![1, (1-υ ⟨k,by omega⟩)*(1-τ ⟨k,by omega⟩);
      0, υ ⟨k,by omega⟩*(1-τ ⟨k,by omega⟩)] : Matrix (Fin 2) (Fin 2) ℝ) r j *
      psi N 2 (machine L α τ υ) k (by omega) j 0) = e1 2 r
    fin_cases r <;> simp [e1,ih]

/-- The full strict-history coefficient table of this predetermined recurrence. -/
def history : Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i j =>
  if h : j.val < i.val then psi N 2 (machine L α τ υ) i.val (by omega) 0
    ⟨j.val+1,by omega⟩ else 0

@[simp] theorem history_causal (i j : Fin (N+1)) (h : i.val≤j.val) :
    history L α τ υ i j = 0 := by simp [history,show ¬j.val < i.val by omega]

theorem target_state (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) :
    target N (history L α τ υ) x0 g k = stateNat N 2 (machine L α τ υ) x0 g k.val 0 := by
  have hs := congrFun (psi_mulVec_state N 2 (machine L α τ υ) x0 g k.val (by omega)) 0
  rw [← hs]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, psi_initial,
    e1, Fin.val_zero, ite_true, inputVec_zero, one_mul, inputVec_succ, target]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [history,j.isLt,dite_true]
  rfl

/-- The strict-history table describes the actual displayed trajectory. -/
theorem target_trajectory (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) :
    target N (history L α τ υ) x0 g k = (trajectory L α τ υ x0 g k.val).1 := by
  rw [target_state, stateNat_trajectory]
  rfl

theorem realizes : Realizes N 2 (history L α τ υ) (machine L α τ υ) := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro x0 g k
    rw [target_state]
    simp [machine,dot,Fin.sum_univ_two,stateFin]
  · intro x0 g
    rw [target_state]
    simp [machine,dot,Fin.sum_univ_two,stateFin]
  · intro x0 g
    rfl

theorem vectorRealizes : VectorRealizes N 2 (history L α τ υ) (machine L α τ υ) :=
  (vectorRealizes_iff_scalar N 2 _ _).mpr (realizes L α τ υ)

theorem cut_rank_le_two (k : ℕ) (hk : k≤N) :
    (RegisterMachine.H_k N k hk (history L α τ υ)).rank ≤ 2 :=
  necessity_rank_le_unconditional N 2 _ k hk ⟨machine L α τ υ,realizes L α τ υ⟩

theorem memory_le_two : MemoryRank.CutRank.memRank N (history L α τ υ) ≤ 2 :=
  maxCutRank_le_registers N 2 _ ⟨machine L α τ υ,realizes L α τ υ⟩
end GenericRecurrence

/-- The concrete ITEM-wf schedule, with its candidate risk parameter fixed before execution. -/
def itemMachine (N : ℕ) (L κ η : ℝ) : Machine N 2 :=
  machine L (alpha N κ η) (t N κ η) (u N κ η)

def itemHistory (N : ℕ) (L κ η : ℝ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  history L (alpha N κ η) (t N κ η) (u N κ η)

theorem item_realizes (N : ℕ) (L κ η : ℝ) :
    Realizes N 2 (itemHistory N L κ η) (itemMachine N L κ η) :=
  realizes L (alpha N κ η) (t N κ η) (u N κ η)

theorem item_vectorRealizes (N : ℕ) (L κ η : ℝ) :
    VectorRealizes N 2 (itemHistory N L κ η) (itemMachine N L κ η) :=
  vectorRealizes L (alpha N κ η) (t N κ η) (u N κ η)

theorem item_cut_rank_le_two (N : ℕ) (L κ η : ℝ) (k : ℕ) (hk : k≤N) :
    (RegisterMachine.H_k N k hk (itemHistory N L κ η)).rank ≤ 2 :=
  cut_rank_le_two L (alpha N κ η) (t N κ η) (u N κ η) k hk

theorem item_memory_le_two (N : ℕ) (L κ η : ℝ) :
    MemoryRank.CutRank.memRank N (itemHistory N L κ η) ≤ 2 :=
  memory_le_two L (alpha N κ η) (t N κ η) (u N κ η)

/-- Exact trajectory bridge for the explicitly instantiated ITEM-wf coefficients. -/
theorem item_history_trajectory (N : ℕ) (L κ η x0 : ℝ) (g : Fin N → ℝ)
    (k : Fin (N+1)) :
    target N (itemHistory N L κ η) x0 g k =
      (trajectory L (alpha N κ η) (t N κ η) (u N κ η) x0 g k.val).1 :=
  target_trajectory L (alpha N κ η) (t N κ η) (u N κ η) x0 g k

/-- One query needs at most one total register, hence no auxiliary vector. -/
theorem item_one_query_memory (L κ η : ℝ) :
    MemoryRank.CutRank.memRank 1 (itemHistory 1 L κ η) ≤ 1 := by
  simpa using MemoryRank.CutRank.memRank_le 1 (itemHistory 1 L κ η)

theorem item_one_query_realizable (L κ η : ℝ) :
    HasVectorRealization 1 (itemHistory 1 L κ η) 1 :=
  (vectorRealization_iff_maxCutRank 1 _ 1).mpr (item_one_query_memory L κ η)

theorem item_executes_oracle (N : ℕ) (L κ η : ℝ) {d : ℕ}
    (G : (Fin d → ℝ) → (Fin d → ℝ)) (x0 : Fin d → ℝ) :
    let W := itemHistory N L κ η
    let M := itemMachine N L κ η
    let g := fun j : Fin N => G (OracleTrajectory.run W G x0 j.castSucc)
    (∀ k : Fin N, vectorReadout (M.c k) (vectorStateNat M x0 g k.val) =
      OracleTrajectory.run W G x0 k.castSucc) ∧
    vectorReadout M.o (vectorStateNat M x0 g N) = OracleTrajectory.run W G x0 (Fin.last N) :=
  OracleTrajectory.realization_executes_oracle _ _ (item_vectorRealizes N L κ η) G x0

#print axioms backward_pair_step
#print axioms stateNat_trajectory
#print axioms item_history_trajectory
#print axioms item_one_query_realizable
#print axioms item_realizes
#print axioms item_vectorRealizes
#print axioms item_memory_le_two
#print axioms item_executes_oracle
end Submission2026.StrongConvexMemory
