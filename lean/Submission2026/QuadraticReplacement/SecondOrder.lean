module
public import Submission2026.QuadraticReplacement.FactorSteps
public import Continuation.Quadratic.MatrixResidual
@[expose] public section
noncomputable section
namespace QuadraticReplacement
open Polynomial Matrix

def subdiagonal (N : ℕ) (t : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i.val=j.val+1 then t i else 0

lemma subdiagonal_strict (N : ℕ) (t : Fin N → ℝ) :
    ∀ i j,i.val  ≤  j.val → subdiagonal N t i j=0 := by
  intro i j hij
  simp [subdiagonal,show i.val ≠ j.val+1 by omega]

/-- An arbitrary second-order recurrence has at most one auxiliary register in the exact cut model. -/
lemma subdiagonal_memory (N : ℕ) (t : Fin N → ℝ) :
    MemoryRank.Incremental.Q N 1 (subdiagonal N t) := by
  intro k hk hkN
  let u : Fin (N-k) → ℝ := fun i => if i.val=0 then t ⟨k+i.val,by omega⟩ else 0
  let v : Fin k → ℝ := fun j => if j.val+1=k then 1 else 0
  have he : MemoryRank.Incremental.S_k N k (subdiagonal N t)=Matrix.vecMulVec u v := by
    ext i j
    by_cases hi : i.val=0  <;> by_cases hj : j.val+1=k  <;>
      simp [MemoryRank.Incremental.S_k,show k  ≤  N by omega,subdiagonal,
        Matrix.vecMulVec_apply,u,v,hi,hj,eq_comm,show (k+i.val=j.val+1) ↔ (i.val=0 ∧ j.val+1=k) by omega]
  rw [he]
  have h := Matrix.rank_vecMulVec_le (R:=ℝ) u v
  omega

lemma subdiagonal_sum (N : ℕ) (d t : Fin N → ℝ) (k : ℕ) (hk : k < N) :
    (∑ j : Fin k,C (subdiagonal N t ⟨k,hk⟩ ⟨j.val,by omega⟩)*
      QuadraticFoundations.pIter N d (subdiagonal N t) j.val) =
    if k=0 then 0 else C (t ⟨k,hk⟩)*QuadraticFoundations.pIter N d (subdiagonal N t) (k-1) := by
  by_cases hk0 : k=0
  · subst k
    simp
  · let j0 : Fin k := ⟨k-1,by omega⟩
    rw [Finset.sum_eq_single j0]
    · simp only [subdiagonal,j0,Fin.val_mk,if_neg hk0,
        if_pos (show k=k-1+1 by omega)]
    · intro j hj hj0
      have hne : k ≠ j.val+1 := by
        intro he
        apply hj0
        apply Fin.ext
        dsimp [j0]
        omega
      simp [subdiagonal,hne]
    · simp

def polynomialState (N : ℕ) (d t : Fin N → ℝ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (0,1)
  | k+1 => if h : k < N then stepPolynomial (d ⟨k,h⟩,t ⟨k,h⟩) (polynomialState N d t k)
      else (0,1)

lemma polynomialState_eq (N : ℕ) (d t : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    polynomialState N d t k =
      (if k=0 then 0 else QuadraticFoundations.pIter N d (subdiagonal N t) (k-1),
       QuadraticFoundations.pIter N d (subdiagonal N t) k) := by
  induction k with
  | zero => simp [polynomialState,QuadraticFoundations.pIter]
  | succ k ih =>
    have hkN : k < N := by omega
    rw [polynomialState,dite_eq_left hkN,ih (by omega)]
    apply Prod.ext
    · simp [stepPolynomial]
    · simp only [stepPolynomial]
      rw [QuadraticFoundations.pIter,dite_eq_left hkN,subdiagonal_sum]
      by_cases hk0 : k=0  <;> simp [hk0]  <;> ring

lemma polynomialState_eq_run (N : ℕ) (d t : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    polynomialState N d t k = runPolynomial
      (List.ofFn (fun i : Fin k => (d ⟨i.val,by omega⟩,t ⟨i.val,by omega⟩))) (0,1) := by
  induction k with
  | zero => simp [polynomialState,runPolynomial]
  | succ k ih =>
    have hkN : k < N := by omega
    rw [polynomialState,dite_eq_left hkN,List.ofFn_succ',List.concat_eq_append,runPolynomial_append]
    rw [ih (by omega)]
    simp only [runPolynomial,Fin.val_castSucc,Fin.val_last]

/-- Every normalized residual polynomial of degree at most N is exactly attained by
a strict-subdiagonal increment map, hence by two persistent registers. -/
theorem exists_two_register_polynomial (N : ℕ) (p : ℝ[X])
    (hp : p.eval 0=1) (hd : p.natDegree  ≤  N) :
    ∃ (d : Fin N → ℝ) (T : RealizationCore.StrictIncrement N),
      RegisterMachine.HasVectorRealization N (RealizationCore.W_of N d T.val) 2 ∧
      QuadraticFoundations.pIter N d T.val N=p := by
  obtain ⟨ss,hlen,hss⟩ := exists_factor_steps N p hp hd
  obtain ⟨s,hs⟩ := ofFn_of_length ss N hlen
  let d : Fin N → ℝ := fun i => (s i).1
  let t : Fin N → ℝ := fun i => (s i).2
  refine ⟨d,⟨subdiagonal N t,subdiagonal_strict N t⟩,?_,?_⟩
  · apply (RegisterMachine.hasVectorRealization_iff_scalar N _ 2).mpr
    exact (RealizationCore.realization_iff_coordinates N 1 d _).mpr (subdiagonal_memory N t)
  · have hr := congrArg Prod.snd (polynomialState_eq_run N d t N le_rfl)
    rw [polynomialState_eq] at hr
    simp only at hr
    have he : (fun i : Fin N => (d ⟨i.val,by omega⟩,t ⟨i.val,by omega⟩))=s := by
      funext i
      rfl
    rw [he,hs] at hr
    exact hr.trans hss
    omega

/-- Every predetermined method has a two-register replacement with exactly the same
terminal point on every matrix quadratic, independently of dimension. -/
theorem exists_two_register_exact_replacement (N : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) :
    ∃ (d' : Fin N → ℝ) (T' : RealizationCore.StrictIncrement N),
      RegisterMachine.HasVectorRealization N (RealizationCore.W_of N d' T'.val) 2 ∧
      ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ),
        QuadraticResidual.errorIter N d' T'.val Q e N =
          QuadraticResidual.errorIter N d T.val Q e N := by
  obtain ⟨d',T',hm,hp⟩ := exists_two_register_polynomial N
    (QuadraticFoundations.pIter N d T.val N)
    (QuadraticFoundations.pIter_eval_zero N d T.val N le_rfl)
    (QuadraticFoundations.pIter_natDegree_le N d T.val N le_rfl)
  refine ⟨d',T',hm,?_⟩
  intro n Q e
  rw [QuadraticResidual.errorIter_eq_polynomial N d' T'.val Q e N le_rfl,
    QuadraticResidual.errorIter_eq_polynomial N d T.val Q e N le_rfl,hp]

end QuadraticReplacement
