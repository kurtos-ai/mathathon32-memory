module
public import Submission2026.CompletionMemory
public import Continuation.Support.SmoothGramCore

/-! # From a positive semidefinite completion to displacement factors

This module supplies the range and finite-rank factorization ingredients for the
completion-memory construction. Factor coordinates use a basis of the column
space; they need not be an orthonormal Gram representation.
-/
@[expose] public section
noncomputable section
namespace Submission2026.CompletionFactorization
open Matrix RegisterMachine
open scoped BigOperators Matrix
variable {N : ℕ}

/-- The actual bordered completion in the theorem. -/
def Gamma (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (z : Fin (N+1) → ℝ) (ν : ℝ) :
    Matrix (Fin (N+1) ⊕ Fin 1) (Fin (N+1) ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks K (fun i _ => z i) (fun _ j => z j) (fun _ _ => ν)

theorem principal_psd (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (z : Fin (N+1) → ℝ)
    (ν : ℝ) (h : (Gamma K z ν).PosSemidef) : K.PosSemidef := by
  have he : (Gamma K z ν).submatrix Sum.inl Sum.inl = K := rfl
  rw [← he]
  exact h.submatrix Sum.inl

theorem rank_le_completion (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (z : Fin (N+1) → ℝ) (ν : ℝ) : K.rank ≤ (Gamma K z ν).rank := by
  have he : (Gamma K z ν).submatrix Sum.inl Sum.inl = K := rfl
  rw [← he]
  exact Matrix.rank_submatrix_le (Gamma K z ν) Sum.inl Sum.inl

theorem range_gram {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : LinearMap.range (Aᵀ*A).mulVecLin = LinearMap.range Aᵀ.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · change (Aᵀ*A).rank = Aᵀ.rank
    rw [Matrix.rank_transpose_mul_self,Matrix.rank_transpose]

/-- PSD of the actual bordered matrix forces its border into the range of K. -/
theorem border_mem_range (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (z : Fin (N+1) → ℝ) (ν : ℝ) (h : (Gamma K z ν).PosSemidef) :
    z ∈ LinearMap.range K.mulVecLin := by
  obtain ⟨B,hB⟩ := Continuation.SmoothSupport.psd_factorization (Gamma K z ν) h
  let A : Matrix (Fin (N+1) ⊕ Fin 1) (Fin (N+1)) ℝ := fun i j => B i (Sum.inl j)
  let q : (Fin (N+1) ⊕ Fin 1) → ℝ := fun i => B i (Sum.inr 0)
  have hK : K = Aᵀ*A := by
    ext i j
    have hb := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hB
    change K i j = ∑ k, B k (Sum.inl i)*B k (Sum.inl j) at hb
    exact hb
  have hz : Aᵀ *ᵥ q = z := by
    ext i
    have hb := congrArg (fun M => M (Sum.inl i) (Sum.inr 0)) hB
    change z i = ∑ k, B k (Sum.inl i)*B k (Sum.inr 0) at hb
    exact hb.symm
  rw [hK,range_gram]
  exact ⟨q,hz⟩

/-- Rank(K)-dimensional factors for K and every vector in its range. -/
theorem exists_rank_factors (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (z : Fin (N+1) → ℝ) (hz : z ∈ LinearMap.range K.mulVecLin) :
    ∃ (ξ β : Fin (N+1) → Fin K.rank → ℝ) (v : Fin K.rank → ℝ),
      (∀ i j, K i j = dot (ξ i) (β j)) ∧ (∀ i, z i = dot (ξ i) v) := by
  let S := LinearMap.range K.mulVecLin
  let b : Module.Basis (Fin K.rank) ℝ S := Module.finBasis ℝ S
  have hc (j : Fin (N+1)) : K.col j ∈ S := by
    refine ⟨Pi.single j 1,?_⟩
    ext i
    simp [Matrix.mulVec,dotProduct,Matrix.col_apply,Pi.single_apply]
  let ξ : Fin (N+1) → Fin K.rank → ℝ := fun i l => (b l).val i
  let β : Fin (N+1) → Fin K.rank → ℝ := fun j => b.repr ⟨K.col j,hc j⟩
  let v : Fin K.rank → ℝ := b.repr ⟨z,hz⟩
  have hrepr (q : S) (i : Fin (N+1)) : q.val i = dot (ξ i) (b.repr q) := by
    have hb := congrArg (fun x : S => x.val i) (b.sum_repr q)
    simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hb
    calc
      q.val i = ∑ l, (b.repr q) l*(b l).val i := hb.symm
      _ = dot (ξ i) (b.repr q) := by
        unfold dot
        apply Finset.sum_congr rfl
        intro l _
        exact mul_comm _ _
  refine ⟨ξ,β,v,?_,?_⟩
  · intro i j
    exact hrepr ⟨K.col j,hc j⟩ i
  · intro i
    exact hrepr ⟨z,hz⟩ i

theorem psd_rank_factors (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (z : Fin (N+1) → ℝ) (ν : ℝ) (h : (Gamma K z ν).PosSemidef) :
    ∃ (ξ β : Fin (N+1) → Fin K.rank → ℝ) (v : Fin K.rank → ℝ),
      (∀ i j, K i j = dot (ξ i) (β j)) ∧ (∀ i, z i = dot (ξ i) v) :=
  exists_rank_factors K z (border_mem_range K z ν h)

/-- The upper triangular matrix with the report's constant strict upper rows. -/
def T (t : ℕ → ℝ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i j =>
  if i=j then t i.val else if i < j then t i.val-t (i.val+1) else 0

@[simp] theorem T_diag (t : ℕ → ℝ) (i : Fin (N+1)) : T t i i = t i.val := by simp [T]

theorem T_upper (t : ℕ → ℝ) : (T t : Matrix (Fin (N+1)) (Fin (N+1)) ℝ).IsUpperTriangular := by
  intro i j h
  change j < i at h
  simp [T,ne_of_gt h,not_lt_of_gt h]

theorem T_isUnit (t : ℕ → ℝ) (ht : ∀ i ≤ N, t i ≠ 0) :
    IsUnit (T t : Matrix (Fin (N+1)) (Fin (N+1)) ℝ).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_of_isUpperTriangular (T_upper t)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simpa using ht i.val (by omega)

theorem T_column_difference (t : ℕ → ℝ) (j : Fin N) (i : Fin (N+1)) :
    T t i j.succ-T t i j.castSucc = t (j.val+1)*
      ((if i=j.succ then 1 else 0)-(if i=j.castSucc then 1 else 0)) := by
  by_cases h0 : i=j.castSucc
  · subst i
    simp [T,Fin.ext_iff,Fin.lt_def]
  by_cases h1 : i=j.succ
  · subst i
    simp [T,Fin.ext_iff,Fin.lt_def]
  have he : (i < j.succ) ↔ i < j.castSucc := by
    have hn : i.val ≠ j.val := fun h => h0 (Fin.ext h)
    simp only [Fin.lt_def,Fin.val_succ,Fin.val_castSucc]
    omega
  simp [T,h0,h1,he]

/-- The completion matrix appearing in the paper. -/
def E (t : ℕ → ℝ) (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := (U*(T t)⁻¹)ᵀ

theorem E_lower (t : ℕ → ℝ) (ht : ∀ i ≤ N, t i ≠ 0)
    (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular) :
    (E t U).IsLowerTriangular := by
  let := Matrix.invertibleOfIsUnitDet (T t : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (T_isUnit t ht)
  exact (hU.mul (Matrix.blockTriangular_inv_of_blockTriangular (T_upper t))).transpose

theorem E_transpose_mul_T (t : ℕ → ℝ) (ht : ∀ i ≤ N, t i ≠ 0)
    (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : (E t U)ᵀ*T t = U := by
  rw [E,Matrix.transpose_transpose,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (T_isUnit t ht),Matrix.mul_one]

theorem E_diag (t : ℕ → ℝ) (ht : ∀ i ≤ N, t i ≠ 0)
    (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular)
    (hdiag : ∀ i, U i i = t i.val) (i : Fin (N+1)) : E t U i i = 1 := by
  have hm : (T t)ᵀ*E t U = Uᵀ := by
    simpa using congrArg Matrix.transpose (E_transpose_mul_T t ht U)
  have hd := congrArg (fun M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ => M i i) hm
  rw [CompletionMemory.lower_mul_diag _ _ (T_upper t).transpose (E_lower t ht U hU)] at hd
  simp only [Matrix.transpose_apply,T_diag,hdiag] at hd
  apply mul_left_cancel₀ (ht i.val (by omega))
  simpa using hd

theorem E_difference (t : ℕ → ℝ) (ht : ∀ i ≤ N, t i ≠ 0)
    (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Fin (N+1)) (j : Fin N) :
    t (j.val+1)*(E t U j.succ i-E t U j.castSucc i) = U i j.succ-U i j.castSucc := by
  conv_rhs => rw [← E_transpose_mul_T t ht U]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,← Finset.sum_sub_distrib,← mul_sub]
  simp_rw [T_column_difference]
  simp [mul_sub,mul_ite,Finset.sum_sub_distrib]
  ring

/-- The symmetric-part slack K = sym(U) - P in the report. -/
def core (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i j => (U i j+U j i)/2-P i j

/-- The actual border U T⁻¹ e_N. -/
def border (t : ℕ → ℝ) (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : Fin (N+1) → ℝ :=
  U *ᵥ ((T t)⁻¹ *ᵥ Pi.single (Fin.last N) 1)

theorem E_terminal (t : ℕ → ℝ) (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (i : Fin (N+1)) : E t U (Fin.last N) i = border t U i := by
  rw [border,Matrix.mulVec_mulVec,Matrix.mulVec_single_one]
  rfl

def ConstantUpperRows (P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : Prop :=
  ∀ i j k, i < j → i < k → P i j = P i k

theorem core_difference (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hU : U.IsUpperTriangular) (hP : ConstantUpperRows P)
    (i : Fin (N+1)) (j : Fin N) (hij : i < j.castSucc) :
    2*(core U P i j.succ-core U P i j.castSucc) = U i j.succ-U i j.castSucc := by
  have hin : i < j.succ := by
    simp only [Fin.lt_def,Fin.val_succ,Fin.val_castSucc] at *
    omega
  have h0 : U j.castSucc i = 0 := hU hij
  have h1 : U j.succ i = 0 := hU hin
  have hp := hP i j.succ j.castSucc hin hij
  simp only [core,h0,h1,hp]
  ring

/-- Backwards telescoping coordinates for the displacement factor. -/
def factors {r : ℕ} (t : ℕ → ℝ) (β : Fin (N+1) → Fin r → ℝ) (v : Fin r → ℝ) :
    Fin (N+1) → Fin r → ℝ :=
  Fin.reverseInduction v (fun j next l => next l-2*(β j.succ l-β j.castSucc l)/t (j.val+1))

@[simp] theorem factors_last {r : ℕ} (t : ℕ → ℝ) (β : Fin (N+1) → Fin r → ℝ)
    (v : Fin r → ℝ) : factors t β v (Fin.last N) = v := by simp [factors]

theorem factors_step {r : ℕ} (t : ℕ → ℝ) (β : Fin (N+1) → Fin r → ℝ)
    (v : Fin r → ℝ) (j : Fin N) :
    factors t β v j.castSucc = fun l =>
      factors t β v j.succ l-2*(β j.succ l-β j.castSucc l)/t (j.val+1) := by simp [factors]

theorem dot_step {r : ℕ} (p q s x : Fin r → ℝ) (t : ℝ) :
    dot (fun l => p l-2*(q l-s l)/t) x = dot p x-2*(dot x q-dot x s)/t := by
  have ht (l : Fin r) : (2*(q l-s l)/t)*x l = (2/t)*(x l*q l-x l*s l) := by ring
  simp only [dot,sub_mul,Finset.sum_sub_distrib]
  simp_rw [ht]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  ring

/-- The PSD completion produces the report's separability, without assuming it. -/
theorem E_separable {r : ℕ} (t : ℕ → ℝ) (ht : ∀ i ≤ N, t i ≠ 0)
    (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular)
    (hP : ConstantUpperRows P) (ξ β : Fin (N+1) → Fin r → ℝ) (v : Fin r → ℝ)
    (hK : ∀ i j, core U P i j = dot (ξ i) (β j))
    (hz : ∀ i, border t U i = dot (ξ i) v) :
    ∀ j i, i < j → E t U j i = dot (factors t β v j) (ξ i) := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    intro i _
    rw [E_terminal,factors_last,hz]
    exact dotProduct_comm _ _
  | cast j ih =>
    intro i hij
    have hin : i < j.succ := by
      simp only [Fin.lt_def,Fin.val_succ,Fin.val_castSucc] at *
      omega
    have hd := E_difference t ht U i j
    rw [← core_difference U P hU hP i j hij,hK,hK] at hd
    have he : E t U j.succ i-E t U j.castSucc i =
        2*(dot (ξ i) (β j.succ)-dot (ξ i) (β j.castSucc))/t (j.val+1) := by
      apply (eq_div_iff (ht (j.val+1) (by omega))).mpr
      nlinarith [hd]
    rw [factors_step,dot_step,← ih i hin]
    linarith

/-- Normalize the irrelevant initial coefficient to the report's a₀ = 0. -/
def displacementFactors {r : ℕ} (t : ℕ → ℝ) (β : Fin (N+1) → Fin r → ℝ)
    (v : Fin r → ℝ) : Fin (N+1) → Fin r → ℝ :=
  fun j => if j=0 then 0 else factors t β v j

@[simp] theorem displacementFactors_zero {r : ℕ} (t : ℕ → ℝ)
    (β : Fin (N+1) → Fin r → ℝ) (v : Fin r → ℝ) :
    displacementFactors t β v 0 = 0 := by simp [displacementFactors]

/-- All separability premises are consequences of the actual completion data. -/
theorem completion_separable (t : ℕ → ℝ) (ht : ∀ i ≤ N, 0 < t i)
    (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular)
    (hP : ConstantUpperRows P) (ν : ℝ)
    (hΓ : (Gamma (core U P) (border t U) ν).PosSemidef) :
    ∃ (a ξ : Fin (N+1) → Fin (core U P).rank → ℝ),
      a 0 = 0 ∧ ∀ j i, i < j → E t U j i = dot (a j) (ξ i) := by
  have ht0 : ∀ i ≤ N, t i ≠ 0 := fun i hi => ne_of_gt (ht i hi)
  obtain ⟨ξ,β,v,hK,hz⟩ := psd_rank_factors (core U P) (border t U) ν hΓ
  refine ⟨displacementFactors t β v,ξ,displacementFactors_zero t β v,?_⟩
  intro j i hij
  have hj : j ≠ 0 := by
    intro hj
    subst j
    exact (Fin.not_lt_zero i) hij
  simpa only [displacementFactors,hj,ite_false] using E_separable t ht0 U P hU hP ξ β v hK hz j i hij

/-- Complete construction from the actual PSD completion data. -/
theorem completion_realization (t : ℕ → ℝ) (ht : ∀ i ≤ N, 0 < t i)
    (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular)
    (hdiag : ∀ i, U i i = t i.val) (hP : ConstantUpperRows P) (ν : ℝ)
    (hΓ : (Gamma (core U P) (border t U) ν).PosSemidef) :
    ∃ (a ξ : Fin (N+1) → Fin (core U P).rank → ℝ),
      a 0 = 0 ∧ VectorRealizes N ((core U P).rank+1)
        (1-(CompletionMemory.C N)⁻¹*(E t U)⁻¹) (CompletionMemory.machine a ξ) := by
  have ht0 : ∀ i ≤ N, t i ≠ 0 := fun i hi => ne_of_gt (ht i hi)
  obtain ⟨a,ξ,ha,hsep⟩ := completion_separable t ht U P hU hP ν hΓ
  refine ⟨a,ξ,ha,?_⟩
  exact CompletionMemory.realizes_of_separable (E t U) a ξ (E_lower t ht0 U hU)
    (E_diag t ht0 U hU hdiag) hsep

/-- The full rank chain in the completion-memory theorem. -/
theorem completion_memory_bound (t : ℕ → ℝ) (ht : ∀ i ≤ N, 0 < t i)
    (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular)
    (hdiag : ∀ i, U i i = t i.val) (hP : ConstantUpperRows P) (ν : ℝ)
    (hΓ : (Gamma (core U P) (border t U) ν).PosSemidef) :
    MemoryRank.CutRank.memRank N (1-(CompletionMemory.C N)⁻¹*(E t U)⁻¹) ≤
        1+(core U P).rank ∧
      1+(core U P).rank ≤ 1+(Gamma (core U P) (border t U) ν).rank := by
  obtain ⟨a,ξ,_,hM⟩ := completion_realization t ht U P hU hdiag hP ν hΓ
  constructor
  · have hm := (vectorRealization_iff_maxCutRank N _ ((core U P).rank+1)).mp ⟨_,hM⟩
    simpa [Nat.add_comm] using hm
  · exact Nat.add_le_add_left (rank_le_completion _ _ _) 1

/-- The inverse-defined H is strictly lower triangular, as asserted in the theorem. -/
theorem completion_strict_lower (t : ℕ → ℝ) (ht : ∀ i ≤ N, 0 < t i)
    (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular)
    (hdiag : ∀ i, U i i = t i.val) (hP : ConstantUpperRows P) (ν : ℝ)
    (hΓ : (Gamma (core U P) (border t U) ν).PosSemidef)
    (i j : Fin (N+1)) (hij : i ≤ j) :
    ((CompletionMemory.C N)⁻¹*(E t U)⁻¹-1) i j = 0 := by
  have ht0 : ∀ i ≤ N, t i ≠ 0 := fun i hi => ne_of_gt (ht i hi)
  obtain ⟨a,ξ,_,hsep⟩ := completion_separable t ht U P hU hP ν hΓ
  rw [CompletionMemory.eq_D_of_separable (E t U) a ξ (E_lower t ht0 U hU)
    (E_diag t ht0 U hU hdiag) hsep]
  have hw := CompletionMemory.W_causal a ξ i j hij
  change (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) i j -
    ((CompletionMemory.C N)⁻¹*(CompletionMemory.D a ξ)⁻¹) i j = 0 at hw
  change ((CompletionMemory.C N)⁻¹*(CompletionMemory.D a ξ)⁻¹) i j -
    (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) i j = 0
  linarith

/-- The bound applies to every operational cut of the actual completion history. -/
theorem completion_cut_rank (t : ℕ → ℝ) (ht : ∀ i ≤ N, 0 < t i)
    (U P : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hU : U.IsUpperTriangular)
    (hdiag : ∀ i, U i i = t i.val) (hP : ConstantUpperRows P) (ν : ℝ)
    (hΓ : (Gamma (core U P) (border t U) ν).PosSemidef) (k : ℕ) (hk : k ≤ N) :
    (RegisterMachine.H_k N k hk (1-(CompletionMemory.C N)⁻¹*(E t U)⁻¹)).rank ≤
      1+(core U P).rank := by
  obtain ⟨a,ξ,_,hM⟩ := completion_realization t ht U P hU hdiag hP ν hΓ
  have hr := necessity_rank_le_unconditional N ((core U P).rank+1) _ k hk
    ⟨_,(vectorRealizes_iff_scalar N ((core U P).rank+1) _ _).mp hM⟩
  simpa [Nat.add_comm] using hr

#print axioms completion_strict_lower
#print axioms completion_cut_rank
#print axioms border_mem_range
#print axioms psd_rank_factors
#print axioms completion_realization
#print axioms completion_memory_bound
end Submission2026.CompletionFactorization
