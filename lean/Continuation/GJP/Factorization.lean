module
public import Continuation.GJP.FactorizationCore
@[expose] public section
noncomputable section
open Matrix
namespace GJP

/-- The triangular factorization and sign clauses of Proposition 2.3. -/
structure TCFactor {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A T C : Matrix n n ℝ) : Prop where
  factor : A = T*C
  upper : T.IsUpperTriangular
  diagNonneg : ∀ i, 0 ≤ T i i
  upperNonpos : ∀ i j, i < j → T i j ≤ 0
  unitLower : UnitLower C
  lowerNonpos : ∀ i j, j < i → C i j ≤ 0

lemma TCFactor.border {n : ℕ} {B T C : Matrix (Fin n) (Fin n) ℝ}
    (h : TCFactor B T C) (u v : Fin n → ℝ) (a : ℝ)
    (hu : ∀ i, u i ≤ 0) (hv : ∀ j, v j ≤ 0) (ha : 0 ≤ a) :
    TCFactor (GJP.border (B+Matrix.vecMulVec u v) u (fun j => a*v j) a)
      (GJP.border T u 0 a) (GJP.border C 0 v 1) := by
  refine ⟨?_,border_upper T u a h.upper,?_,?_,border_unitLower C v h.unitLower,?_⟩
  · rw [border_mul,h.factor]
  · intro i
    induction i using Fin.lastCases
    · simpa only [GJP.border_last_last] using ha
    · simpa only [GJP.border_cast_cast] using h.diagNonneg _
  · intro i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · exact False.elim (lt_irrefl _ hij)
    · simp only [Fin.lt_def,Fin.val_last,Fin.val_castSucc] at hij; omega
    · simpa only [GJP.border_cast_last] using hu _
    · simpa only [GJP.border_cast_cast] using h.upperNonpos _ _ hij
  · intro i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · exact False.elim (lt_irrefl _ hij)
    · simpa only [GJP.border_last_cast] using hv _
    · simp only [Fin.lt_def,Fin.val_last,Fin.val_castSucc] at hij; omega
    · simpa only [GJP.border_cast_cast] using h.lowerNonpos _ _ hij

/-- Proposition 2.3, including matrices with singular pivots: every row- and
    column-diagonally-dominant Z-matrix admits the stated TC factorization. -/
theorem exists_TC_factor (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : DDMZ A) :
    ∃ T C, TCFactor A T C := by
  induction n with
  | zero =>
    refine ⟨A,1,?_⟩
    refine ⟨by simp,?_,?_,?_,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · constructor <;> intro i <;> exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    have ha0 := hA.diag_nonneg (Fin.last n)
    by_cases ha : A (Fin.last n) (Fin.last n) = 0
    · obtain ⟨hr,hc⟩ := hA.zero_pivot (Fin.last n) ha
      let B : Matrix (Fin n) (Fin n) ℝ := fun i j => A i.castSucc j.castSucc
      have hB : DDMZ B := by
        refine ⟨?_,?_,?_⟩
        · intro i j hij
          exact hA.offdiag i.castSucc j.castSucc (by intro he; exact hij (Fin.castSucc_injective _ he))
        · intro i
          have h := hA.rows i.castSucc
          rw [Fin.sum_univ_castSucc, hc i.castSucc,add_zero] at h
          exact h
        · intro j
          have h := hA.cols j.castSucc
          rw [Fin.sum_univ_castSucc, hr j.castSucc,add_zero] at h
          exact h
      obtain ⟨T,C,hTC⟩ := ih B hB
      have hf := hTC.border (fun _ => 0) (fun _ => 0) 0 (fun _ => le_rfl) (fun _ => le_rfl) le_rfl
      have he : A = GJP.border (B+Matrix.vecMulVec (fun _ => 0) (fun _ => 0))
          (fun _ => 0) (fun j => (0 : ℝ)*0) 0 := by
        rw [matrix_eq_border A]
        have hz : Matrix.vecMulVec (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (0 : ℝ)) = 0 := by
          ext i j; simp [Matrix.vecMulVec_apply]
        simp only [hc,hr,hz,add_zero,mul_zero]
        rfl
      rw [← he] at hf
      exact ⟨_,_,hf⟩
    · have hap : 0 < A (Fin.last n) (Fin.last n) := lt_of_le_of_ne ha0 (Ne.symm ha)
      obtain ⟨T,C,hTC⟩ := ih (lastSchur A) (hA.schur hap)
      let u : Fin n → ℝ := fun i => A i.castSucc (Fin.last n)
      let v : Fin n → ℝ := fun j => A (Fin.last n) j.castSucc/A (Fin.last n) (Fin.last n)
      have hu : ∀ i, u i ≤ 0 := fun i => hA.offdiag _ _ (Fin.castSucc_ne_last i)
      have hv : ∀ j, v j ≤ 0 := fun j => div_nonpos_of_nonpos_of_nonneg
        (hA.offdiag _ _ (Ne.symm (Fin.castSucc_ne_last j))) hap.le
      have hf := hTC.border u v (A (Fin.last n) (Fin.last n)) hu hv hap.le
      have hB : lastSchur A+Matrix.vecMulVec u v = fun i j => A i.castSucc j.castSucc := by
        ext i j
        simp only [lastSchur,Matrix.add_apply,Matrix.vecMulVec_apply,u,v]
        ring
      have hv' : (fun j => A (Fin.last n) (Fin.last n)*v j) = fun j => A (Fin.last n) j.castSucc := by
        funext j
        dsimp [v]
        field_simp
      rw [hB,hv'] at hf
      rw [← matrix_eq_border A] at hf
      exact ⟨_,_,hf⟩

end GJP
