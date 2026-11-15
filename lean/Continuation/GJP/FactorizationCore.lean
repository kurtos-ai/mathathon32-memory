module
public import Continuation.GJP.FactorProjection
@[expose] public section
noncomputable section
open Matrix
namespace GJP

/-- The exact row/column diagonally dominant Z-matrix domain of Proposition 2.3. -/
structure DDMZ {n : Type*} [Fintype n] (A : Matrix n n ℝ) : Prop where
  offdiag : ∀ i j, i ≠ j → A i j ≤ 0
  rows : ∀ i, 0 ≤ ∑ j, A i j
  cols : ∀ j, 0 ≤ ∑ i, A i j

lemma DDMZ.diag_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : DDMZ A) (i : n) : 0 ≤ A i i := by
  have hs : (∑ j ∈ Finset.univ.erase i, A i j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    exact h.offdiag i j (Ne.symm (Finset.mem_erase.mp hj).1)
  have hr := h.rows i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hr
  linarith

lemma DDMZ.zero_pivot {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : DDMZ A) (i : n) (hi : A i i = 0) :
    (∀ j, A i j = 0) ∧ (∀ j, A j i = 0) := by
  have hr : ∀ j, A i j ≤ 0 := by
    intro j
    by_cases he : i=j
    · subst j; exact hi.le
    · exact h.offdiag i j he
  have hc : ∀ j, A j i ≤ 0 := by
    intro j
    by_cases he : j=i
    · subst j; exact hi.le
    · exact h.offdiag j i he
  have hrs : ∑ j, A i j = 0 := le_antisymm (Finset.sum_nonpos (fun j _ => hr j)) (h.rows i)
  have hcs : ∑ j, A j i = 0 := le_antisymm (Finset.sum_nonpos (fun j _ => hc j)) (h.cols i)
  exact ⟨fun j => (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => hr k)).mp hrs j (Finset.mem_univ j),
    fun j => (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => hc k)).mp hcs j (Finset.mem_univ j)⟩

/-- Append a final row and column, keeping the finite order used in the elimination. -/
def border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) (a : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.lastCases (Fin.lastCases a v j)
    (fun i => Fin.lastCases (u i) (fun j => A i j) j) i

@[simp] lemma border_cast_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) (a : ℝ)
    (i j : Fin n) : border A u v a i.castSucc j.castSucc = A i j := by simp [border]

@[simp] lemma border_cast_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) (a : ℝ)
    (i : Fin n) : border A u v a i.castSucc (Fin.last n) = u i := by simp [border]

@[simp] lemma border_last_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) (a : ℝ)
    (j : Fin n) : border A u v a (Fin.last n) j.castSucc = v j := by simp [border]

@[simp] lemma border_last_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) (a : ℝ) :
    border A u v a (Fin.last n) (Fin.last n) = a := by simp [border]

lemma border_mul {n : ℕ} (T C : Matrix (Fin n) (Fin n) ℝ)
    (u v : Fin n → ℝ) (a : ℝ) :
    border T u 0 a * border C 0 v 1 =
      border (T*C+Matrix.vecMulVec u v) u (fun j => a*v j) a := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply,Fin.sum_univ_castSucc,Matrix.vecMulVec_apply]

lemma matrix_eq_border {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    A = border (fun i j => A i.castSucc j.castSucc)
      (fun i => A i.castSucc (Fin.last n)) (fun j => A (Fin.last n) j.castSucc)
      (A (Fin.last n) (Fin.last n)) := by
  funext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (border_last_last (fun i j => A i.castSucc j.castSucc) (fun i => A i.castSucc (Fin.last n)) (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n))).symm
    | cast j => exact (border_last_cast (fun i j => A i.castSucc j.castSucc) (fun i => A i.castSucc (Fin.last n)) (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)) j).symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact (border_cast_last (fun i j => A i.castSucc j.castSucc) (fun i => A i.castSucc (Fin.last n)) (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)) i).symm
    | cast j => exact (border_cast_cast (fun i j => A i.castSucc j.castSucc) (fun i => A i.castSucc (Fin.last n)) (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)) i j).symm

lemma border_upper {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (a : ℝ)
    (hT : T.IsUpperTriangular) : (border T u 0 a).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · exact False.elim (lt_irrefl _ hij)
  · simp
  · simp only [Fin.lt_def,Fin.val_last,Fin.val_castSucc] at hij; omega
  · simpa only [border_cast_cast] using hT hij

lemma border_unitLower {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hC : UnitLower C) : UnitLower (border C 0 v 1) := by
  constructor
  · intro i j hij
    change i < j at hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · exact False.elim (lt_irrefl _ hij)
    · simp only [Fin.lt_def,Fin.val_last,Fin.val_castSucc] at hij; omega
    · simp
    · simpa only [border_cast_cast] using hC.1 hij
  · intro i
    induction i using Fin.lastCases
    · simp
    · simp [hC.2]

/-- Backward Gaussian elimination's Schur complement. -/
def lastSchur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i.castSucc j.castSucc-
    A i.castSucc (Fin.last n)*A (Fin.last n) j.castSucc/A (Fin.last n) (Fin.last n)

lemma lastSchur_rows {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (ha : A (Fin.last n) (Fin.last n) ≠ 0) (i : Fin n) :
    (∑ j, lastSchur A i j) = (∑ j, A i.castSucc j)-
      A i.castSucc (Fin.last n)/A (Fin.last n) (Fin.last n)*(∑ j, A (Fin.last n) j) := by
  simp only [lastSchur,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum]
  rw [Fin.sum_univ_castSucc (fun j => A i.castSucc j),
    Fin.sum_univ_castSucc (fun j => A (Fin.last n) j)]
  field_simp
  ring

lemma lastSchur_cols {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (ha : A (Fin.last n) (Fin.last n) ≠ 0) (j : Fin n) :
    (∑ i, lastSchur A i j) = (∑ i, A i j.castSucc)-
      A (Fin.last n) j.castSucc/A (Fin.last n) (Fin.last n)*(∑ i, A i (Fin.last n)) := by
  simp only [lastSchur,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_mul]
  rw [Fin.sum_univ_castSucc (fun i => A i j.castSucc),
    Fin.sum_univ_castSucc (fun i => A i (Fin.last n))]
  field_simp
  ring

lemma DDMZ.schur {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (h : DDMZ A) (ha : 0 < A (Fin.last n) (Fin.last n)) : DDMZ (lastSchur A) := by
  have hu (i : Fin n) : A i.castSucc (Fin.last n) ≤ 0 :=
    h.offdiag i.castSucc (Fin.last n) (Fin.castSucc_ne_last i)
  have hv (j : Fin n) : A (Fin.last n) j.castSucc ≤ 0 :=
    h.offdiag (Fin.last n) j.castSucc (Ne.symm (Fin.castSucc_ne_last j))
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    have hbase := h.offdiag i.castSucc j.castSucc (by intro he; exact hij (Fin.castSucc_injective _ he))
    have hprod := div_nonneg (mul_nonneg_of_nonpos_of_nonpos (hu i) (hv j)) ha.le
    dsimp [lastSchur]
    linarith
  · intro i
    rw [lastSchur_rows A (ne_of_gt ha)]
    have hm := mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (hu i) ha.le) (h.rows (Fin.last n))
    linarith [h.rows i.castSucc]
  · intro j
    rw [lastSchur_cols A (ne_of_gt ha)]
    have hm := mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (hv j) ha.le) (h.cols (Fin.last n))
    linarith [h.cols j.castSucc]

end GJP
