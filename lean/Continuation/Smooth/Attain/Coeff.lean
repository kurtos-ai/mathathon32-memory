module
public import Continuation.Quadratic.Foundations
public import Mathlib
@[expose] public section
noncomputable section
namespace SmoothAttain

open Polynomial QuadraticFoundations Finset

-- p_α(λ) = ∏ (1 - α_i λ)
def pReal {N : ℕ} (α : Fin N → ℝ) (lam : ℝ) : ℝ :=
  ∏ i : Fin N, (1 - α i * lam)

lemma pReal_eq_productPoly_eval {N : ℕ} (α : Fin N → ℝ) (lam : ℝ) :
    pReal α lam = (productPoly (fun i => -α i)).eval lam := by
  unfold pReal productPoly
  simp only [eval_prod, eval_add, eval_mul, eval_C, eval_X]
  apply Finset.prod_congr rfl
  intro i _
  ring

-- coeff 0 of productPoly is 1
lemma productPoly_coeff_zero {N : ℕ} (d : Fin N → ℝ) :
    (productPoly (N:=N) d).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, productPoly_eval_zero]

-- Helper: productPoly for Fin (N+1) splits
lemma productPoly_succ {N : ℕ} (d : Fin (N+1) → ℝ) :
    productPoly d = productPoly (fun i : Fin N => d (Fin.castSucc i)) * (Polynomial.C 1 + Polynomial.C (d (Fin.last N)) * Polynomial.X) := by
  unfold productPoly
  rw [Fin.prod_univ_castSucc]

-- coeff helpers for p*(C1+Cd*X)
lemma coeff_mul_C_add_CdX_one (p : ℝ[X]) (d : ℝ) :
    (p * (Polynomial.C 1 + Polynomial.C d * Polynomial.X)).coeff 1 = p.coeff 1 + p.coeff 0 * d := by
  have h2 : (p * (Polynomial.C 1 + Polynomial.C d * Polynomial.X)).coeff 1 =
      (p * Polynomial.C 1).coeff 1 + (p * (Polynomial.C d * Polynomial.X)).coeff 1 := by
    rw [mul_add, coeff_add]
  have h3 : (p * Polynomial.C (1:ℝ)).coeff 1 = p.coeff 1 := by simp
  have h4 : (p * (Polynomial.C d * Polynomial.X)).coeff 1 = p.coeff 0 * d := by
    have : p * (Polynomial.C d * Polynomial.X) = Polynomial.C d * (p * Polynomial.X) := by ring
    rw [this, coeff_C_mul, coeff_mul_X]
    ring
  rw [h2, h3, h4]

lemma coeff_mul_C_add_CdX_two (p : ℝ[X]) (d : ℝ) :
    (p * (Polynomial.C 1 + Polynomial.C d * Polynomial.X)).coeff 2 = p.coeff 2 + p.coeff 1 * d := by
  have h2 : (p * (Polynomial.C 1 + Polynomial.C d * Polynomial.X)).coeff 2 =
      (p * Polynomial.C 1).coeff 2 + (p * (Polynomial.C d * Polynomial.X)).coeff 2 := by
    rw [mul_add, coeff_add]
  have h3 : (p * Polynomial.C (1:ℝ)).coeff 2 = p.coeff 2 := by simp
  have h4 : (p * (Polynomial.C d * Polynomial.X)).coeff 2 = p.coeff 1 * d := by
    have : p * (Polynomial.C d * Polynomial.X) = Polynomial.C d * (p * Polynomial.X) := by ring
    rw [this, coeff_C_mul, coeff_mul_X]
    ring
  rw [h2, h3, h4]

-- coeff 1 formula: coeff 1 = ∑ d i
lemma productPoly_coeff_one {N : ℕ} (d : Fin N → ℝ) :
    (productPoly (N:=N) d).coeff 1 = ∑ i : Fin N, d i := by
  induction N with
  | zero =>
    have h : (productPoly (N:=0) d) = 1 := by unfold productPoly; simp
    rw [h]
    simp [coeff_one]
  | succ N ih =>
    have hsplit := productPoly_succ (N:=N) d
    have h_sum : (∑ i : Fin (N+1), d i) = (∑ i : Fin N, d (Fin.castSucc i)) + d (Fin.last N) := by
      rw [Fin.sum_univ_castSucc]
    rw [hsplit, coeff_mul_C_add_CdX_one, ih, productPoly_coeff_zero]
    rw [h_sum]
    ring

-- Define pair sum as ∑ i, ∑ j > i, d i * d j
def pairSum {N : ℕ} (d : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if (i.val < j.val) then d i * d j else 0

lemma pairSum_succ {N : ℕ} (d : Fin (N+1) → ℝ) :
    pairSum d = pairSum (fun i : Fin N => d (Fin.castSucc i)) + (∑ i : Fin N, d (Fin.castSucc i) * d (Fin.last N)) := by
  unfold pairSum
  have h1 : (∑ i : Fin (N+1), ∑ j : Fin (N+1), if (i.val < j.val) then d i * d j else 0) =
      (∑ i : Fin N, ∑ j : Fin (N+1), if ((Fin.castSucc i).val < j.val) then d (Fin.castSucc i) * d j else 0) +
      (∑ j : Fin (N+1), if ((Fin.last N).val < j.val) then d (Fin.last N) * d j else 0) := by
    rw [Fin.sum_univ_castSucc (f := fun i => ∑ j : Fin (N+1), if (i.val < j.val) then d i * d j else 0)]
  have h_last_zero : (∑ j : Fin (N+1), if ((Fin.last N).val < j.val) then d (Fin.last N) * d j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : ¬ ((Fin.last N).val < j.val) := by simp [Fin.val_last]; omega
    rw [if_neg hj]
  rw [h_last_zero, add_zero] at h1
  have h_inner : ∀ i : Fin N, (∑ j : Fin (N+1), if ((Fin.castSucc i).val < j.val) then d (Fin.castSucc i) * d j else 0) =
      (∑ j : Fin N, if (i.val < j.val) then d (Fin.castSucc i) * d (Fin.castSucc j) else 0) +
      d (Fin.castSucc i) * d (Fin.last N) := by
    intro i
    rw [Fin.sum_univ_castSucc (f := fun j => if ((Fin.castSucc i).val < j.val) then d (Fin.castSucc i) * d j else 0)]
    simp [Fin.val_castSucc, Fin.val_last]
  have h2 : (∑ i : Fin N, ∑ j : Fin (N+1), if ((Fin.castSucc i).val < j.val) then d (Fin.castSucc i) * d j else 0) =
      (∑ i : Fin N, ((∑ j : Fin N, if i.val < j.val then d (Fin.castSucc i) * d (Fin.castSucc j) else 0) + d (Fin.castSucc i) * d (Fin.last N))) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h_inner i]
  rw [h2] at h1
  have h_swap : (∑ i : Fin N, ((∑ j : Fin N, if i.val < j.val then d (Fin.castSucc i) * d (Fin.castSucc j) else 0) + d (Fin.castSucc i) * d (Fin.last N))) =
      (∑ i : Fin N, ∑ j : Fin N, if i.val < j.val then d (Fin.castSucc i) * d (Fin.castSucc j) else 0) + ∑ i : Fin N, d (Fin.castSucc i) * d (Fin.last N) := by
    rw [Finset.sum_add_distrib]
  rw [h_swap] at h1
  rw [h1]

lemma productPoly_coeff_two {N : ℕ} (d : Fin N → ℝ) :
    (productPoly (N:=N) d).coeff 2 = pairSum d := by
  induction N with
  | zero =>
    have h : (productPoly (N:=0) d) = 1 := by unfold productPoly; simp
    rw [h]
    simp [pairSum, coeff_one]
  | succ N ih =>
    have hsplit := productPoly_succ (N:=N) d
    rw [hsplit, coeff_mul_C_add_CdX_two, ih, productPoly_coeff_one (d := fun i : Fin N => d (Fin.castSucc i))]
    rw [pairSum_succ]
    simp [Finset.sum_mul]

-- Specialize to α: d = -α
lemma zeta1_eq {N : ℕ} (α : Fin N → ℝ) :
    (productPoly (fun i => -α i)).coeff 1 = - (∑ i : Fin N, α i) := by
  rw [productPoly_coeff_one]
  simp [Finset.sum_neg_distrib]

lemma zeta2_eq {N : ℕ} (α : Fin N → ℝ) :
    (productPoly (fun i => -α i)).coeff 2 = pairSum α := by
  rw [productPoly_coeff_two]
  unfold pairSum
  congr 1
  ext i
  congr 1
  ext j
  by_cases h : i.val < j.val
  · simp [h]
  · simp [h]

/-- Diagonal decomposition: splitting into j = i, i < j, j < i. -/
private lemma sum_split_diagonal {N : ℕ} (i : Fin N) (α : Fin N → ℝ) :
    (∑ j : Fin N, α i * α j) =
      α i * α i + (∑ j : Fin N, if i.val < j.val then α i * α j else 0) +
        (∑ j : Fin N, if j.val < i.val then α i * α j else 0) := by
  have hall : ∀ j : Fin N, α i * α j =
      (if j = i then α i * α j else 0) + (if i.val < j.val then α i * α j else 0) +
        (if j.val < i.val then α i * α j else 0) := by
    intro j
    by_cases hij_eq : j = i
    · subst hij_eq; simp
    · by_cases hij_lt : i.val < j.val
      · have hjlt : ¬ (j.val < i.val) := by omega
        simp [hij_eq, hij_lt, hjlt]
      · have hjlt : j.val < i.val := by omega
        simp [hij_eq, hij_lt, hjlt]
  calc (∑ j : Fin N, α i * α j)
      = ∑ j : Fin N, ((if j = i then α i * α j else 0) +
          (if i.val < j.val then α i * α j else 0) +
          (if j.val < i.val then α i * α j else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hall j
    _ = (∑ j : Fin N, if j = i then α i * α j else 0) +
          (∑ j : Fin N, if i.val < j.val then α i * α j else 0) +
          (∑ j : Fin N, if j.val < i.val then α i * α j else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = α i * α i + (∑ j : Fin N, if i.val < j.val then α i * α j else 0) +
          (∑ j : Fin N, if j.val < i.val then α i * α j else 0) := by
          have hd : (∑ j : Fin N, if j = i then α i * α j else 0) = α i * α i := by simp
          rw [hd]

-- Sum of squares identity: Σ α_i^2 = (Σ α_i)^2 - 2 * pairSum α
lemma sum_sq_eq {N : ℕ} (α : Fin N → ℝ) :
    (∑ i : Fin N, α i ^ 2) = (∑ i : Fin N, α i) ^ 2 - 2 * pairSum α := by
  unfold pairSum
  have h1 : (∑ i : Fin N, α i) ^ 2 = ∑ i : Fin N, ∑ j : Fin N, α i * α j := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : (∑ i : Fin N, ∑ j : Fin N, α i * α j) =
      (∑ i : Fin N, α i ^ 2) + 2 * (∑ i : Fin N, ∑ j : Fin N, if i.val < j.val then α i * α j else 0) := by
    simp_rw [sum_split_diagonal]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h_diag : (∑ i : Fin N, α i * α i) = ∑ i : Fin N, α i ^ 2 := by
      congr 1; ext i; ring
    rw [h_diag]
    have h_sym : (∑ i : Fin N, ∑ j : Fin N, if j.val < i.val then α i * α j else 0) =
        (∑ i : Fin N, ∑ j : Fin N, if i.val < j.val then α i * α j else 0) := by
      have h_swap : (∑ i : Fin N, ∑ j : Fin N, if j.val < i.val then α i * α j else 0) =
          (∑ j : Fin N, ∑ i : Fin N, if j.val < i.val then α i * α j else 0) := by
        rw [Finset.sum_comm]
      rw [h_swap]
      congr 1; ext j
      congr 1; ext i
      by_cases h : j.val < i.val
      · simp [h, mul_comm]
      · simp [h]
    rw [h_sym]
    ring
  rw [h1, h2]
  ring

-- Hence Σ α² = ζ1² -2 ζ2
theorem sumAlphaSq_eq_zeta {N : ℕ} (α : Fin N → ℝ) :
    (∑ i : Fin N, α i ^ 2) = ((productPoly (fun i => -α i)).coeff 1) ^ 2 - 2 * ((productPoly (fun i => -α i)).coeff 2) := by
  rw [zeta1_eq, zeta2_eq, sum_sq_eq]
  ring


end SmoothAttain
