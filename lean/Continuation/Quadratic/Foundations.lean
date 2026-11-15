module

public import Benchmarks.Quadratic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Tactic

open Polynomial Finset Real

/-! Polynomial recurrence, degree bounds, the zero-increment product identity,
and odd-Chebyshev algebra. The spectral risk and minimax identities remain open. -/
@[expose] public section
noncomputable section

namespace QuadraticFoundations

-- Section 1: polynomial recurrence (paper 5.2 eq:polynomials)
def pIter (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n+1 =>
    if h : n < N then
      let pn := pIter N d T n
      let sumTerm : ℝ[X] := ∑ j : Fin n, C (T ⟨n, h⟩ ⟨j.val, by omega⟩) * pIter N d T j.val
      (C 1 + C (d ⟨n, h⟩) * X) * pn + X * sumTerm
    else 1

def pN (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) : ℝ[X] := pIter N d T N

theorem pIter_eval_zero (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) (n : ℕ) (hn : n ≤ N) :
    (pIter N d T n).eval 0 = 1 := by
  induction n with
  | zero => simp [pIter]
  | succ n ih =>
    have hn' : n ≤ N := by omega
    have hlt : n < N := by omega
    simp only [pIter, dite_eq_left hlt] at *
    simp [ih hn']

theorem pIter_natDegree_le (N : ℕ) (d : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ) :
    ∀ n, n ≤ N → (pIter N d T n).natDegree ≤ n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [pIter]
    | n+1 =>
      have hlt : n < N := by omega
      simp only [pIter, dite_eq_left hlt]
      have ih_n : (pIter N d T n).natDegree ≤ n := ih n (by omega) (by omega)
      have hCX : (C (1:ℝ) + C (d ⟨n, hlt⟩) * X).natDegree ≤ 1 := by
        have : (C (d ⟨n, hlt⟩) * X : ℝ[X]).natDegree ≤ 1 := by
          calc (C (d ⟨n, hlt⟩) * X).natDegree ≤ (C (d ⟨n, hlt⟩)).natDegree + X.natDegree := natDegree_mul_le
            _ ≤ 1 := by simp [natDegree_C, natDegree_X]
        calc (C 1 + C (d ⟨n, hlt⟩) * X).natDegree ≤ max (C (1:ℝ)).natDegree (C (d ⟨n, hlt⟩) * X).natDegree := natDegree_add_le _ _
          _ ≤ 1 := by simp [natDegree_C, this]
      have h1 : ((C (1:ℝ) + C (d ⟨n, hlt⟩) * X) * pIter N d T n).natDegree ≤ n+1 := by
        calc _ ≤ (C 1 + C (d ⟨n, hlt⟩) * X).natDegree + (pIter N d T n).natDegree := natDegree_mul_le
          _ ≤ 1 + n := by omega
          _ = n+1 := by omega
      have h2 : (X * (∑ j : Fin n, (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d T j.val : ℝ[X]))).natDegree ≤ n := by
        by_cases hn0 : n = 0
        · simp [hn0]
        · have hsum : (∑ j : Fin n, (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d T j.val : ℝ[X])).natDegree ≤ n-1 := by
            calc _ ≤ Finset.sup Finset.univ (fun j : Fin n => (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d T j.val : ℝ[X]).natDegree) := natDegree_sum_le _ _
              _ ≤ n-1 := by
                apply Finset.sup_le
                intro j _
                have hj : (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d T j.val : ℝ[X]).natDegree ≤ j.val := by
                  calc _ ≤ (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩)).natDegree + (pIter N d T j.val).natDegree := natDegree_mul_le
                    _ ≤ j.val := by
                      have hj_le : (pIter N d T j.val).natDegree ≤ j.val := ih j.val (by omega) (by omega)
                      simp [natDegree_C, hj_le]
                omega
          calc (X * (∑ j : Fin n, (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d T j.val : ℝ[X]))).natDegree
              ≤ X.natDegree + (∑ j : Fin n, (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d T j.val : ℝ[X])).natDegree := natDegree_mul_le
            _ ≤ 1 + (n-1) := by simp [natDegree_X, hsum]
            _ = n := by omega
      calc ((C 1 + C (d ⟨n, hlt⟩) * X) * pIter N d T n + X * (∑ j : Fin n, (C (T ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d T j.val : ℝ[X]))).natDegree
          ≤ max ((C 1 + C (d ⟨n, hlt⟩) * X) * pIter N d T n).natDegree (X * (∑ j, _)).natDegree := natDegree_add_le _ _
        _ ≤ n+1 := by omega

-- Section 2: product specialization (paper eq:product)
export QuadraticBenchmark (productPoly productPoly_eval_zero productPoly_eval)

theorem pIter_T_zero_eq_product (N : ℕ) (d : Fin N → ℝ) (n : ℕ) (hn : n ≤ N) :
    pIter N d (0 : Matrix (Fin N) (Fin N) ℝ) n =
      Finset.prod Finset.univ (fun i : Fin n => (C (1:ℝ) + C (d ⟨i.val, by omega⟩) * X)) := by
  induction n with
  | zero => simp [pIter]
  | succ n ih =>
    have hlt : n < N := by omega
    have ih' := ih (by omega)
    have hsum : (∑ j : Fin n, C ((0 : Matrix (Fin N) (Fin N) ℝ) ⟨n, hlt⟩ ⟨j.val, by omega⟩) * pIter N d 0 j.val) = 0 := by simp
    have hprod : Finset.prod Finset.univ (fun i : Fin (n+1) => (C (1:ℝ) + C (d ⟨i.val, by omega⟩) * X)) = (Finset.prod Finset.univ (fun i : Fin n => (C (1:ℝ) + C (d ⟨i.val, by omega⟩) * X))) * (C (1:ℝ) + C (d ⟨n, hlt⟩) * X) := by
      rw [Fin.prod_univ_castSucc]
      simp
    simp only [pIter, dite_eq_left hlt, ih', hsum, mul_zero, add_zero, hprod]
    ring

theorem pN_T_zero_eq_productPoly (N : ℕ) (d : Fin N → ℝ) :
    pN N d (0 : Matrix (Fin N) (Fin N) ℝ) = productPoly d := by
  unfold pN productPoly
  have h := pIter_T_zero_eq_product N d N (le_refl N)
  rw [h]

-- Section 3: Chebyshev via Mathlib T
noncomputable def chebM (N : ℕ) : ℝ[X] := Polynomial.Chebyshev.T ℝ ((2 * (N : ℤ) + 1))

theorem chebM_degree (N : ℕ) : (chebM N).degree = ((2 * N + 1 : ℕ) : WithBot ℕ) := by
  unfold chebM
  exact Polynomial.Chebyshev.degree_T (R:=ℝ) (2 * (N : ℤ) + 1)

theorem chebM_natDegree (N : ℕ) : (chebM N).natDegree = 2 * N + 1 := by
  unfold chebM
  exact Polynomial.Chebyshev.natDegree_T (R:=ℝ) (2 * (N : ℤ) + 1)

theorem chebM_eval_cos (N : ℕ) (θ : ℝ) : (chebM N).eval (Real.cos θ) = Real.cos ((2 * (N : ℝ) + 1) * θ) := by
  unfold chebM
  have h := Polynomial.Chebyshev.T_real_cos θ (2 * (N : ℤ) + 1)
  have heq : ((2 * (N : ℤ) + 1 : ℤ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
  rw [heq] at h
  exact h

theorem chebM_eval_neg (N : ℕ) (x : ℝ) : (chebM N).eval (-x) = - (chebM N).eval x := by
  unfold chebM
  have h := Polynomial.Chebyshev.T_eval_neg (R:=ℝ) (2 * (N : ℤ) + 1) x
  have hodd : Odd (2 * (N : ℤ) + 1) := ⟨N, by omega⟩
  have hpow : (2 * (N : ℤ) + 1).negOnePow = -1 := Int.negOnePow_odd _ hodd
  rw [hpow] at h
  simpa using h

theorem chebM_comp_neg (N : ℕ) : (chebM N).comp (-X) = - (chebM N) := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_neg, eval_X, chebM_eval_neg, eval_neg, eval_comp, eval_X]

theorem chebM_eval_zero (N : ℕ) : (chebM N).eval (0 : ℝ) = 0 := by
  have hodd : Odd (2 * (N : ℤ) + 1) := ⟨N, by omega⟩
  have h := Polynomial.Chebyshev.T_eval_zero_of_odd (R:=ℝ) hodd
  unfold chebM
  simpa using h

theorem chebM_dvd_X (N : ℕ) : (X : ℝ[X]) ∣ chebM N := by
  rw [X_dvd_iff]
  have h : (chebM N).coeff 0 = (chebM N).eval (0 : ℝ) := by simp [coeff_zero_eq_eval_zero]
  rw [h, chebM_eval_zero]

noncomputable def chebM_s (N : ℕ) : ℝ[X] :=
  Classical.choose (dvd_def.mp (chebM_dvd_X N))

theorem chebM_eq_X_mul_s (N : ℕ) : chebM N = X * chebM_s N := by
  unfold chebM_s
  have h := Classical.choose_spec (dvd_def.mp (chebM_dvd_X N))
  exact h

theorem neg_X_pow (n : ℕ) : (-X : ℝ[X]) ^ n = C ((-1 : ℝ) ^ n) * X ^ n := by
  have h : (-X : ℝ[X]) = C (-1) * X := by simp
  rw [h]
  have hcomm : Commute (C (-1 : ℝ)) (X : ℝ[X]) := by
    rw [Commute, SemiconjBy]
    simp [mul_comm]
  rw [hcomm.mul_pow]
  simp [C_pow]

theorem comp_neg_X_coeff (p : ℝ[X]) (k : ℕ) : (p.comp (-X)).coeff k = (-1 : ℝ) ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial n a =>
    have h1 : (monomial n a).comp (-X) = C a * (-X) ^ n := by
      have : monomial n a = C a * X ^ n := by rw [C_mul_X_pow_eq_monomial]
      rw [this]
      simp [mul_comp, C_comp, pow_comp, X_comp]
    have h2 : (-X : ℝ[X]) ^ n = C ((-1 : ℝ) ^ n) * X ^ n := neg_X_pow n
    rw [h1, h2]
    have h3 : C a * (C ((-1 : ℝ) ^ n) * X ^ n) = C (a * (-1 : ℝ) ^ n) * X ^ n := by
      simp [C_mul, mul_assoc]
    rw [h3]
    have h4 : C (a * (-1 : ℝ) ^ n) * X ^ n = Polynomial.monomial n (a * (-1 : ℝ) ^ n) := by
      rw [C_mul_X_pow_eq_monomial]
    rw [h4]
    rw [Polynomial.coeff_monomial]
    rw [Polynomial.coeff_monomial]
    by_cases hnk : n = k
    · subst hnk
      simp [mul_comm]
    · have h1 : ¬ (n = k) := hnk
      rw [if_neg h1, if_neg h1]
      simp

end QuadraticFoundations
