module
public import Continuation.Smooth.Attain.Coeff
public import Continuation.Quadratic.Foundations
public import Mathlib
@[expose] public section
noncomputable section
namespace SmoothAttain

open Polynomial QuadraticFoundations Finset Matrix

-- A) Lam definition
def lam (N : ℕ) (L : ℝ) (m : Fin N) : ℝ :=
  L / 2 + (m.val : ℝ) * L / (2 * ((N : ℝ) + 1))

lemma lam_mem_Icc {N : ℕ} {L : ℝ} (hL : 0 < L) (m : Fin N) :
    lam N L m ∈ Set.Icc (L/2) L := by
  unfold lam
  constructor
  · have h1 : 0 ≤ (m.val : ℝ) * L / (2 * ((N : ℝ) + 1)) := by positivity
    linarith
  · have hNpos : 0 < (2 : ℝ) * ((N : ℝ) + 1) := by positivity
    have h_le : (m.val : ℝ) * L / (2 * ((N : ℝ) + 1)) ≤ L / 2 := by
      have h1 : (m.val : ℝ) ≤ (N : ℝ) := by
        have : m.val < N := m.isLt
        exact_mod_cast (Nat.le_of_lt this)
      have h2 : (m.val : ℝ) * L ≤ (N : ℝ) * L := by
        apply mul_le_mul_of_nonneg_right h1 (le_of_lt hL)
      have h3 : (N : ℝ) * L / (2 * ((N : ℝ) + 1)) ≤ L / 2 := by
        have h4 : (N : ℝ) * L ≤ ((N : ℝ) + 1) * L := by nlinarith
        have hpos : 0 < 2 * ((N : ℝ) + 1) := hNpos
        calc (N : ℝ) * L / (2 * ((N : ℝ) + 1))
            ≤ ((N : ℝ) + 1) * L / (2 * ((N : ℝ) + 1)) := by
              apply div_le_div_of_nonneg_right h4 (le_of_lt hpos)
          _ = L / 2 := by field_simp
      calc (m.val : ℝ) * L / (2 * ((N : ℝ) + 1))
          ≤ (N : ℝ) * L / (2 * ((N : ℝ) + 1)) := by
            apply div_le_div_of_nonneg_right h2 (le_of_lt hNpos)
        _ ≤ L / 2 := h3
    linarith

lemma lam_pos {N : ℕ} {L : ℝ} (hL : 0 < L) (m : Fin N) : 0 < lam N L m := by
  have hmem := lam_mem_Icc hL m
  have : 0 < L / 2 := by linarith
  linarith [hmem.1]

lemma lam_ne_zero {N : ℕ} {L : ℝ} (hL : 0 < L) (m : Fin N) : lam N L m ≠ 0 := by
  have hpos := lam_pos hL m; linarith

lemma lam_lt_L {N : ℕ} {L : ℝ} (hL : 0 < L) (m : Fin N) : lam N L m < L := by
  have hNpos : 0 < (2 : ℝ) * ((N : ℝ) + 1) := by positivity
  unfold lam
  have h1 : (m.val : ℝ) * L / (2 * ((N : ℝ) + 1)) < L / 2 := by
    have h3 : (m.val : ℝ) * L < ((N : ℝ) + 1) * L := by
      have h1' : (m.val : ℝ) < ((N : ℝ) + 1 : ℝ) := by
        have : (m.val : ℝ) < (N : ℝ) := by exact_mod_cast m.isLt
        linarith
      exact mul_lt_mul_of_pos_right h1' hL
    have h4 : (m.val : ℝ) * L / (2 * ((N : ℝ) + 1)) < ((N : ℝ) + 1) * L / (2 * ((N : ℝ) + 1)) := by
      apply div_lt_div_of_pos_right h3 hNpos
    have h5 : ((N : ℝ) + 1) * L / (2 * ((N : ℝ) + 1)) = L / 2 := by field_simp
    linarith
  linarith

lemma lam_injective {N : ℕ} {L : ℝ} (hL : 0 < L) : Function.Injective (lam N L) := by
  intro i j hij
  unfold lam at hij
  have hLne : L ≠ 0 := ne_of_gt hL
  have h1 : (i.val : ℝ) * L = (j.val : ℝ) * L := by
    have h3 : (i.val : ℝ) * L / (2 * ((N : ℝ) + 1)) = (j.val : ℝ) * L / (2 * ((N : ℝ) + 1)) := by linarith
    field_simp at h3
    nlinarith
  have h2 : (i.val : ℝ) = (j.val : ℝ) := mul_right_cancel₀ hLne h1
  have h3 : i.val = j.val := by exact_mod_cast h2
  exact Fin.ext h3

lemma lam_le_L1 {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) : lam N L i ≤ L + 1 := by
  have h1 : lam N L i ≤ L := (lam_mem_Icc hL i).2
  linarith

lemma lam_nonneg {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) : 0 ≤ lam N L i := le_of_lt (lam_pos hL i)

-- natDegree bound
lemma productPoly_natDegree_le {N : ℕ} (d : Fin N → ℝ) : (productPoly d).natDegree ≤ N := by
  unfold productPoly
  have h_le : (Finset.prod Finset.univ (fun i : Fin N => (Polynomial.C (1:ℝ) + Polynomial.C (d i) * Polynomial.X))).natDegree ≤ N := by
    calc (Finset.prod Finset.univ (fun i : Fin N => (Polynomial.C (1:ℝ) + Polynomial.C (d i) * Polynomial.X))).natDegree
        ≤ ∑ i : Fin N, (Polynomial.C (1:ℝ) + Polynomial.C (d i) * Polynomial.X).natDegree := by
          apply Polynomial.natDegree_prod_le
      _ ≤ ∑ i : Fin N, 1 := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : (Polynomial.C (1:ℝ) + Polynomial.C (d i) * Polynomial.X).natDegree ≤ 1 := by
            calc (Polynomial.C (1:ℝ) + Polynomial.C (d i) * Polynomial.X).natDegree ≤ max (Polynomial.C (1:ℝ)).natDegree (Polynomial.C (d i) * Polynomial.X).natDegree := Polynomial.natDegree_add_le _ _
              _ ≤ 1 := by
                have hCdX : (Polynomial.C (d i) * Polynomial.X).natDegree ≤ 1 := by
                  calc (Polynomial.C (d i) * Polynomial.X).natDegree ≤ (Polynomial.C (d i)).natDegree + Polynomial.X.natDegree := Polynomial.natDegree_mul_le
                    _ ≤ 1 := by simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
                simp [Polynomial.natDegree_C, hCdX]
          exact h1
      _ = N := by simp
  exact h_le

-- Vandermonde matrix M_{m,j} = lam^{j+1}
def Mmat (N : ℕ) (L : ℝ) (hL : 0 < L) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => (lam N L i) ^ ((j.val : ℕ) + 1)

lemma Mmat_eq_diag_mul_vandermonde (N : ℕ) (L : ℝ) (hL : 0 < L) :
    Mmat N L hL = Matrix.diagonal (lam N L) * Matrix.vandermonde (lam N L) := by
  ext i j
  simp only [Mmat, Matrix.diagonal_mul, Matrix.vandermonde_apply, Matrix.of_apply]
  rw [pow_succ]
  ring

lemma det_Mmat_ne_zero (N : ℕ) (L : ℝ) (hL : 0 < L) : (Mmat N L hL).det ≠ 0 := by
  rw [Mmat_eq_diag_mul_vandermonde]
  rw [Matrix.det_mul]
  apply mul_ne_zero
  · rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact lam_ne_zero hL i
  · rw [Matrix.det_vandermonde]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hinj : Function.Injective (lam N L) := lam_injective hL
    have hne : lam N L j ≠ lam N L i := by
      intro heq
      have : j = i := hinj heq
      have : j.val = i.val := congrArg Fin.val this
      have hij : i < j := (Finset.mem_Ioi.mp hj)
      omega
    exact sub_ne_zero.mpr hne

-- Evaluation representation: M * ζ = p(lam) - 1
lemma eval_M_mul_zeta (N : ℕ) (L : ℝ) (hL : 0 < L) (α : Fin N → ℝ) :
    let p := productPoly (fun i => -α i)
    let zeta : Fin N → ℝ := fun j => p.coeff (j.val + 1)
    let b : Fin N → ℝ := fun i => p.eval (lam N L i) - 1
    Mmat N L hL *ᵥ zeta = b := by
  intro p zeta b
  ext i
  simp only [Mmat, b, zeta, Matrix.mulVec, Matrix.of_apply, dotProduct]
  have h_coeff0 : p.coeff 0 = 1 := productPoly_coeff_zero _
  have h_deg_lt : p.natDegree < N + 1 := by
    calc p.natDegree ≤ N := productPoly_natDegree_le _
      _ < N + 1 := by omega
  have h_eval_sum : p.eval (lam N L i) = ∑ k ∈ Finset.range (N+1), p.coeff k * (lam N L i) ^ k := by
    rw [Polynomial.eval_eq_sum_range' h_deg_lt]
  have h_range_split : (∑ k ∈ Finset.range (N+1), p.coeff k * (lam N L i) ^ k) = 1 + ∑ j : Fin N, p.coeff (j.val + 1) * (lam N L i) ^ (j.val + 1) := by
    calc (∑ k ∈ Finset.range (N+1), p.coeff k * (lam N L i) ^ k)
        = p.coeff 0 * (lam N L i) ^ 0 + ∑ k ∈ Finset.range N, p.coeff (k+1) * (lam N L i) ^ (k+1) := by
            rw [Finset.sum_range_succ']
            ring
      _ = 1 + ∑ k ∈ Finset.range N, p.coeff (k+1) * (lam N L i) ^ (k+1) := by simp [h_coeff0]
      _ = 1 + ∑ j : Fin N, p.coeff (j.val + 1) * (lam N L i) ^ (j.val + 1) := by
            congr 1
            rw [← Fin.sum_univ_eq_sum_range (fun k => p.coeff (k+1) * (lam N L i) ^ (k+1)) N]
  rw [h_eval_sum, h_range_split]
  simp only [add_sub_cancel_left]
  have h_comm : (∑ x : Fin N, lam N L i ^ (x.val + 1) * p.coeff (x.val + 1)) = ∑ j : Fin N, p.coeff (j.val + 1) * lam N L i ^ (j.val + 1) := by
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h_comm]

-- B) Coefficient bound via Cramer's rule
section CoeffBound

lemma abs_det_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, |A i j| ≤ C) : |A.det| ≤ (Nat.factorial n : ℝ) * C ^ n := by
  have h_det : A.det = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i : Fin n, A (σ i) i := Matrix.det_apply A
  rw [h_det]
  calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i : Fin n, A (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i : Fin n, A (σ i) i| := by
        apply Finset.abs_sum_le_sum_abs
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), C ^ n := by
        apply Finset.sum_le_sum
        intro σ _
        have hsign : |Equiv.Perm.sign σ • (∏ i : Fin n, A (σ i) i)| = |∏ i : Fin n, A (σ i) i| := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
          · simp [h]
          · simp [h]
        rw [hsign]
        have hprod : |∏ i : Fin n, A (σ i) i| = ∏ i : Fin n, |A (σ i) i| := by
          rw [Finset.abs_prod]
        rw [hprod]
        have hle : ∀ i : Fin n, |A (σ i) i| ≤ C := fun i => hA (σ i) i
        have hprod_le : ∏ i : Fin n, |A (σ i) i| ≤ ∏ _i : Fin n, C := by
          apply Finset.prod_le_prod₀
          · intro i _; exact abs_nonneg _
          · intro i _; exact hle i
        have hprod_const : (∏ _i : Fin n, (C : ℝ)) = C ^ n := by
          simp [Finset.prod_const, Fintype.card_fin]
        linarith
    _ = (Nat.factorial n : ℝ) * C ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
        simp [nsmul_eq_mul]

noncomputable def C_entry (N : ℕ) (L S : ℝ) : ℝ := S + 1 + (L + 1) ^ N

lemma C_entry_nonneg {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) : 0 ≤ C_entry N L S := by
  unfold C_entry
  positivity

lemma C_entry_ge_S1 {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) : S + 1 ≤ C_entry N L S := by
  unfold C_entry
  have hbase : 0 ≤ (L : ℝ) + 1 := by linarith
  have h : 0 ≤ (L + 1) ^ N := pow_nonneg hbase N
  linarith

lemma C_entry_ge_pow {N : ℕ} {L S : ℝ} (hS : 0 ≤ S) : (L + 1) ^ N ≤ C_entry N L S := by
  unfold C_entry
  have h : 0 ≤ S + 1 := by linarith
  linarith

lemma lam_pow_le_C_entry {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) (i : Fin N) (k : ℕ) (hk : k ≤ N) :
    (lam N L i) ^ k ≤ C_entry N L S := by
  have h1 : 0 ≤ lam N L i := lam_nonneg hL i
  have h2 : lam N L i ≤ L + 1 := lam_le_L1 hL i
  have h3 : (lam N L i) ^ k ≤ (L + 1) ^ k := pow_le_pow_left₀ h1 h2 k
  have h4 : (L + 1) ^ k ≤ (L + 1) ^ N := by
    apply pow_le_pow_right₀
    · linarith
    · exact hk
  have h5 : (L + 1) ^ N ≤ C_entry N L S := C_entry_ge_pow hS
  linarith

lemma M_entries_le_C {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) (i j : Fin N) :
    |Mmat N L hL i j| ≤ C_entry N L S := by
  unfold Mmat
  simp only [Matrix.of_apply]
  have hk : j.val + 1 ≤ N := by omega
  have hpow : (lam N L i) ^ (j.val + 1) ≤ C_entry N L S := lam_pow_le_C_entry hL hS i (j.val + 1) hk
  have hpow_nonneg : 0 ≤ (lam N L i) ^ (j.val + 1) := pow_nonneg (lam_nonneg hL i) _
  rw [abs_of_nonneg hpow_nonneg]
  exact hpow

lemma b_bound {N : ℕ} {L S : ℝ} {α : Fin N → ℝ} (hL : 0 < L) (hS : 0 ≤ S)
    (hp : ∀ m : Fin N, |pReal α (lam N L m)| ≤ S) (i : Fin N) :
    |(productPoly (fun i => -α i)).eval (lam N L i) - 1| ≤ C_entry N L S := by
  have h1 : |(productPoly (fun i => -α i)).eval (lam N L i)| ≤ S := by
    have h2 : pReal α (lam N L i) = (productPoly (fun i => -α i)).eval (lam N L i) := pReal_eq_productPoly_eval α (lam N L i)
    have hp' := hp i
    rw [h2] at hp'
    exact hp'
  have h2 : |(productPoly (fun i => -α i)).eval (lam N L i) - 1| ≤ S + 1 := by
    have h3 : |(productPoly (fun i => -α i)).eval (lam N L i) - 1| ≤ |(productPoly (fun i => -α i)).eval (lam N L i)| + |(1:ℝ)| := by
      calc |(productPoly (fun i => -α i)).eval (lam N L i) - 1|
          = |(productPoly (fun i => -α i)).eval (lam N L i) + (-1)| := by ring_nf
        _ ≤ |(productPoly (fun i => -α i)).eval (lam N L i)| + |(-1 : ℝ)| := abs_add_le _ _
        _ = |(productPoly (fun i => -α i)).eval (lam N L i)| + |(1:ℝ)| := by simp [abs_neg]
    have h4 : |(1:ℝ)| = 1 := by simp
    rw [h4] at h3
    linarith
  calc |_ - 1| ≤ S + 1 := h2
    _ ≤ C_entry N L S := C_entry_ge_S1 (hL := hL) (hS := hS)

lemma cramer_eq_det_smul_zeta {N : ℕ} {L : ℝ} (hL : 0 < L) (α : Fin N → ℝ) :
    let M := Mmat N L hL
    let p := productPoly (fun i => -α i)
    let zeta : Fin N → ℝ := fun j => p.coeff (j.val + 1)
    let b : Fin N → ℝ := fun i => p.eval (lam N L i) - 1
    M.cramer b = M.det • zeta := by
  intro M p zeta b
  have h_eval : M *ᵥ zeta = b := eval_M_mul_zeta N L hL α
  have h1 : M.cramer b = M.adjugate *ᵥ b := by rw [Matrix.cramer_eq_adjugate_mulVec]
  have h2 : M.adjugate *ᵥ b = M.adjugate *ᵥ (M *ᵥ zeta) := by rw [h_eval]
  have h3 : M.adjugate *ᵥ (M *ᵥ zeta) = (M.adjugate * M) *ᵥ zeta := by rw [Matrix.mulVec_mulVec]
  have h4 : (M.adjugate * M) = M.det • (1 : Matrix (Fin N) (Fin N) ℝ) := by rw [Matrix.adjugate_mul]
  have h5 : (M.det • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ zeta = M.det • zeta := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h1, h2, h3, h4, h5]

noncomputable def K_bound (N : ℕ) (L S : ℝ) (hL : 0 < L) : ℝ :=
  if hdet : (Mmat N L hL).det = 0 then 0
  else (Nat.factorial N : ℝ) * (C_entry N L S) ^ N / |(Mmat N L hL).det|

lemma K_bound_nonneg {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) : 0 ≤ K_bound N L S hL := by
  unfold K_bound
  by_cases hdet : (Mmat N L hL).det = 0
  · simp [hdet]
  · simp [hdet]
    apply div_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact pow_nonneg (C_entry_nonneg hL hS) _
    · exact abs_nonneg _

theorem coeff_bound {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) {α : Fin N → ℝ}
    (hp : ∀ m : Fin N, |pReal α (lam N L m)| ≤ S) (j : Fin N) :
    |(productPoly (fun i => -α i)).coeff (j.val + 1)| ≤ K_bound N L S hL := by
  by_cases hN0 : N = 0
  · have h_empty : IsEmpty (Fin N) := by rw [hN0]; infer_instance
    exact h_empty.elim j
  · have hdet_ne : (Mmat N L hL).det ≠ 0 := det_Mmat_ne_zero N L hL
    have hC_nonneg : 0 ≤ C_entry N L S := C_entry_nonneg hL hS
    have h_cramer : (Mmat N L hL).cramer (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1) = (Mmat N L hL).det • (fun j => (productPoly (fun i => -α i)).coeff (j.val + 1)) := cramer_eq_det_smul_zeta hL α
    have h_cramer_j : (Mmat N L hL).cramer (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1) j = (Mmat N L hL).det * (productPoly (fun i => -α i)).coeff (j.val + 1) := by
      have hj := congrFun h_cramer j
      simp only [Pi.smul_apply, smul_eq_mul] at hj
      exact hj
    have h_cramer_eq_det_update : (Mmat N L hL).cramer (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1) j = ((Mmat N L hL).updateCol j (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1)).det := by rw [Matrix.cramer_apply]
    have h_zeta_eq : (Mmat N L hL).det * (productPoly (fun i => -α i)).coeff (j.val + 1) = ((Mmat N L hL).updateCol j (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1)).det := by
      rw [← h_cramer_eq_det_update, h_cramer_j]
    have h_abs_zeta : |(productPoly (fun i => -α i)).coeff (j.val + 1)| = |((Mmat N L hL).updateCol j (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1)).det| / |(Mmat N L hL).det| := by
      have hdet_abs_ne : |(Mmat N L hL).det| ≠ 0 := by rw [abs_ne_zero]; exact hdet_ne
      have h1 : |(Mmat N L hL).det * (productPoly (fun i => -α i)).coeff (j.val + 1)| = |((Mmat N L hL).updateCol j (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1)).det| := by rw [← h_zeta_eq]
      have h2 : |(Mmat N L hL).det * (productPoly (fun i => -α i)).coeff (j.val + 1)| = |(Mmat N L hL).det| * |(productPoly (fun i => -α i)).coeff (j.val + 1)| := abs_mul _ _
      have h3 : |(Mmat N L hL).det| * |(productPoly (fun i => -α i)).coeff (j.val + 1)| = |((Mmat N L hL).updateCol j (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1)).det| := by linarith
      field_simp at h3 ⊢
      linarith
    have h_det_bound : |((Mmat N L hL).updateCol j (fun i => (productPoly (fun i => -α i)).eval (lam N L i) - 1)).det| ≤ (Nat.factorial N : ℝ) * (C_entry N L S) ^ N := by
      apply abs_det_le hC_nonneg
      intro i k
      by_cases hk : k = j
      · subst hk
        simp [Matrix.updateCol_self]
        exact b_bound hL hS hp i
      · simp [Matrix.updateCol_ne hk]
        exact M_entries_le_C hL hS i k
    have hK_eq : K_bound N L S hL = (Nat.factorial N : ℝ) * (C_entry N L S) ^ N / |(Mmat N L hL).det| := by
      unfold K_bound
      simp [hdet_ne]
    rw [h_abs_zeta, hK_eq]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    exact h_det_bound

lemma coeff_bound_two_step {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) {α : Fin 2 → ℝ}
    (hp : ∀ m : Fin 2, |pReal α (lam 2 L m)| ≤ S) :
    |(productPoly (fun i => -α i)).coeff 1| ≤ K_bound 2 L S hL ∧
    |(productPoly (fun i => -α i)).coeff 2| ≤ K_bound 2 L S hL := by
  constructor
  · have h1 := coeff_bound hL hS hp (0 : Fin 2)
    simpa using h1
  · have h2 := coeff_bound hL hS hp (1 : Fin 2)
    simpa using h2

end CoeffBound

-- C) Step-square bound (simplified)
section StepSq

noncomputable def B_bound (N : ℕ) (L S : ℝ) (hL : 0 < L) : ℝ :=
  if N = 0 then 0 else (K_bound N L S hL) ^ 2 + 2 * K_bound N L S hL

lemma B_bound_nonneg {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) : 0 ≤ B_bound N L S hL := by
  unfold B_bound
  by_cases hN0 : N = 0
  · simp [hN0]
  · simp [hN0]
    have hK_nonneg : 0 ≤ K_bound N L S hL := K_bound_nonneg hL hS
    positivity

theorem sumAlphaSq_le_B_bound {N : ℕ} {L S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) {α : Fin N → ℝ}
    (hp : ∀ m : Fin N, |pReal α (lam N L m)| ≤ S) :
    ∑ i : Fin N, (α i) ^ 2 ≤ B_bound N L S hL := by
  by_cases hN0 : N = 0
  · simp [hN0, B_bound]
  · have hK_nonneg : 0 ≤ K_bound N L S hL := K_bound_nonneg hL hS
    have h_sum_eq : (∑ i : Fin N, (α i) ^ 2) = ((productPoly (fun i => -α i)).coeff 1) ^ 2 - 2 * ((productPoly (fun i => -α i)).coeff 2) := sumAlphaSq_eq_zeta α
    have h_zeta1_bound : |(productPoly (fun i => -α i)).coeff 1| ≤ K_bound N L S hL := by
      letI : NeZero N := ⟨hN0⟩
      have h0 := coeff_bound hL hS hp (0 : Fin N)
      simpa using h0
    have h_zeta2_bound : |(productPoly (fun i => -α i)).coeff 2| ≤ K_bound N L S hL := by
      by_cases hN_lt2 : N < 2
      · have h_coeff2_zero : (productPoly (fun i : Fin N => -α i)).coeff 2 = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have h_deg : (productPoly (fun i : Fin N => -α i)).natDegree ≤ N := productPoly_natDegree_le _
          omega
        rw [h_coeff2_zero, abs_zero]
        exact hK_nonneg
      · have hN : 2 ≤ N := by omega
        letI : NeZero N := ⟨hN0⟩
        have h1 := coeff_bound hL hS hp (1 : Fin N)
        simpa [Nat.mod_eq_of_lt hN] using h1
    have h_le : (∑ i : Fin N, (α i) ^ 2) ≤ (K_bound N L S hL) ^ 2 + 2 * K_bound N L S hL := by
      rw [h_sum_eq]
      have h_zeta1_sq_le : ((productPoly (fun i => -α i)).coeff 1) ^ 2 ≤ (K_bound N L S hL) ^ 2 := by
        have h_abs : |((productPoly (fun i => -α i)).coeff 1)| ≤ K_bound N L S hL := h_zeta1_bound
        have h1 : |((productPoly (fun i => -α i)).coeff 1)| ^ 2 ≤ (K_bound N L S hL) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _) h_abs 2
        have h2 : |((productPoly (fun i => -α i)).coeff 1) ^ 2| = |((productPoly (fun i => -α i)).coeff 1)| ^ 2 := by rw [abs_pow]
        have h3 : 0 ≤ ((productPoly (fun i => -α i)).coeff 1) ^ 2 := by positivity
        have h4 : |((productPoly (fun i => -α i)).coeff 1) ^ 2| = ((productPoly (fun i => -α i)).coeff 1) ^ 2 := abs_of_nonneg h3
        linarith
      have h_zeta2_le : -2 * ((productPoly (fun i => -α i)).coeff 2) ≤ 2 * K_bound N L S hL := by
        have h_abs : |(productPoly (fun i => -α i)).coeff 2| ≤ K_bound N L S hL := h_zeta2_bound
        have h1 : -((productPoly (fun i => -α i)).coeff 2) ≤ |(productPoly (fun i => -α i)).coeff 2| := neg_le_abs _
        have h2 : -2 * ((productPoly (fun i => -α i)).coeff 2) = 2 * (-((productPoly (fun i => -α i)).coeff 2)) := by ring
        rw [h2]
        have h3 : 2 * (-((productPoly (fun i => -α i)).coeff 2)) ≤ 2 * |(productPoly (fun i => -α i)).coeff 2| := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
        have h4 : 2 * |(productPoly (fun i => -α i)).coeff 2| ≤ 2 * K_bound N L S hL := by
          apply mul_le_mul_of_nonneg_left h_abs (by positivity)
        linarith
      linarith
    have hB_eq : B_bound N L S hL = (K_bound N L S hL) ^ 2 + 2 * K_bound N L S hL := by
      unfold B_bound; simp [hN0]
    rw [hB_eq]
    exact h_le

end StepSq


end SmoothAttain
