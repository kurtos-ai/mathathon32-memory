module
/-
Source fidelity note (ext:thm:near + Appendix K explicit constants):
Finite horizon N, predetermined strictly lower-triangular real gain A with
| A | entrywise absolute value, J = (L0+eps0)|A| strictly lower-triangular.
Define finite Neumann majorant h_A = (I - J)^{-1} 1 as finite sum due to
nilpotency: J^{N}=0, so (I-J)^{-1}= Σ_{k=0}^{N-1} J^{k}. Hence h finite,
nonnegative when L0+eps0 ≥ 0. Response entries p_A(λ), r^{A}_{N,j}(λ) are
polynomials in λ (continuous), so |p_A|, |r_{N,j}| continuous on compact
I=[0,L0]; by IsCompact/Icc they attain maxima and are bounded. Define
  π_A = max_{λ∈[0,L0]} |p_A(λ)|,
  β_A = Σ_{j<N} max_{λ∈[0,L0]} |r^{A}_{N,j}(λ)|·(h_A)_j,
  κ_A = 1/2 (h_A)_N^2 + L0 π_A β_A + 1/2 L0 ε0 β_A^2,
with finiteness/nonnegativity. No minimax value is defined as a formula;
no quadratic factorization/Chebyshev bound is attempted. Where a maximum
value is needed we quantify over a supplied majorant function M ≥ sup,
or take sSup of the bounded image — both are source-faithful and avoid
assuming attainment when stating bounds.
-/

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

namespace NearQuadratic

open Finset BigOperators Polynomial

/-! ### Finite strictly lower-triangular matrices and Neumann sum -/

section Neumann

variable {N : ℕ}

-- Strictly lower-triangular: j ≥ i ⇒ M i j = 0
def IsStrictLowerTri' (M : Fin N → Fin N → ℝ) : Prop :=
  ∀ i j : Fin N, j.val ≥ i.val → M i j = 0

def IsNonnegMat' (M : Fin N → Fin N → ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

-- Entrywise absolute matrix
noncomputable def absMat (A : Fin N → Fin N → ℝ) : Fin N → Fin N → ℝ :=
  fun i j => |A i j|

lemma absMat_nonneg (A : Fin N → Fin N → ℝ) : IsNonnegMat' (absMat A) := fun _ _ => abs_nonneg _

lemma absMat_strictLower {A : Fin N → Fin N → ℝ} (hA : IsStrictLowerTri' A) :
    IsStrictLowerTri' (absMat A) := fun i j h => by simp [absMat, hA i j h]

lemma IsStrictLowerTri'_zero : IsStrictLowerTri' (N:=N) (fun _ _ => (0:ℝ)) := fun _ _ _ => rfl

-- Matrix-vector product
noncomputable def matVecMul' (M : Fin N → Fin N → ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ∑ j : Fin N, M i j * v j

lemma matVecMul'_nonneg {M : Fin N → Fin N → ℝ} {v : Fin N → ℝ}
    (hM : IsNonnegMat' M) (hv : ∀ j, 0 ≤ v j) (i : Fin N) :
    0 ≤ matVecMul' M v i := by
  unfold matVecMul'
  apply Finset.sum_nonneg
  intro j _; exact mul_nonneg (hM _ _) (hv _)

-- Powers of strictly lower-triangular matrix acting on vectors
noncomputable def JpowVec' : ℕ → (Fin N → Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)
  | 0, _, v => v
  | k+1, J, v => matVecMul' J (JpowVec' k J v)

-- Nilpotency: J^k v has support in indices ≥ k
lemma JpowVec'_zero_of_lt {J : Fin N → Fin N → ℝ} (hJ : IsStrictLowerTri' J)
    (v : Fin N → ℝ) : ∀ (k : ℕ) (i : Fin N), i.val < k → JpowVec' (N:=N) k J v i = 0 := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    simp only [JpowVec', matVecMul']
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : J i j = 0
    · simp [hj]
    · have hlt : j.val < i.val := by
        by_contra hge
        push Not at hge
        have := hJ i j (by omega)
        simp [this] at hj
      have hjk : j.val < k := by omega
      have := ih j hjk
      simp [this]

lemma JpowVec'_N_zero {J : Fin N → Fin N → ℝ} (hJ : IsStrictLowerTri' J)
    (v : Fin N → ℝ) : JpowVec' (N:=N) N J v = fun _ => 0 := by
  funext i
  exact JpowVec'_zero_of_lt hJ v N i i.isLt

-- Finite Neumann sum Σ_{k=0}^{N-1} J^k v  (N terms, finite)
noncomputable def neumannSum' (J : Fin N → Fin N → ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ∑ k ∈ Finset.range N, JpowVec' (N:=N) k J v i

lemma neumannSum'_finite (J : Fin N → Fin N → ℝ) (v : Fin N → ℝ) (i : Fin N) :
    neumannSum' J v i = ∑ k ∈ Finset.range N, JpowVec' (N:=N) k J v i := rfl

lemma neumannSum'_nonneg {J : Fin N → Fin N → ℝ} {v : Fin N → ℝ}
    (hJ : IsNonnegMat' J) (hv : ∀ j, 0 ≤ v j) (i : Fin N) :
    0 ≤ neumannSum' (N:=N) J v i := by
  unfold neumannSum'
  apply Finset.sum_nonneg
  intro k _
  have : ∀ k, ∀ i : Fin N, 0 ≤ JpowVec' (N:=N) k J v i := by
    intro k; induction k with
    | zero => intro i; simp [JpowVec', hv i]
    | succ k ih => intro i; simp only [JpowVec']; exact matVecMul'_nonneg hJ ih i
  exact this k i

-- h_A definition: (I - L|A|)^{-1} 1  = finite Neumann sum
noncomputable def hA_of (A : Fin N → Fin N → ℝ) (L : ℝ) : Fin N → ℝ :=
  neumannSum' (N:=N) (fun i j => L * |A i j|) (fun _ => (1:ℝ))

lemma hA_of_nonneg {A : Fin N → Fin N → ℝ} {L : ℝ} (hL : 0 ≤ L) (i : Fin N) :
    0 ≤ hA_of (N:=N) A L i := by
  unfold hA_of
  have hJ : IsNonnegMat' (fun i j : Fin N => L * |A i j|) := fun a b => mul_nonneg hL (abs_nonneg _)
  exact neumannSum'_nonneg hJ (fun _ => zero_le_one) i

lemma hA_of_finite (A : Fin N → Fin N → ℝ) (L : ℝ) (i : Fin N) :
    hA_of (N:=N) A L i = ∑ k ∈ Finset.range N, JpowVec' (N:=N) k (fun i j => L * |A i j|) (fun _ => (1:ℝ)) i := rfl

end Neumann

/-! ### Continuous polynomial response entries and max-on-[0,L0] bounds -/

section PolyMax

variable {L0 : ℝ}

-- A polynomial p : ℝ → ℝ obtained from a Polynomial ℝ is continuous
lemma poly_continuous (p : ℝ[X]) : Continuous (fun x : ℝ => p.eval x) :=
  p.continuous

-- The interval [0, L0] is compact
lemma isCompact_Icc_zero_L0 (hL0 : 0 ≤ L0) : IsCompact (Set.Icc (0:ℝ) L0) :=
  isCompact_Icc

-- Nonempty when L0 ≥ 0
lemma nonempty_Icc_zero_L0 (hL0 : 0 ≤ L0) : (Set.Icc (0:ℝ) L0).Nonempty :=
  ⟨0, Set.mem_Icc.mpr ⟨le_rfl, hL0⟩⟩

-- Existence of maximum for continuous function on compact Icc (extreme value)
theorem continuous_exists_isMaxOn_Icc (f : ℝ → ℝ) (hL0 : 0 ≤ L0)
    (hf : ContinuousOn f (Set.Icc (0:ℝ) L0)) :
    ∃ x ∈ Set.Icc (0:ℝ) L0, ∀ y ∈ Set.Icc (0:ℝ) L0, f y ≤ f x :=
  IsCompact.exists_isMaxOn (isCompact_Icc_zero_L0 hL0) (nonempty_Icc_zero_L0 hL0) hf

-- Polynomial response entries are bounded on [0,L0]
lemma poly_bddAbove_Icc (p : ℝ[X]) (hL0 : 0 ≤ L0) :
    BddAbove ((fun x : ℝ => p.eval x) '' Set.Icc (0:ℝ) L0) := by
  have hcont : ContinuousOn (fun x : ℝ => p.eval x) (Set.Icc (0:ℝ) L0) :=
    (poly_continuous p).continuousOn
  exact (isCompact_Icc_zero_L0 hL0).bddAbove_image hcont

-- The absolute value of a polynomial is continuous and bounded on Icc
lemma absPoly_bddAbove_Icc (p : ℝ[X]) (hL0 : 0 ≤ L0) :
    BddAbove ((fun x : ℝ => |p.eval x|) '' Set.Icc (0:ℝ) L0) := by
  have hcont : ContinuousOn (fun x : ℝ => |p.eval x|) (Set.Icc (0:ℝ) L0) := by
    have hc : Continuous (fun x : ℝ => |p.eval x|) := (poly_continuous p).abs
    exact hc.continuousOn
  exact (isCompact_Icc_zero_L0 hL0).bddAbove_image hcont

lemma absPoly_nonempty_image (p : ℝ[X]) (hL0 : 0 ≤ L0) :
    ((fun x : ℝ => |p.eval x|) '' Set.Icc (0:ℝ) L0).Nonempty :=
  Set.Nonempty.image _ (nonempty_Icc_zero_L0 hL0)

/- Define π_A as sSup of |p(λ)| on [0,L0] -/
noncomputable def pi_of_poly (p : ℝ[X]) (L0 : ℝ) : ℝ :=
  sSup ((fun x : ℝ => |p.eval x|) '' Set.Icc (0:ℝ) L0)

lemma pi_of_poly_nonneg (p : ℝ[X]) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    0 ≤ pi_of_poly p L0 := by
  unfold pi_of_poly
  have hbdd := absPoly_bddAbove_Icc p hL0
  have h_le : |p.eval (0:ℝ)| ≤ sSup ((fun x : ℝ => |p.eval x|) '' Set.Icc (0:ℝ) L0) :=
    le_csSup hbdd ⟨0, Set.mem_Icc.mpr ⟨le_rfl, hL0⟩, rfl⟩
  linarith [abs_nonneg (p.eval (0:ℝ))]

-- Uniform bound: ∀ λ∈[0,L0], |p(λ)| ≤ π_A
lemma pi_of_poly_is_ub (p : ℝ[X]) (L0 : ℝ) (hL0 : 0 ≤ L0) (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) L0) :
    |p.eval lam| ≤ pi_of_poly p L0 := by
  unfold pi_of_poly
  exact le_csSup (absPoly_bddAbove_Icc p hL0) ⟨lam, hlam, rfl⟩

-- Attainment: ∃ lam* ∈ [0,L0] attaining π_A, with equality |p(lam*)| = π_A
lemma pi_of_poly_attains (p : ℝ[X]) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∃ lamStar ∈ Set.Icc (0:ℝ) L0, (∀ lam ∈ Set.Icc (0:ℝ) L0, |p.eval lam| ≤ |p.eval lamStar|)
      ∧ |p.eval lamStar| = pi_of_poly p L0 := by
  have hcont : ContinuousOn (fun x : ℝ => |p.eval x|) (Set.Icc (0:ℝ) L0) := by
    have hc : Continuous (fun x : ℝ => |p.eval x|) := (poly_continuous p).abs
    exact hc.continuousOn
  obtain ⟨lamStar, hmem, hmax⟩ := continuous_exists_isMaxOn_Icc _ hL0 hcont
  refine ⟨lamStar, hmem, hmax, ?_⟩
  apply le_antisymm
  · exact pi_of_poly_is_ub p L0 hL0 lamStar hmem
  · apply csSup_le
    · exact absPoly_nonempty_image p hL0
    · intro y hy
      obtain ⟨lam, hlam, rfl⟩ := hy
      exact hmax lam hlam

end PolyMax

/-! ### β and κ explicit constants -/

section BetaKappa

variable {N : ℕ}

-- β_A = Σ_{j<N} max_{[0,L0]} |r_{N,j}(λ)| · (h_A)_j
-- We take rPolys : Fin N → ℝ[X] and hA : Fin N → ℝ
noncomputable def beta_of (rPolys : Fin N → ℝ[X]) (hA : Fin N → ℝ) (L0 : ℝ) : ℝ :=
  ∑ j : Fin N, pi_of_poly (rPolys j) L0 * hA j

lemma beta_of_nonneg {rPolys : Fin N → ℝ[X]} {hA : Fin N → ℝ} {L0 : ℝ}
    (hL0 : 0 ≤ L0) (hhA : ∀ j, 0 ≤ hA j) :
    0 ≤ beta_of (N:=N) rPolys hA L0 := by
  unfold beta_of
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (pi_of_poly_nonneg _ _ hL0) (hhA _)

lemma beta_of_finite (rPolys : Fin N → ℝ[X]) (hA : Fin N → ℝ) (L0 : ℝ) :
    beta_of (N:=N) rPolys hA L0 = ∑ j : Fin N, pi_of_poly (rPolys j) L0 * hA j := rfl

-- κ_A = 1/2 h_N^2 + L0 π β + 1/2 L0 ε0 β^2
noncomputable def kappa_of (hN piA betaA L0 eps0 : ℝ) : ℝ :=
  1/2 * hN ^ 2 + L0 * piA * betaA + 1/2 * L0 * eps0 * betaA ^ 2

lemma kappa_of_nonneg {hN piA betaA L0 eps0 : ℝ}
    (hL0 : 0 ≤ L0) (heps0 : 0 ≤ eps0) (hpi : 0 ≤ piA) (hbeta : 0 ≤ betaA) :
    0 ≤ kappa_of hN piA betaA L0 eps0 := by
  unfold kappa_of; positivity

lemma kappa_of_finite (hN piA betaA L0 eps0 : ℝ) :
    kappa_of hN piA betaA L0 eps0 = 1/2 * hN ^ 2 + L0 * piA * betaA + 1/2 * L0 * eps0 * betaA ^ 2 := rfl

-- Generic supplied-max version: if M_p ≥ max |p| and M_r j ≥ max |r_j|, define π,β with Ms
noncomputable def pi_of_supplied (M_p : ℝ) : ℝ := M_p
noncomputable def beta_of_supplied (M_r : Fin N → ℝ) (hA : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, M_r j * hA j

lemma beta_supplied_nonneg {M_r : Fin N → ℝ} {hA : Fin N → ℝ}
    (hM : ∀ j, 0 ≤ M_r j) (hhA : ∀ j, 0 ≤ hA j) :
    0 ≤ beta_of_supplied (N:=N) M_r hA := by
  unfold beta_of_supplied
  apply Finset.sum_nonneg; intro j _; exact mul_nonneg (hM _) (hhA _)

-- Supplied bound implies true max bound: if M_r j ≥ sup_{[0,L0]}|r_j|, then β_supplied ≥ β_true when h≥0
lemma beta_supplied_ge_beta {rPolys : Fin N → ℝ[X]} {hA : Fin N → ℝ} {L0 : ℝ} {M_r : Fin N → ℝ}
    (hL0 : 0 ≤ L0) (hhA : ∀ j, 0 ≤ hA j)
    (hM_ge : ∀ j, pi_of_poly (rPolys j) L0 ≤ M_r j) :
    beta_of (N:=N) rPolys hA L0 ≤ beta_of_supplied M_r hA := by
  unfold beta_of beta_of_supplied
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hM_ge _) (hhA _)

-- kappa with supplied beta is upper bound
lemma kappa_of_mono_beta {hN piA L0 eps0 : ℝ} {b1 b2 : ℝ}
    (hL0 : 0 ≤ L0) (heps0 : 0 ≤ eps0) (hpi : 0 ≤ piA) (hb1 : 0 ≤ b1) (hle : b1 ≤ b2) :
    kappa_of hN piA b1 L0 eps0 ≤ kappa_of hN piA b2 L0 eps0 := by
  unfold kappa_of
  have h1 : L0 * piA * b1 ≤ L0 * piA * b2 := by
    apply mul_le_mul_of_nonneg_left hle
    exact mul_nonneg hL0 hpi
  have h2 : 1/2 * L0 * eps0 * b1 ^ 2 ≤ 1/2 * L0 * eps0 * b2 ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ hb1 hle 2
  linarith

-- Uniform max bound via supplied majorant: generic version avoids assuming max exists
theorem pi_beta_uniform_bound {rPolys : Fin N → ℝ[X]} {hA : Fin N → ℝ} {L0 : ℝ}
    (hL0 : 0 ≤ L0) (M_r : Fin N → ℝ)
    (hM_ub : ∀ j (lam : ℝ), lam ∈ Set.Icc (0:ℝ) L0 → |(rPolys j).eval lam| ≤ M_r j) :
    ∀ j (lam : ℝ), lam ∈ Set.Icc (0:ℝ) L0 → |(rPolys j).eval lam| ≤ pi_of_poly (rPolys j) L0
    ∧ pi_of_poly (rPolys j) L0 ≤ M_r j := by
  intro j lam hlam
  constructor
  · exact pi_of_poly_is_ub _ L0 hL0 lam hlam
  · unfold pi_of_poly
    apply csSup_le
    · exact absPoly_nonempty_image (rPolys j) hL0
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := hy
      exact hM_ub j t ht

end BetaKappa

/-! ### Finiteness summary -/

section Summary

variable {N : ℕ}

-- Finite-state (Fin N) summary: terminal at last index N-1
theorem explicit_consts_all_finite (A : Fin N → Fin N → ℝ) (L0 eps0 : ℝ)
    (pA : ℝ[X]) (rA : Fin N → ℝ[X]) (hL0 : 0 ≤ L0) (heps0 : 0 ≤ eps0) :
    let hA := hA_of (N:=N) A (L0 + eps0)
    let piA := pi_of_poly pA L0
    let betaA := beta_of (N:=N) rA hA L0
    let kappaA := kappa_of (if h : N > 0 then hA ⟨N-1, by omega⟩ else 0) piA betaA L0 eps0
    (∀ i, 0 ≤ hA i) ∧ 0 ≤ piA ∧ 0 ≤ betaA ∧ 0 ≤ kappaA := by
  simp only
  have hL : 0 ≤ L0 + eps0 := by linarith
  constructor
  · intro i; exact hA_of_nonneg hL i
  constructor
  · exact pi_of_poly_nonneg pA L0 hL0
  constructor
  · exact beta_of_nonneg hL0 (fun j => hA_of_nonneg hL j)
  · exact kappa_of_nonneg hL0 heps0 (pi_of_poly_nonneg pA L0 hL0) (beta_of_nonneg hL0 (fun j => hA_of_nonneg hL j))

-- Appendix K source-indexed terminal API: states 0..N (Fin (N+1)), response sum j < N,
-- terminal h at index N, kappa uses (h_A)_N. This matches ext:thm:near Appendix K
-- where h_A = (I-(L0+eps0)|A|)^{-1} 1 in ℝ^{N+1}, π_A = max_{[0,L0]}|p_A|,
-- β_A = Σ_{j<N} max_{[0,L0]}|r_{N,j}|·(h_A)_j, κ_A = 1/2 (h_A)_N^2 + L0 π_A β_A + 1/2 L0 ε0 β_A^2.
noncomputable def beta_of_terminal {N : ℕ} (rPolys : Fin N → ℝ[X]) (hA : Fin (N+1) → ℝ) (L0 : ℝ) : ℝ :=
  ∑ j : Fin N, pi_of_poly (rPolys j) L0 * hA ⟨j.val, by omega⟩

lemma beta_of_terminal_nonneg {N : ℕ} {rPolys : Fin N → ℝ[X]} {hA : Fin (N+1) → ℝ} {L0 : ℝ}
    (hL0 : 0 ≤ L0) (hhA : ∀ i, 0 ≤ hA i) : 0 ≤ beta_of_terminal (N:=N) rPolys hA L0 := by
  unfold beta_of_terminal
  apply Finset.sum_nonneg; intro j _; exact mul_nonneg (pi_of_poly_nonneg _ _ hL0) (hhA _)

theorem explicit_consts_terminal_finite {N : ℕ} (A : Fin (N+1) → Fin (N+1) → ℝ) (L0 eps0 : ℝ)
    (pA : ℝ[X]) (rA : Fin N → ℝ[X]) (hL0 : 0 ≤ L0) (heps0 : 0 ≤ eps0) :
    let hA := hA_of (N:=N+1) A (L0 + eps0)
    let piA := pi_of_poly pA L0
    let betaA := beta_of_terminal (N:=N) rA hA L0
    let hN : ℝ := hA ⟨N, by omega⟩
    let kappaA := kappa_of hN piA betaA L0 eps0
    (∀ i, 0 ≤ hA i) ∧ 0 ≤ piA ∧ 0 ≤ betaA ∧ 0 ≤ kappaA := by
  simp only
  have hL : 0 ≤ L0 + eps0 := by linarith
  constructor
  · intro i; exact hA_of_nonneg hL i
  constructor
  · exact pi_of_poly_nonneg pA L0 hL0
  constructor
  · exact beta_of_terminal_nonneg hL0 (fun i => hA_of_nonneg hL i)
  · exact kappa_of_nonneg hL0 heps0 (pi_of_poly_nonneg pA L0 hL0) (beta_of_terminal_nonneg hL0 (fun i => hA_of_nonneg hL i))

end Summary

end NearQuadratic
