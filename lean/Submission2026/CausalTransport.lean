module
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace CausalTransport
open Matrix
open scoped BigOperators

/-- Causality includes the zero diagonal. -/
def StrictLower {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i.val ≤ j.val → M i j = 0

lemma power_entry_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : StrictLower M) (k : ℕ) (i j : Fin n) (hij : i.val < j.val+k) :
    (M^k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; omega
    simp [hne]
  | succ k ih =>
    rw [pow_succ,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hil : i.val < l.val+k
    · rw [ih i l hil,zero_mul]
    · rw [hM l j (by omega),mul_zero]

/-- Every strictly causal n-by-n matrix is nilpotent at exponent n. -/
theorem power_dimension_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : StrictLower M) : M^n = 0 := by
  ext i j
  exact power_entry_zero M hM n i j (by omega)

/-- The finite causal resolvent needs no small-gain hypothesis. -/
def resolvent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k ∈ Finset.range n, M^k

theorem resolvent_right_inverse {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : StrictLower M) : resolvent M * (1-M) = 1 := by
  rw [resolvent,geom_sum_mul_neg,power_dimension_zero M hM,sub_zero]

theorem resolvent_left_inverse {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : StrictLower M) : (1-M)*resolvent M = 1 := by
  rw [resolvent,mul_neg_geom_sum,power_dimension_zero M hM,sub_zero]

theorem inverse_eq_resolvent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : StrictLower M) : (1-M)⁻¹ = resolvent M :=
  Matrix.inv_eq_right_inv (resolvent_left_inverse M hM)

lemma power_nonnegative {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) : ∀ i j, 0 ≤ (M^k) i j := by
  induction k with
  | zero => intro i j; simp only [pow_zero,Matrix.one_apply]; split <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ,Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hM l j))

lemma resolvent_nonnegative {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) : ∀ i j, 0 ≤ resolvent M i j := by
  intro i j
  simp only [resolvent,Matrix.sum_apply]
  exact Finset.sum_nonneg (fun k _ => power_nonnegative M hM k i j)

lemma mulVec_monotone {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (x y : Fin n → ℝ) (hxy : ∀ i, x i ≤ y i) :
    ∀ i, (M*ᵥx) i ≤ (M*ᵥy) i := by
  intro i
  simp only [Matrix.mulVec,dotProduct]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hM i j))

/-- A causal componentwise feedback inequality has a finite resolvent bound, with
no upper restriction on the nonnegative coefficients. -/
theorem feedback_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hcausal : StrictLower M) (hnonneg : ∀ i j, 0 ≤ M i j)
    (x v : Fin n → ℝ) (h : ∀ i, x i ≤ v i+(M*ᵥx) i) :
    ∀ i, x i ≤ (resolvent M*ᵥv) i := by
  have hRM : resolvent M*M = resolvent M-1 := by
    have he := resolvent_right_inverse M hcausal
    rw [mul_sub,mul_one] at he
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp he).symm
  have hm := mulVec_monotone (resolvent M) (resolvent_nonnegative M hnonneg) x
    (v+M*ᵥx) h
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,hRM,Matrix.sub_mulVec,Matrix.one_mulVec] at hm
  intro i
  have hi := hm i
  simp only [Pi.add_apply,Pi.sub_apply] at hi
  linarith

/-- Equivalent inverse notation for the same finite causal bound. -/
theorem feedback_bound_inverse {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hcausal : StrictLower M) (hnonneg : ∀ i j, 0 ≤ M i j)
    (x v : Fin n → ℝ) (h : ∀ i, x i ≤ v i+(M*ᵥx) i) :
    ∀ i, x i ≤ ((1-M)⁻¹*ᵥv) i := by
  rw [inverse_eq_resolvent M hcausal]
  exact feedback_bound M hcausal hnonneg x v h

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm estimate retains the residual-feedback term from changing query points.
The only residual hypothesis is its Lipschitz-sized difference along these two trajectories. -/
theorem norm_le_resolvent_of_feedback {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (E →L[ℝ] E))
    (hB : ∀ i j, i.val ≤ j.val → B i j = 0) (ε : ℝ) (hε : 0 ≤ ε)
    (delta source residual : Fin n → E)
    (heq : ∀ i, delta i = source i + ∑ j, B i j (residual j))
    (hres : ∀ j, ‖residual j‖ ≤ ε*‖delta j‖) :
    ∀ i, ‖delta i‖ ≤
      (resolvent (fun i j => ε*‖B i j‖)*ᵥ(fun j => ‖source j‖)) i := by
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => ε*‖B i j‖
  have hM : StrictLower M := by
    intro i j hij
    simp [M,hB i j hij]
  apply feedback_bound M hM (fun i j => mul_nonneg hε (norm_nonneg _))
  intro i
  calc
    ‖delta i‖ = ‖source i + ∑ j, B i j (residual j)‖ := congrArg norm (heq i)
    _ ≤ ‖source i‖ + ‖∑ j, B i j (residual j)‖ := norm_add_le _ _
    _ ≤ ‖source i‖ + ∑ j, ‖B i j (residual j)‖ := add_le_add_right (norm_sum_le _ _) _
    _ ≤ ‖source i‖ + (M*ᵥ(fun j => ‖delta j‖)) i := by
      apply add_le_add_right
      simp only [Matrix.mulVec,dotProduct]
      apply Finset.sum_le_sum
      intro j _
      calc
        ‖B i j (residual j)‖ ≤ ‖B i j‖*‖residual j‖ := (B i j).le_opNorm _
        _ ≤ ‖B i j‖*(ε*‖delta j‖) := mul_le_mul_of_nonneg_left (hres j) (norm_nonneg _)
        _ = M i j*‖delta j‖ := by dsimp [M]; ring

/-- Exact comparison of two forced linear responses. The final term records that
residuals are evaluated at the new trajectory's points. -/
theorem transport_identity {n : ℕ}
    (RA RB : Matrix (Fin n) (Fin n) (E →L[ℝ] E))
    (xA xB pA pB residualA residualB : Fin n → E)
    (hA : ∀ i, xA i = pA i + ∑ j, RA i j (residualA j))
    (hB : ∀ i, xB i = pB i + ∑ j, RB i j (residualB j)) :
    ∀ i, xB i-xA i =
      (pB i-pA i + ∑ j, (RB i j-RA i j) (residualA j)) +
        ∑ j, RB i j (residualB j-residualA j) := by
  intro i
  rw [hA i,hB i]
  simp only [_root_.sub_apply,map_sub,Finset.sum_sub_distrib]
  abel

/-- The causal comparison bound for two trajectories of the same Lipschitz residual
map. It retains the source term from both linear responses and imposes no small-gain
condition on ε or the finite horizon. -/
theorem two_trajectory_transport_bound {n : ℕ}
    (RA RB : Matrix (Fin n) (Fin n) (E →L[ℝ] E))
    (hB : ∀ i j, i.val ≤ j.val → RB i j = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (residual : E → E)
    (hres : ∀ x y, ‖residual x-residual y‖ ≤ ε*‖x-y‖)
    (xA xB pA pB : Fin n → E)
    (hAeq : ∀ i, xA i = pA i + ∑ j, RA i j (residual (xA j)))
    (hBeq : ∀ i, xB i = pB i + ∑ j, RB i j (residual (xB j))) :
    let source := fun i => pB i-pA i + ∑ j, (RB i j-RA i j) (residual (xA j))
    ∀ i, ‖xB i-xA i‖ ≤
      (resolvent (fun i j => ε*‖RB i j‖)*ᵥ(fun j => ‖source j‖)) i := by
  dsimp only
  apply norm_le_resolvent_of_feedback RB hB ε hε
    (fun i => xB i-xA i)
    (fun i => pB i-pA i + ∑ j, (RB i j-RA i j) (residual (xA j)))
    (fun j => residual (xB j)-residual (xA j))
  · exact transport_identity RA RB xA xB pA pB
      (fun j => residual (xA j)) (fun j => residual (xB j)) hAeq hBeq
  · intro j
    exact hres (xB j) (xA j)

end Normed
end CausalTransport
