module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

namespace NearQuadratic

open Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section ResponseOps

variable (A : ℕ → ℕ → ℝ) (Q : V →L[ℝ] V)

noncomputable def pOp : ℕ → V →L[ℝ] V :=
  (measure fun n : ℕ => n).wf.fix fun n ih =>
    match n with
    | 0 => ContinuousLinearMap.id ℝ V
    | n + 1 =>
      ContinuousLinearMap.id ℝ V +
        ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • Q.comp (ih k.val k.isLt)

theorem pOp_zero_eq :
    pOp (V := V) A Q 0 = ContinuousLinearMap.id ℝ V := by
  unfold pOp
  rw [WellFounded.fix_eq]

theorem pOp_succ_eq (A:=A) (Q:=Q) (n : ℕ) :
    pOp (V := V) A Q (n + 1) =
      ContinuousLinearMap.id ℝ V +
        ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • Q.comp (pOp (V := V) A Q k.val) := by
  have hP : pOp (V := V) A Q (n + 1) = WellFounded.fix (measure fun n : ℕ => n).wf
    (fun (n : ℕ) (ih : ∀ k, k < n → V →L[ℝ] V) =>
      match n with
      | 0 => ContinuousLinearMap.id ℝ V
      | n' + 1 =>
        ContinuousLinearMap.id ℝ V +
          ∑ k : Fin (n' + 1), (A (n' + 1) k.val : ℝ) • Q.comp (ih k.val k.isLt))
    (n + 1) := rfl
  have h := WellFounded.fix_eq (measure fun n : ℕ => n).wf
    (fun (n : ℕ) (ih : ∀ k, k < n → V →L[ℝ] V) =>
      match n with
      | 0 => ContinuousLinearMap.id ℝ V
      | n' + 1 =>
        ContinuousLinearMap.id ℝ V +
          ∑ k : Fin (n' + 1), (A (n' + 1) k.val : ℝ) • Q.comp (ih k.val k.isLt))
    (n + 1)
  rw [hP, h]
  apply congrArg (HAdd.hAdd (ContinuousLinearMap.id ℝ V))
  apply Finset.sum_congr rfl
  intro k _
  rfl

noncomputable def ROp : ℕ → ℕ → V →L[ℝ] V :=
  (measure fun n : ℕ => n).wf.fix fun n ih =>
    fun j =>
      match n with
      | 0 => 0
      | n + 1 =>
        if h : j < n + 1 then
          (A (n + 1) j : ℝ) • ContinuousLinearMap.id ℝ V +
            (∑ k : Fin (n + 1), if j < k.val then
              (A (n + 1) k.val : ℝ) • Q.comp (ih k.val k.isLt j)
            else 0)
        else 0

theorem ROp_succ_lt (n j : ℕ) (h : j < n + 1) :
    ROp (V := V) A Q (n + 1) j =
      (A (n + 1) j : ℝ) • ContinuousLinearMap.id ℝ V +
        (∑ k : Fin (n + 1), if j < k.val then
          (A (n + 1) k.val : ℝ) • Q.comp (ROp (V := V) A Q k.val j)
        else 0) := by
  have hP : ROp (V := V) A Q (n + 1) j = WellFounded.fix (measure fun n : ℕ => n).wf
    (fun (n : ℕ) (ih : ∀ k, k < n → ℕ → V →L[ℝ] V) (j : ℕ) =>
      match n with
      | 0 => (0 : V →L[ℝ] V)
      | n' + 1 =>
        if h : j < n' + 1 then
          (A (n' + 1) j : ℝ) • ContinuousLinearMap.id ℝ V +
            (∑ k : Fin (n' + 1), if j < k.val then
              (A (n' + 1) k.val : ℝ) • Q.comp (ih k.val k.isLt j)
            else 0)
        else 0) (n + 1) j := rfl
  have hfix := WellFounded.fix_eq (measure fun n : ℕ => n).wf
    (fun (n : ℕ) (ih : ∀ k, k < n → ℕ → V →L[ℝ] V) (j : ℕ) =>
      match n with
      | 0 => (0 : V →L[ℝ] V)
      | n' + 1 =>
        if h : j < n' + 1 then
          (A (n' + 1) j : ℝ) • ContinuousLinearMap.id ℝ V +
            (∑ k : Fin (n' + 1), if j < k.val then
              (A (n' + 1) k.val : ℝ) • Q.comp (ih k.val k.isLt j)
            else 0)
        else 0) (n + 1)
  rw [hP]
  have h2 := congrFun hfix j
  rw [h2]
  simp only [h, dite_true]
  apply congrArg (HAdd.hAdd ((A (n + 1) j : ℝ) • ContinuousLinearMap.id ℝ V))
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h2
  · rfl
  · rfl

noncomputable def pScalar (A : ℕ → ℕ → ℝ) : ℕ → ℝ → ℝ :=
  (measure fun n : ℕ => n).wf.fix fun n ih =>
    fun lam =>
      match n with
      | 0 => 1
      | n + 1 => 1 + ∑ k : Fin (n + 1), A (n + 1) k.val * lam * ih k.val k.isLt lam

noncomputable def rScalar (A : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ :=
  (measure fun n : ℕ => n).wf.fix fun n ih =>
    fun j lam =>
      match n with
      | 0 => 0
      | n + 1 =>
        if h : j < n + 1 then
          A (n + 1) j + ∑ k : Fin (n + 1), if j < k.val then
            A (n + 1) k.val * lam * ih k.val k.isLt j lam
          else 0
        else 0

noncomputable def traj (A : ℕ → ℕ → ℝ) (Q : V →L[ℝ] V) (r : ℕ → V) (e0 : V) : ℕ → V :=
  (measure fun n : ℕ => n).wf.fix fun n ih =>
    match n with
    | 0 => e0
    | n + 1 => e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • (Q (ih k.val k.isLt) + r k.val)

theorem traj_zero : traj (V := V) A Q r e0 0 = e0 := by
  unfold traj
  rw [WellFounded.fix_eq]

theorem traj_succ (n : ℕ) :
    traj (V := V) A Q r e0 (n + 1) =
      e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • (Q (traj (V := V) A Q r e0 k.val) + r k.val) := by
  have hP : traj (V := V) A Q r e0 (n + 1) = WellFounded.fix (measure fun n : ℕ => n).wf
    (fun (n : ℕ) (ih : ∀ k, k < n → V) =>
      match n with
      | 0 => e0
      | n' + 1 => e0 + ∑ k : Fin (n' + 1), (A (n' + 1) k.val : ℝ) • (Q (ih k.val k.isLt) + r k.val))
    (n + 1) := rfl
  have h := WellFounded.fix_eq (measure fun n : ℕ => n).wf
    (fun (n : ℕ) (ih : ∀ k, k < n → V) =>
      match n with
      | 0 => e0
      | n' + 1 => e0 + ∑ k : Fin (n' + 1), (A (n' + 1) k.val : ℝ) • (Q (ih k.val k.isLt) + r k.val))
    (n + 1)
  rw [hP, h]
  apply congrArg (HAdd.hAdd e0)
  apply Finset.sum_congr rfl
  intro k _
  rfl

-- Exact error identity
theorem traj_eq_pOp_plus_ROp (r : ℕ → V) (e0 : V) (n : ℕ) :
    traj (V := V) A Q r e0 n = pOp (V := V) A Q n e0 + ∑ j : Fin n, ROp (V := V) A Q n j.val (r j.val) := by
  induction n using (measure fun n : ℕ => n).wf.induction with
  | h n ih =>
    match n with
    | 0 =>
      simp [traj_zero, pOp_zero_eq]
    | n + 1 =>
      have h_pOp : pOp (V := V) A Q (n + 1) e0 =
          e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • Q (pOp (V := V) A Q k.val e0) := by
        calc pOp (V := V) A Q (n + 1) e0
            = (pOp (V := V) A Q (n + 1)) e0 := rfl
          _ = (ContinuousLinearMap.id ℝ V +
                ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • Q.comp (pOp (V := V) A Q k.val)) e0 := by
                rw [pOp_succ_eq (A:=A) (Q:=Q)]
          _ = e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • Q (pOp (V := V) A Q k.val e0) := by
                simp
      have h_traj_k : ∀ (k : Fin (n + 1)),
          traj (V := V) A Q r e0 k.val = pOp (V := V) A Q k.val e0 + ∑ j : Fin k.val, ROp (V := V) A Q k.val j.val (r j.val) := by
        intro k
        exact ih k.val k.isLt
      calc traj (V := V) A Q r e0 (n + 1)
          = e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • (Q (traj (V := V) A Q r e0 k.val) + r k.val) := traj_succ (A:=A) (Q:=Q) n
        _ = e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • (Q (pOp (V := V) A Q k.val e0 + ∑ j : Fin k.val, ROp (V := V) A Q k.val j.val (r j.val)) + r k.val) := by
            apply congrArg (HAdd.hAdd e0)
            apply Finset.sum_congr rfl
            intro k _
            rw [h_traj_k k]
        _ = e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • (Q (pOp (V := V) A Q k.val e0) + (∑ j : Fin k.val, Q (ROp (V := V) A Q k.val j.val (r j.val))) + r k.val) := by
            apply congrArg (HAdd.hAdd e0)
            apply Finset.sum_congr rfl
            intro k _
            rw [map_add, map_sum]
        _ = (e0 + ∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • Q (pOp (V := V) A Q k.val e0)) +
            (∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • r k.val +
             ∑ k : Fin (n + 1), ∑ j : Fin k.val, (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val))) := by
            simp [smul_add, Finset.smul_sum, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm]
        _ = pOp (V := V) A Q (n + 1) e0 +
            (∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • r k.val +
             ∑ k : Fin (n + 1), ∑ j : Fin k.val, (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val))) := by
            rw [← h_pOp]
        _ = pOp (V := V) A Q (n + 1) e0 +
            ∑ j : Fin (n + 1), ROp (V := V) A Q (n + 1) j.val (r j.val) := by
            congr 1
            have h_ROp_eq : ∀ (j : Fin (n + 1)), ROp (V := V) A Q (n + 1) j.val (r j.val) =
                (A (n + 1) j.val : ℝ) • r j.val +
                ∑ k : Fin (n + 1), if j.val < k.val then (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val)) else 0 := by
              intro j
              have hlt : j.val < n + 1 := j.isLt
              calc ROp (V := V) A Q (n + 1) j.val (r j.val)
                  = ((A (n + 1) j.val : ℝ) • ContinuousLinearMap.id ℝ V +
                      ∑ k : Fin (n + 1), if j.val < k.val then (A (n + 1) k.val : ℝ) • Q.comp (ROp (V := V) A Q k.val j.val) else 0) (r j.val) := by
                    rw [ROp_succ_lt (A:=A) (Q:=Q) _ _ hlt]
                  _ = (A (n + 1) j.val : ℝ) • r j.val +
                      ∑ k : Fin (n + 1), if j.val < k.val then (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val)) else 0 := by
                    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
                      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
                      ContinuousLinearMap.id_apply, zero_apply, smul_zero, ite_apply]
                    congr 1
                    apply Finset.sum_congr rfl
                    intro k _
                    split_ifs <;> simp
            have h_swap : ∑ k : Fin (n + 1), ∑ j : Fin k.val, (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val)) =
                ∑ j : Fin (n + 1), ∑ k : Fin (n + 1), if j.val < k.val then (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val)) else 0 := by
              have h_inner : ∀ k : Fin (n + 1),
                  (∑ j : Fin k.val, (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val))) =
                    ∑ j : Fin (n + 1), if j.val < k.val then
                      (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val)) else 0 := by
                intro k
                let F : ℕ → V := fun j => (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j (r j))
                calc
                  _ = ∑ j ∈ Finset.range k.val, F j := Fin.sum_univ_eq_sum_range F k.val
                  _ = ∑ j ∈ (Finset.range (n+1)).filter (· < k.val), F j := by
                    congr 1
                    ext j
                    simp only [Finset.mem_filter, Finset.mem_range]
                    omega
                  _ = ∑ j ∈ Finset.range (n+1), if j < k.val then F j else 0 := by
                    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
                  _ = _ := (Fin.sum_univ_eq_sum_range
                    (fun j => if j < k.val then F j else 0) (n+1)).symm
              simp_rw [h_inner]
              rw [Finset.sum_comm]
            have h_resid : (∑ k : Fin (n + 1), (A (n + 1) k.val : ℝ) • r k.val +
             ∑ k : Fin (n + 1), ∑ j : Fin k.val, (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val))) =
             ∑ j : Fin (n + 1), ((A (n + 1) j.val : ℝ) • r j.val +
               ∑ k : Fin (n + 1), if j.val < k.val then (A (n + 1) k.val : ℝ) • Q (ROp (V := V) A Q k.val j.val (r j.val)) else 0) := by
              rw [h_swap]
              simp [Finset.sum_add_distrib]
            rw [h_resid]
            apply Finset.sum_congr rfl
            intro j _
            rw [h_ROp_eq j]

end ResponseOps

section TerminalBound

variable {A : ℕ → ℕ → ℝ} {Q : V →L[ℝ] V} {r : ℕ → V} {e0 : V}
variable {N : ℕ} {R ε : ℝ} {hA : ℕ → ℝ} {rho : ℕ → ℝ}

noncomputable def betaCoeff (N : ℕ) (rho hA : ℕ → ℝ) : ℝ :=
  ∑ j : Fin N, rho j.val * hA j.val

theorem betaCoeff_nonneg (h_rho : ∀ j, 0 ≤ rho j) (h_hA : ∀ j, 0 ≤ hA j) :
    0 ≤ betaCoeff N rho hA := by
  unfold betaCoeff
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (h_rho i.val) (h_hA i.val)

theorem terminal_response_bound
    (h_traj : traj (V := V) A Q r e0 N = pOp (V := V) A Q N e0 + ∑ j : Fin N, ROp (V := V) A Q N j.val (r j.val))
    (h_resid_norm : ∀ j, j < N → ‖r j‖ ≤ ε * ‖traj (V := V) A Q r e0 j‖)
    (h_causal : ∀ j, j < N → ‖traj (V := V) A Q r e0 j‖ ≤ R * hA j)
    (h_ROp_norm : ∀ j, j < N → ‖ROp (V := V) A Q N j‖ ≤ rho j)
    (h_eps_nonneg : 0 ≤ ε) (h_R_nonneg : 0 ≤ R)
    (h_rho_nonneg : ∀ j, 0 ≤ rho j) (h_hA_nonneg : ∀ j, 0 ≤ hA j) :
    ‖traj (V := V) A Q r e0 N - pOp (V := V) A Q N e0‖ ≤ ε * R * betaCoeff N rho hA := by
  have h_sub : traj (V := V) A Q r e0 N - pOp (V := V) A Q N e0 = ∑ j : Fin N, ROp (V := V) A Q N j.val (r j.val) := by
    rw [h_traj, add_sub_cancel_left]
  rw [h_sub]
  calc ‖∑ j : Fin N, ROp (V := V) A Q N j.val (r j.val)‖
      ≤ ∑ j : Fin N, ‖ROp (V := V) A Q N j.val (r j.val)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin N, ‖ROp (V := V) A Q N j.val‖ * ‖r j.val‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ∑ j : Fin N, rho j.val * (ε * (R * hA j.val)) := by
        apply Finset.sum_le_sum
        intro j _
        have hj : (j.val : ℕ) < N := j.isLt
        have hr : ‖r j.val‖ ≤ ε * ‖traj (V := V) A Q r e0 j.val‖ := h_resid_norm _ hj
        have hc : ‖traj (V := V) A Q r e0 j.val‖ ≤ R * hA j.val := h_causal _ hj
        have hR : ‖ROp (V := V) A Q N j.val‖ ≤ rho j.val := h_ROp_norm _ hj
        calc ‖ROp (V := V) A Q N j.val‖ * ‖r j.val‖
            ≤ rho j.val * (ε * ‖traj (V := V) A Q r e0 j.val‖) :=
              mul_le_mul hR hr (norm_nonneg _) (h_rho_nonneg _)
          _ ≤ rho j.val * (ε * (R * hA j.val)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc h_eps_nonneg) (h_rho_nonneg _)
    _ = ε * R * betaCoeff N rho hA := by
        unfold betaCoeff
        have : ∀ (j : Fin N), rho j.val * (ε * (R * hA j.val)) = ε * R * (rho j.val * hA j.val) := by
          intro j; ring
        simp_rw [this]
        rw [← Finset.mul_sum]

end TerminalBound

end NearQuadratic
