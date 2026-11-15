module
public import Continuation.Quadratic.Foundations
public import RealizationCore.Coordinates
public import RealizationCore.VectorRealization
@[expose] public section
noncomputable section
namespace QuadraticResidual
open Matrix Polynomial

/-- Error trajectory driven by the exact linear gradient oracle g=Qe.
The coefficients are the paper's increments d,T. -/
def errorIter {n : ℕ} (N : ℕ) (d : Fin N → ℝ)
    (T : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (e0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => e0
  | k+1 => if h : k < N then
      errorIter N d T Q e0 k + d ⟨k,h⟩ • (Q *ᵥ errorIter N d T Q e0 k) +
        ∑ j : Fin k, T ⟨k,h⟩ ⟨j.val,by omega⟩ •
          (Q *ᵥ errorIter N d T Q e0 j.val)
    else e0

private theorem sum_mulVec {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ i, A i) *ᵥ v = ∑ i, A i *ᵥ v := by
  exact map_sum (Matrix.mulVec.addMonoidHomLeft v) A Finset.univ

private theorem mulVec_sum {n k : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (v : Fin k → Fin n → ℝ) :
    Q *ᵥ (∑ i, v i) = ∑ i, Q *ᵥ v i := by
  exact map_sum Q.mulVecLin v Finset.univ

/-- The residual identity: scalar polynomial p_k is evaluated in the matrix
algebra at Q, and that matrix acts on the initial error. No spectral or
optimality assumption is needed for this algebraic statement. -/
theorem errorIter_eq_polynomial {n : ℕ} (N : ℕ) (d : Fin N → ℝ)
    (T : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (e0 : Fin n → ℝ) (k : ℕ) (hk : k ≤ N) :
    errorIter N d T Q e0 k =
      (Polynomial.aeval Q (QuadraticFoundations.pIter N d T k)) *ᵥ e0 := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    cases k with
    | zero => simp [errorIter, QuadraticFoundations.pIter]
    | succ k =>
      have hkN : k < N := by omega
      simp only [errorIter, QuadraticFoundations.pIter, dite_eq_left hkN]
      have hprev := ih k (by omega) (by omega)
      have hj : ∀ j : Fin k, errorIter N d T Q e0 j.val =
          (Polynomial.aeval Q (QuadraticFoundations.pIter N d T j.val)) *ᵥ e0 := by
        intro j
        exact ih j.val (by omega) (by omega)
      rw [hprev]
      simp_rw [hj]
      simp only [map_add, map_mul, map_sum, aeval_C, aeval_X,
        Algebra.algebraMap_eq_smul_one, add_mulVec, smul_mulVec,
        one_mulVec, ← mulVec_mulVec, sum_mulVec, mulVec_sum, mulVec_smul,
        one_smul]

theorem vectorTarget_step {n N : ℕ} (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (x0 : Fin n → ℝ)
    (g : Fin N → Fin n → ℝ) (k : ℕ) (hk : k < N) :
    RegisterMachine.vectorTarget (RealizationCore.W_of N d T.val) x0 g
        ⟨k+1,by omega⟩ =
      RegisterMachine.vectorTarget (RealizationCore.W_of N d T.val) x0 g
        ⟨k,by omega⟩ + d ⟨k,hk⟩ • g ⟨k,hk⟩ +
        ∑ j : Fin k, T.val ⟨k,hk⟩ ⟨j.val,by omega⟩ • g ⟨j.val,by omega⟩ := by
  let W := RealizationCore.W_of N d T.val
  have hdiag : W ⟨k+1,by omega⟩ ⟨k,by omega⟩ = d ⟨k,hk⟩ := by
    have h := congrFun (RealizationCore.d_of_W_of N d T.val) ⟨k,hk⟩
    exact h
  have hinc (j : Fin k) : W ⟨k+1,by omega⟩ ⟨j.val,by omega⟩ =
      W ⟨k,by omega⟩ ⟨j.val,by omega⟩ + T.val ⟨k,hk⟩ ⟨j.val,by omega⟩ := by
    have h := congrFun (congrFun (RealizationCore.T_of_W_of N d T.val T.property)
      ⟨k,hk⟩) ⟨j.val,by omega⟩
    simp only [RealizationCore.T_of, Matrix.of_apply, j.isLt, dite_true] at h
    change W ⟨k+1,by omega⟩ ⟨j.val,by omega⟩ -
      W ⟨k,by omega⟩ ⟨j.val,by omega⟩ = _ at h
    linarith
  funext a
  change x0 a + (∑ j : Fin (k+1), W ⟨k+1,by omega⟩ ⟨j.val,by omega⟩ *
    g ⟨j.val,by omega⟩ a) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [hdiag]
  simp_rw [hinc]
  simp only [RegisterMachine.vectorTarget, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  change _ = x0 a + (∑ j : Fin k, W ⟨k,by omega⟩ ⟨j.val,by omega⟩ *
    g ⟨j.val,by omega⟩ a) + d ⟨k,hk⟩ * g ⟨k,hk⟩ a + _
  ring

/-- The increment trajectory is the history-map trajectory with exact linear
oracle outputs. This ties the residual polynomial to the accepted W(d,T) model. -/
theorem errorIter_eq_history {n N : ℕ} (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (Q : Matrix (Fin n) (Fin n) ℝ)
    (e0 : Fin n → ℝ) (k : ℕ) (hk : k ≤ N) :
    errorIter N d T.val Q e0 k =
      RegisterMachine.vectorTarget (RealizationCore.W_of N d T.val) e0
        (fun j : Fin N => Q *ᵥ errorIter N d T.val Q e0 j.val) ⟨k,by omega⟩ := by
  induction k with
  | zero =>
    unfold errorIter RegisterMachine.vectorTarget
    funext a
    simp
  | succ k ih =>
    have hkN : k < N := by omega
    rw [vectorTarget_step d T e0 _ k hkN]
    simp only [errorIter, dite_eq_left hkN]
    rw [← ih (by omega)]

/-- The paper's history-map output under the exact linear oracle is p_k(Q)e0. -/
theorem history_eq_polynomial {n N : ℕ} (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) (Q : Matrix (Fin n) (Fin n) ℝ)
    (e0 : Fin n → ℝ) (k : ℕ) (hk : k ≤ N) :
    RegisterMachine.vectorTarget (RealizationCore.W_of N d T.val) e0
        (fun j : Fin N => Q *ᵥ errorIter N d T.val Q e0 j.val) ⟨k,by omega⟩ =
      (Polynomial.aeval Q (QuadraticFoundations.pIter N d T.val k)) *ᵥ e0 :=
  (errorIter_eq_history d T Q e0 k hk).symm.trans
    (errorIter_eq_polynomial N d T.val Q e0 k hk)

end QuadraticResidual
