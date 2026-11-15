module
public import Continuation.GJP.FactorizationAdmissible
public import Continuation.GJP.FactorStability

@[expose] public section
noncomputable section
open Matrix Filter Topology
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The original compact dual PSD matrix (9), writing `A = -Λ`. -/
def compactDualMatrix (last : n) (W A : Matrix n n ℝ) (r : ℝ) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ :=
  borderedMatrix r (fun j => ∑ i, A i j)
    (matrixSymm (Wᵀ * A) - (1/2:ℝ) •
      Matrix.vecMulVec (Pi.single last 1) (Pi.single last 1))

/-- Actual compact dual feasibility (9), including a strictly positive rate. -/
structure CompactDualFeasible (last : n) (W A : Matrix n n ℝ) (r : ℝ) : Prop where
  rate_pos : 0 < r
  offdiag : ∀ i j, i ≠ j → A i j ≤ 0
  rowBound : ∀ i, (Pi.single last (1:ℝ) : n → ℝ) i ≤ (A *ᵥ (fun _ => 1)) i
  columnBound : ∀ i, 0 ≤ (Aᵀ *ᵥ (fun _ => 1)) i
  psd : (compactDualMatrix last W A r).PosSemidef

lemma compactDualMatrix_factor (last : n) (W T C : Matrix n n ℝ) (r : ℝ) :
    compactDualMatrix last W (T*C) r = equation15Matrix last W T C r := by
  simp only [compactDualMatrix, equation15Matrix, Matrix.mul_assoc]

variable {N : ℕ}

/-- Exact passage from an original dual solution to its triangular formulation. -/
theorem CompactDualFeasible.factor {W A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} {r : ℝ}
    (h : CompactDualFeasible (Fin.last N) W A r) :
    ∃ T C, A = T*C ∧ TCAdmissible (Fin.last N) T C ∧
      (equation15Matrix (Fin.last N) W T C r).PosSemidef := by
  obtain ⟨T,C,hA,hTC⟩ := exists_TC_admissible N A h.offdiag h.rowBound h.columnBound
  refine ⟨T,C,hA,hTC,?_⟩
  simpa only [hA, compactDualMatrix_factor] using h.psd

/-- The sharp lower bound applies already to the original, unfactored compact dual. -/
theorem compactDual_rate_lower {W A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} {r : ℝ}
    (hW : UnitLower W) (h : CompactDualFeasible (Fin.last N) W A r) : rOGM N ≤ r := by
  obtain ⟨T,C,_,hTC,hPSD⟩ := h.factor
  exact equation15_rate_lower W T C r h.rate_pos hW hTC hPSD

/-- Approximate original dual certificates attain the canonical limiting certificate. -/
theorem compactDual_limit_certificate
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (As : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (rs : ℕ → ℝ)
    (hW : UnitLower W) (hs : ∀ k, CompactDualFeasible (Fin.last N) W (As k) (rs k))
    (hrlim : Tendsto rs atTop (𝓝 (rOGM N))) :
    TCAdmissible (Fin.last N) (optimalFactorT N) 1 ∧
      (equation15Matrix (Fin.last N) W (optimalFactorT N) 1 (rOGM N)).PosSemidef := by
  choose Ts Cs hA hTC hPSD using (fun k => (hs k).factor)
  exact equation15_limit_certificate W Ts Cs rs hW (fun k => (hs k).rate_pos) hTC hPSD hrlim

/-- The original compact dual cannot have two distinct methods at the optimal limiting rate. -/
theorem compactDual_approaching_method_unique
    (W₁ W₂ : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (A₁ A₂ : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (r₁ r₂ : ℕ → ℝ)
    (hW₁ : UnitLower W₁) (hW₂ : UnitLower W₂)
    (hs₁ : ∀ k, CompactDualFeasible (Fin.last N) W₁ (A₁ k) (r₁ k))
    (hs₂ : ∀ k, CompactDualFeasible (Fin.last N) W₂ (A₂ k) (r₂ k))
    (hr₁ : Tendsto r₁ atTop (𝓝 (rOGM N))) (hr₂ : Tendsto r₂ atTop (𝓝 (rOGM N))) : W₁ = W₂ := by
  obtain ⟨hTC₁,hPSD₁⟩ := compactDual_limit_certificate W₁ A₁ r₁ hW₁ hs₁ hr₁
  obtain ⟨hTC₂,hPSD₂⟩ := compactDual_limit_certificate W₂ A₂ r₂ hW₂ hs₂ hr₂
  exact equation15_optimal_method_unique W₁ _ _ W₂ _ _ hW₁ hW₂ hTC₁ hTC₂ hPSD₁ hPSD₂

end GJP
