module
public import Continuation.GJP.FactorProjection
public import Continuation.GJP.ScalarProjection

@[expose] public section
noncomputable section
open Matrix
namespace GJP

variable {N : ℕ}

def flowDelta (T : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (b : Fin (N+1) → ℝ) : Fin (N+1) → ℝ :=
  fun i => (∑ j, T j i) * b i

lemma flowDelta_simplex (T : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (b : Fin (N+1) → ℝ)
    (hp : ∀ i, 0 ≤ ∑ j, T j i) (hb : ∀ i, 0 ≤ b i)
    (hTb : T *ᵥ b = Pi.single (Fin.last N) 1) : DeltaProp N (flowDelta T b) := by
  constructor
  · intro i; exact mul_nonneg (hp i) (hb i)
  · unfold flowDelta
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    change (∑ i, (T *ᵥ b) i) = 1
    rw [hTb]
    simp

lemma flowDelta_prefix_bound (T : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (b : Fin (N+1) → ℝ) (hT : T.IsUpperTriangular)
    (hs : ∀ i j, i < j → T i j ≤ 0) (hb : ∀ i, 0 ≤ b i)
    (hTb : T *ᵥ b = Pi.single (Fin.last N) 1) (i : Fin (N+1)) (hi : i.val < N) :
    T i i * b i ≤ S N (flowDelta T b) i.val := by
  have h := upper_prefix_bound (Fin.last N) T b hT hs hb hTb i (by change i.val < N; exact hi)
  change T i i * b i ≤ ∑ j, if j ≤ i then (∑ k, T k j) * b j else 0
  simpa only [Finset.sum_filter] using h

/-- The scalar projection inequality (19), with every premise derived from (15). -/
theorem equation15_flow_bound (W T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (r : ℝ) (hr : 0 < r) (hW : UnitLower W) (hTC : TCAdmissible (Fin.last N) T C)
    (hPSD : (equation15Matrix (Fin.last N) W T C r).PosSemidef)
    (b : Fin (N+1) → ℝ) (hTb : T *ᵥ b = Pi.single (Fin.last N) 1)
    (hb : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    Phi N (flowDelta T b) ≤ r := by
  have hΔ := flowDelta_simplex T b hTC.colsum_nonneg hb hTb
  have hdiag := equation15_diagonal_necessary (Fin.last N) r hr hW hTC.upper hTC.unitLower hPSD
  apply Finset.sup'_le
  intro i _
  unfold phiTerm
  by_cases hi : i.val < N
  · simp only [hi, ↓reduceIte, partialSum, flowDelta]
    apply projected_fraction_bound r (T i i) (∑ j, T j i) (C⁻¹ (Fin.last N) i)
      (b i) (S N (flowDelta T b) i.val) hr (hTC.diagNonneg i) (hb i) (hb1 i)
      (S_nonneg N (flowDelta T b) hΔ.1 i.val)
      (flowDelta_prefix_bound T b hTC.upper hTC.upperNonpos hb hTb i hi) (hdiag i)
  · simp only [hi, ↓reduceIte, flowDelta]
    have hiLast : i = Fin.last N := Fin.ext (by simp; omega)
    subst i
    have hrow := upper_terminal_row (Fin.last N) (fun j => Fin.le_last j) T hTC.upper b hTb
    have hlast := hdiag (Fin.last N)
    rw [hTC.unitLower.inv.2 (Fin.last N)] at hlast
    norm_num only [one_pow] at hlast
    exact projected_terminal_bound r (T (Fin.last N) (Fin.last N))
      (∑ j, T j (Fin.last N)) (b (Fin.last N)) hr (hb _) hrow hlast

/-- The projection part of Lemma 3.4, including existence of its simplex vector. -/
theorem equation15_projects_simplex (W T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (r : ℝ) (hr : 0 < r) (hW : UnitLower W) (hTC : TCAdmissible (Fin.last N) T C)
    (hPSD : (equation15Matrix (Fin.last N) W T C r).PosSemidef) :
    ∃ b : Fin (N+1) → ℝ, T *ᵥ b = Pi.single (Fin.last N) 1 ∧
      (∀ i, 0 ≤ b i) ∧ (∀ i, b i ≤ 1) ∧
      (∀ i, T i i ≠ 0 → b i ≤ (C *ᵥ (fun _ => 1)) i) ∧
      (∀ i, T i i = 0 → b i = 0) ∧
      DeltaProp N (flowDelta T b) ∧ Phi N (flowDelta T b) ≤ r := by
  obtain ⟨b, hTb, hb, hb1, hbC, hbzero⟩ := hTC.exists_b
  exact ⟨b, hTb, hb, hb1, hbC, hbzero,
    flowDelta_simplex T b hTC.colsum_nonneg hb hTb,
    equation15_flow_bound W T C r hr hW hTC hPSD b hTb hb hb1⟩

/-- The exact OGM rate is a lower bound on every feasible tuple of equation (15). -/
theorem equation15_rate_lower (W T C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (r : ℝ) (hr : 0 < r) (hW : UnitLower W) (hTC : TCAdmissible (Fin.last N) T C)
    (hPSD : (equation15Matrix (Fin.last N) W T C r).PosSemidef) : rOGM N ≤ r := by
  obtain ⟨b, _, _, _, _, _, hΔ, hPhi⟩ := equation15_projects_simplex W T C r hr hW hTC hPSD
  exact (rOGM_leq_Phi N (flowDelta T b) hΔ).trans hPhi

end GJP
