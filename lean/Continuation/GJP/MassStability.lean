module
public import Continuation.GJP.OptimalFactors
public import Continuation.GJP.SimplexStability

@[expose] public section
noncomputable section
open Matrix Filter Topology
namespace GJP

lemma projected_square_bound_with_mass (r d p q b s : ℝ) (hr : 0 < r)
    (hb : 0 ≤ b) (hprefix : d*b ≤ s) (hdiag : p^2/(2*r) ≤ d-q^2/2) :
    (p*b)^2 ≤ (2*r*s)*b := by
  have hp : p^2 ≤ 2*r*d := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*r)).mp hdiag
    nlinarith [mul_nonneg hr.le (sq_nonneg q)]
  calc
    (p*b)^2 = p^2*b^2 := by ring
    _ ≤ (2*r*d)*b^2 := mul_le_mul_of_nonneg_right hp (sq_nonneg b)
    _ = ((2*r)*(d*b))*b := by ring
    _ ≤ ((2*r)*s)*b := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprefix (by positivity)) hb

lemma projected_terminal_bound_with_mass (r d p b : ℝ) (hr : 0 < r)
    (hrow : d*b = 1) (hdiag : p^2/(2*r) ≤ d-1/2) : (p*b)^2 ≤ r*(2*b-b^2) := by
  have hp : p^2 ≤ r*(2*d-1) := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*r)).mp hdiag
    nlinarith
  have hdb : d*b^2 = b := by
    calc d*b^2 = (d*b)*b := by ring
         _ = b := by rw [hrow]; ring
  have hsq := mul_le_mul_of_nonneg_right hp (sq_nonneg b)
  have hid : r*(2*d-1)*b^2 = r*(2*b-b^2) := by
    calc r*(2*d-1)*b^2 = r*(2*(d*b^2)-b^2) := by ring
         _ = r*(2*b-b^2) := by rw [hdb]
  rw [hid] at hsq
  simpa only [mul_pow] using hsq

variable {N : ℕ}

/-- The bounded projection mass converges to ones when the polynomial scalar chains saturate. -/
theorem mass_stability (δs bs : ℕ → Fin (N+1) → ℝ) (rs : ℕ → ℝ)
    (hb : ∀ k i, 0 ≤ bs k i) (hb1 : ∀ k i, bs k i ≤ 1)
    (hδ : Tendsto δs atTop (𝓝 (deltaStar N))) (hr : Tendsto rs atTop (𝓝 (rOGM N)))
    (hchain : ∀ k i, i.val < N → (δs k i)^2 ≤ (2*rs k*S N (δs k) i.val)*bs k i)
    (hterminal : ∀ k, (δs k (Fin.last N))^2 ≤ rs k*(2*bs k (Fin.last N)-(bs k (Fin.last N))^2)) :
    Tendsto bs atTop (𝓝 (fun _ => (1:ℝ))) := by
  have hmem : ∀ᶠ k in atTop, bs k ∈ Set.Icc (0 : Fin (N+1) → ℝ) 1 :=
    Eventually.of_forall (fun k => ⟨hb k, hb1 k⟩)
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin (N+1) → ℝ) 1)).tendsto_nhds_of_unique_mapClusterPt hmem
  intro b hbox hcluster
  obtain ⟨φ, hφ, hblim⟩ := hcluster.tendsto_subseq
  have hδlim := hδ.comp hφ.tendsto_atTop
  have hrlim := hr.comp hφ.tendsto_atTop
  funext i
  have hbLim : Tendsto (fun k => bs (φ k) i) atTop (𝓝 (b i)) := (tendsto_pi_nhds.mp hblim) i
  have hδLim : Tendsto (fun k => δs (φ k) i) atTop (𝓝 (deltaStar N i)) :=
    (tendsto_pi_nhds.mp hδlim) i
  by_cases hi : i.val < N
  · have hS : Tendsto (fun k => S N (δs (φ k)) i.val) atTop (𝓝 (S N (deltaStar N) i.val)) :=
      ((continuous_partial_sum N i.val).tendsto _).comp hδlim
    have hbound : (deltaStar N i)^2 ≤ (2*rOGM N*S N (deltaStar N) i.val)*b i :=
      le_of_tendsto_of_tendsto (hδLim.pow 2) (((tendsto_const_nhds.mul hrlim).mul hS).mul hbLim)
        (Eventually.of_forall (fun k => hchain (φ k) i hi))
    have hterm := phiTerm_tied N i
    have hspos : 0 < S N (deltaStar N) i.val := by
      rw [deltaStar_S_eq N i.val hi]
      have hr := rOGM_pos N
      have ht := SmoothBenchmark.theta_pos N i.val (by omega)
      positivity
    have heq : (deltaStar N i)^2 = rOGM N*(2*S N (deltaStar N) i.val) := by
      apply (div_eq_iff (by positivity : 2*S N (deltaStar N) i.val ≠ 0)).mp
      simpa [phiTerm, partialSum, hi] using hterm
    have hrpos := rOGM_pos N
    have hge : 1 ≤ b i := by
      apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2*rOGM N*S N (deltaStar N) i.val)).mp
      nlinarith
    exact le_antisymm (hbox.2 i) hge
  · have hiLast : i = Fin.last N := Fin.ext (by simp; omega)
    subst i
    have hbound : (deltaStar N (Fin.last N))^2 ≤ rOGM N*(2*b (Fin.last N)-(b (Fin.last N))^2) :=
      le_of_tendsto_of_tendsto (hδLim.pow 2)
        (hrlim.mul ((tendsto_const_nhds.mul hbLim).sub (hbLim.pow 2)))
        (Eventually.of_forall (fun k => hterminal (φ k)))
    have hterm : (deltaStar N (Fin.last N))^2 = rOGM N := by
      simpa [phiTerm] using phiTerm_tied N (Fin.last N)
    have hs : (1-b (Fin.last N))^2 ≤ 0 := by
      apply nonpos_of_mul_nonpos_left _ (rOGM_pos N)
      nlinarith
    nlinarith [sq_nonneg (1-b (Fin.last N))]

/-- Actual feasible tuples approaching the OGM rate force their constructed masses to ones. -/
theorem equation15_mass_stability
    (Ws Ts Cs : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (rs : ℕ → ℝ)
    (bs : ℕ → Fin (N+1) → ℝ)
    (hr : ∀ k, 0 < rs k) (hW : ∀ k, UnitLower (Ws k))
    (hTC : ∀ k, TCAdmissible (Fin.last N) (Ts k) (Cs k))
    (hPSD : ∀ k, (equation15Matrix (Fin.last N) (Ws k) (Ts k) (Cs k) (rs k)).PosSemidef)
    (hTb : ∀ k, Ts k *ᵥ bs k = Pi.single (Fin.last N) 1)
    (hb : ∀ k i, 0 ≤ bs k i) (hb1 : ∀ k i, bs k i ≤ 1)
    (hrlim : Tendsto rs atTop (𝓝 (rOGM N))) : Tendsto bs atTop (𝓝 (fun _ => (1:ℝ))) := by
  have hδ := simplex_stability (fun k => flowDelta (Ts k) (bs k)) rs
    (fun k => flowDelta_simplex (Ts k) (bs k) (hTC k).colsum_nonneg (hb k) (hTb k))
    (fun k => equation15_flow_bound (Ws k) (Ts k) (Cs k) (rs k) (hr k) (hW k) (hTC k) (hPSD k)
      (bs k) (hTb k) (hb k) (hb1 k)) hrlim
  apply mass_stability (fun k => flowDelta (Ts k) (bs k)) bs rs hb hb1 hδ hrlim
  · intro k i hi
    exact projected_square_bound_with_mass (rs k) (Ts k i i) (∑ j, Ts k j i)
      ((Cs k)⁻¹ (Fin.last N) i) (bs k i) (S N (flowDelta (Ts k) (bs k)) i.val)
      (hr k) (hb k i)
      (flowDelta_prefix_bound (Ts k) (bs k) (hTC k).upper (hTC k).upperNonpos (hb k) (hTb k) i hi)
      (equation15_diagonal_necessary (Fin.last N) (rs k) (hr k) (hW k) (hTC k).upper (hTC k).unitLower (hPSD k) i)
  · intro k
    apply projected_terminal_bound_with_mass (rs k) (Ts k (Fin.last N) (Fin.last N))
      (∑ j, Ts k j (Fin.last N)) (bs k (Fin.last N)) (hr k)
      (upper_terminal_row (Fin.last N) (fun j => Fin.le_last j) (Ts k) (hTC k).upper (bs k) (hTb k))
    have h := equation15_diagonal_necessary (Fin.last N) (rs k) (hr k) (hW k)
      (hTC k).upper (hTC k).unitLower (hPSD k) (Fin.last N)
    simpa only [(hTC k).unitLower.inv.2 (Fin.last N), one_pow] using h

end GJP
