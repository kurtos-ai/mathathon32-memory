module
public import Continuation.Smooth.ConjugateRegularity
@[expose] public section

open Set Filter
open scoped Topology InnerProductSpace

namespace ConstrainedConjugate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {H : V → ℝ} {μ : ℝ} {K : Set V}

theorem strong_support (hH : StrongConvexOn K μ H) (p q : V) (hqK : q ∈ K)
    (hq : ∀ u ∈ K, H q + ⟪p,u-q⟫_ℝ ≤ H u) (u : V) (huK : u ∈ K) :
    H q + ⟪p,u-q⟫_ℝ + μ/2 * ‖u-q‖^2 ≤ H u := by
  have ht (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
      (1-t)*(μ/2*‖u-q‖^2) ≤ H u - H q - ⟪p,u-q⟫_ℝ := by
    have hs := hH.2 huK hqK ht0.le
      (show 0 ≤ 1-t by linarith) (show t+(1-t)=1 by ring)
    have hm := hq (t • u + (1-t) • q)
      (hH.1 huK hqK ht0.le (by linarith) (by ring))
    have he : t • u + (1-t) • q - q = t • (u-q) := by module
    rw [he, real_inner_smul_right] at hm
    simp only [smul_eq_mul] at hs
    nlinarith
  have hlim : Tendsto (fun t : ℝ => (1-t)*(μ/2*‖u-q‖^2))
      (𝓝[>] (0:ℝ)) (𝓝 (μ/2*‖u-q‖^2)) := by
    have hc : Continuous (fun t : ℝ => (1-t)*(μ/2*‖u-q‖^2)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hh : μ/2*‖u-q‖^2 ≤ H u - H q - ⟪p,u-q⟫_ℝ := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht0 ht1
    exact ht t ht0 ht1
  linarith

theorem maximizers_monotone (hH : StrongConvexOn K μ H) (G : V → V)
    (hGK : ∀ p, G p ∈ K)
    (hG : ∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u) (p r : V) :
    μ * ‖G p-G r‖^2 ≤ ⟪p-r,G p-G r⟫_ℝ := by
  have h1 := strong_support hH p (G p) (hGK p) (hG p) (G r) (hGK r)
  have h2 := strong_support hH r (G r) (hGK r) (hG r) (G p) (hGK p)
  rw [norm_sub_rev (G r) (G p)] at h1
  simp only [inner_sub_left, inner_sub_right] at *
  nlinarith

theorem maximizers_lipschitz (hμ : 0 < μ) (hH : StrongConvexOn K μ H) (G : V → V)
    (hGK : ∀ p, G p ∈ K)
    (hG : ∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u) (p r : V) :
    ‖G p-G r‖ ≤ (1/μ)*‖p-r‖ := by
  have hm := maximizers_monotone hH G hGK hG p r
  have hi := real_inner_le_norm (p-r) (G p-G r)
  by_cases hz : ‖G p-G r‖ = 0
  · rw [hz]; positivity
  have hn : 0 < ‖G p-G r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hbound : μ * ‖G p-G r‖ ≤ ‖p-r‖ := by nlinarith
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ hμ).2 (by simpa [mul_comm] using hbound)

abbrev value (H : V → ℝ) (G : V → V) (p : V) : ℝ :=
  ConjugateRegularity.value H G p

theorem value_ge (G : V → V)
    (hG : ∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u)
    (p u : V) (hu : u ∈ K) :
    ⟪p,u⟫_ℝ - H u ≤ value H G p := by
  have h := hG p u hu
  simp only [inner_sub_right] at h
  dsimp [value,ConjugateRegularity.value]; linarith

theorem value_support (G : V → V) (hGK : ∀ p, G p ∈ K)
    (hG : ∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u) (p r : V) :
    value H G p + ⟪G p,r-p⟫_ℝ ≤ value H G r := by
  have h := value_ge G hG r (G p) (hGK p)
  dsimp [value,ConjugateRegularity.value] at *
  rw [inner_sub_right]
  linarith [real_inner_comm (G p) r, real_inner_comm (G p) p]

theorem value_remainder (hμ : 0 < μ) (hH : StrongConvexOn K μ H) (G : V → V)
    (hGK : ∀ p, G p ∈ K)
    (hG : ∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u) (p r : V) :
    0 ≤ value H G r - value H G p - ⟪G p,r-p⟫_ℝ ∧
    value H G r - value H G p - ⟪G p,r-p⟫_ℝ ≤ (1/μ)*‖r-p‖^2 := by
  constructor
  · linarith [value_support G hGK hG p r]
  · have hs := value_support G hGK hG r p
    have hi := real_inner_le_norm (G r-G p) (r-p)
    have hl := mul_le_mul_of_nonneg_right (maximizers_lipschitz hμ hH G hGK hG r p)
      (norm_nonneg (r-p))
    simp only [inner_sub_left, inner_sub_right] at hs hi ⊢
    nlinarith

theorem value_convex (G : V → V) (hGK : ∀ p, G p ∈ K)
    (hG : ∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u) :
    ConvexOn ℝ univ (value H G) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ r _ a b ha hb hab
  have h1 := mul_le_mul_of_nonneg_left
    (value_ge G hG p (G (a • p+b • r)) (hGK _)) ha
  have h2 := mul_le_mul_of_nonneg_left
    (value_ge G hG r (G (a • p+b • r)) (hGK _)) hb
  have he := congrArg (fun t : ℝ => t * H (G (a • p+b • r))) hab
  simp only [add_mul, one_mul] at he
  simp only [value,ConjugateRegularity.value,inner_add_left,real_inner_smul_left,smul_eq_mul] at *
  nlinarith

theorem value_hasGradientAt (hμ : 0 < μ) (hH : StrongConvexOn K μ H) (G : V → V)
    (hGK : ∀ p, G p ∈ K)
    (hG : ∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u) (p : V) :
    HasGradientAt (value H G) (G p) p := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hC : 0 < 1/μ+1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:V) (div_pos hc hC)] with h hh
  have hn : ‖h‖ < c / (1/μ+1) := by simpa [dist_eq_norm] using hh
  have hr := value_remainder hμ hH G hGK hG p (p+h)
  simp only [add_sub_cancel_left] at hr
  rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
  have hn' := (lt_div_iff₀ hC).mp hn
  have hm := mul_le_mul_of_nonneg_right hn'.le (norm_nonneg h)
  nlinarith [norm_nonneg h, sq_nonneg ‖h‖]

theorem maximizer_unique (hμ : 0 < μ) (hH : StrongConvexOn K μ H)
    (p q r : V) (hqK : q ∈ K) (hrK : r ∈ K)
    (hq : ∀ u ∈ K, H q + ⟪p,u-q⟫_ℝ ≤ H u)
    (hr : ∀ u ∈ K, H r + ⟪p,u-r⟫_ℝ ≤ H u) : q = r := by
  have hs := strong_support hH p q hqK hq r hrK
  have hw := hr q hqK
  simp only [inner_sub_right] at hs hw
  have hprod : μ/2*‖r-q‖^2 ≤ 0 := by linarith
  have hsq : ‖r-q‖^2 = 0 := le_antisymm
    ((mul_le_mul_iff_left₀ (by positivity : 0 < μ/2)).mp (by simpa [mul_comm] using hprod)) (sq_nonneg _)
  have hz : ‖r-q‖ = 0 := sq_eq_zero_iff.mp hsq
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem exists_maximizer [ProperSpace V] (hμ : 0 < μ) (hK : IsClosed K)
    (hcont : ContinuousOn H K) (p₀ q₀ : V) (hq₀ : q₀ ∈ K)
    (hbase : ∀ u ∈ K, H q₀ + ⟪p₀,u-q₀⟫_ℝ + μ/2*‖u-q₀‖^2 ≤ H u)
    (p : V) : ∃ q ∈ K, ∀ u ∈ K, H q + ⟪p,u-q⟫_ℝ ≤ H u := by
  let F : V → ℝ := fun u => H u - ⟪p,u⟫_ℝ
  let ρ : ℝ := 2*‖p₀-p‖/μ
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hF : ContinuousOn F K := hcont.sub (by fun_prop)
  have hc : IsCompact (Metric.closedBall q₀ ρ ∩ K) :=
    (isCompact_closedBall q₀ ρ).inter_right hK
  have hq₀ball : q₀ ∈ Metric.closedBall q₀ ρ ∩ K :=
    ⟨Metric.mem_closedBall_self hρ,hq₀⟩
  obtain ⟨q,hqmem,hq⟩ := hc.exists_isMinOn ⟨q₀,hq₀ball⟩ (hF.mono inter_subset_right)
  have hq0 := hq hq₀ball
  have hglobal (u : V) (huK : u ∈ K) : F q ≤ F u := by
    by_cases hu : u ∈ Metric.closedBall q₀ ρ
    · exact hq ⟨hu,huK⟩
    · have hdist : ρ < ‖u-q₀‖ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      have hm : 2*‖p₀-p‖ < ‖u-q₀‖*μ := (div_lt_iff₀ hμ).mp hdist
      have hi := real_inner_le_norm (p-p₀) (u-q₀)
      rw [norm_sub_rev p p₀] at hi
      have hb := hbase u huK
      simp only [inner_sub_left, inner_sub_right] at hi hb
      have hf : F q₀ ≤ F u := by
        dsimp [F]
        nlinarith [mul_nonneg (norm_nonneg (u-q₀))
          (show 0 ≤ ‖u-q₀‖*μ - 2*‖p₀-p‖ by linarith)]
      exact hq0.trans hf
  refine ⟨q,hqmem.2,fun u hu => ?_⟩
  have h := hglobal u hu
  dsimp [F] at h
  rw [inner_sub_right]
  linarith

theorem exists_smooth_conjugate [ProperSpace V] (hμ : 0 < μ)
    (hK : IsClosed K) (hH : StrongConvexOn K μ H) (hcont : ContinuousOn H K)
    (p₀ q₀ : V) (hq₀ : q₀ ∈ K)
    (hbase : ∀ u ∈ K, H q₀ + ⟪p₀,u-q₀⟫_ℝ ≤ H u) :
    ∃ G : V → V, (∀ p, G p ∈ K) ∧
      (∀ p u, u ∈ K → H (G p) + ⟪p,u-G p⟫_ℝ ≤ H u) ∧
      (∀ p, HasGradientAt (value H G) (G p) p) ∧
      ConvexOn ℝ univ (value H G) ∧
      LipschitzWith (Real.toNNReal (1/μ)) G := by
  classical
  have hex : ∀ p : V, ∃ q ∈ K, ∀ u ∈ K, H q + ⟪p,u-q⟫_ℝ ≤ H u :=
    exists_maximizer hμ hK hcont p₀ q₀ hq₀ (strong_support hH p₀ q₀ hq₀ hbase)
  choose G hGK hG using hex
  refine ⟨G,hGK,hG,value_hasGradientAt hμ hH G hGK hG,value_convex G hGK hG,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro p r
  simpa only [dist_eq_norm, Real.coe_toNNReal _ (one_div_pos.mpr hμ).le]
    using maximizers_lipschitz hμ hH G hGK hG p r

end ConstrainedConjugate
