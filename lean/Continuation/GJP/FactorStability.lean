module
public import Continuation.GJP.FactorBounds
public import Continuation.GJP.ClosedFeasibility

@[expose] public section
noncomputable section
open Matrix Filter Topology
namespace GJP
variable {N : ℕ}

/-- Proposition 3.5: all admissible factor sequences approaching the OGM rate converge to
the unique factors (17). The method matrix is fixed, as in the source proposition. -/
theorem equation15_factor_stability
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (Ts Cs : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (rs : ℕ → ℝ)
    (hW : UnitLower W) (hr : ∀ k, 0 < rs k)
    (hTC : ∀ k, TCAdmissible (Fin.last N) (Ts k) (Cs k))
    (hPSD : ∀ k, (equation15Matrix (Fin.last N) W (Ts k) (Cs k) (rs k)).PosSemidef)
    (hrlim : Tendsto rs atTop (𝓝 (rOGM N))) :
    Tendsto (fun k => (Ts k, Cs k)) atTop (𝓝 (optimalFactorT N, 1)) := by
  choose bs hTb hb hb1 hbC hbzero using (fun k => (hTC k).exists_b)
  have hblim := equation15_mass_stability (fun _ => W) Ts Cs rs bs hr (fun _ => hW)
    hTC hPSD hTb hb hb1 hrlim
  have hbhalf : ∀ᶠ k in atTop, ∀ i, (1/2:ℝ) ≤ bs k i := by
    apply eventually_all.mpr
    intro i
    exact ((tendsto_pi_nhds.mp hblim) i).eventually (eventually_ge_nhds (by norm_num : (1/2:ℝ)<1))
  let KT : Set (Matrix (Fin (N+1)) (Fin (N+1)) ℝ) := (Set.Icc (-2:ℝ) 2).matrix
  let KC : Set (Matrix (Fin (N+1)) (Fin (N+1)) ℝ) := (Set.Icc (-1:ℝ) 1).matrix
  have hcompact : IsCompact (KT ×ˢ KC) := isCompact_Icc.matrix.prod isCompact_Icc.matrix
  letI : FirstCountableTopology (Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin (N+1) → Fin (N+1) → ℝ))
  have hmem : ∀ᶠ k in atTop, (Ts k, Cs k) ∈ KT ×ˢ KC := by
    filter_upwards [hbhalf] with k hk
    obtain ⟨hTbound, hCbound⟩ := factors_bounded_of_mass (Ts k) (Cs k) (hTC k) (bs k)
      (hTb k) (hb k) hk (hbC k) (hbzero k)
    exact ⟨hTbound, hCbound⟩
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt hmem
  intro P _ hcluster
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  have hTlim : Tendsto (fun k => Ts (φ k)) atTop (𝓝 P.1) := hlim.fst_nhds
  have hClim : Tendsto (fun k => Cs (φ k)) atTop (𝓝 P.2) := hlim.snd_nhds
  have hrlim' : Tendsto (fun k => rs (φ k)) atTop (𝓝 (rOGM N)) := hrlim.comp hφ.tendsto_atTop
  have hTC' := TCAdmissible.of_tendsto (Fin.last N) hTlim hClim (fun k => hTC (φ k))
  have hPSD' := equation15_psd_of_tendsto (Fin.last N) W hTlim hClim hrlim' (fun k => hPSD (φ k))
  obtain ⟨hT, hC, _⟩ := equation15_optimal_factors W P.1 P.2 hW hTC' hPSD'
  exact Prod.ext hT hC

/-- Any approaching feasible sequence produces an attained optimal certificate at the canonical
factors. This is the limiting-certificate step needed after PEP strong duality. -/
theorem equation15_limit_certificate
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (Ts Cs : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (rs : ℕ → ℝ)
    (hW : UnitLower W) (hr : ∀ k, 0 < rs k)
    (hTC : ∀ k, TCAdmissible (Fin.last N) (Ts k) (Cs k))
    (hPSD : ∀ k, (equation15Matrix (Fin.last N) W (Ts k) (Cs k) (rs k)).PosSemidef)
    (hrlim : Tendsto rs atTop (𝓝 (rOGM N))) :
    TCAdmissible (Fin.last N) (optimalFactorT N) 1 ∧
      (equation15Matrix (Fin.last N) W (optimalFactorT N) 1 (rOGM N)).PosSemidef := by
  have hlim := equation15_factor_stability W Ts Cs rs hW hr hTC hPSD hrlim
  have hTlim : Tendsto Ts atTop (𝓝 (optimalFactorT N)) := hlim.fst_nhds
  have hClim : Tendsto Cs atTop (𝓝 1) := hlim.snd_nhds
  exact ⟨TCAdmissible.of_tendsto (Fin.last N) hTlim hClim hTC,
    equation15_psd_of_tendsto (Fin.last N) W hTlim hClim hrlim hPSD⟩

/-- Uniqueness extends to methods with only approaching, potentially nonattained dual certificates. -/
theorem equation15_approaching_method_unique
    (W₁ W₂ : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (T₁ C₁ T₂ C₂ : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (r₁ r₂ : ℕ → ℝ)
    (hW₁ : UnitLower W₁) (hW₂ : UnitLower W₂)
    (hr₁ : ∀ k, 0 < r₁ k) (hr₂ : ∀ k, 0 < r₂ k)
    (hTC₁ : ∀ k, TCAdmissible (Fin.last N) (T₁ k) (C₁ k))
    (hTC₂ : ∀ k, TCAdmissible (Fin.last N) (T₂ k) (C₂ k))
    (hPSD₁ : ∀ k, (equation15Matrix (Fin.last N) W₁ (T₁ k) (C₁ k) (r₁ k)).PosSemidef)
    (hPSD₂ : ∀ k, (equation15Matrix (Fin.last N) W₂ (T₂ k) (C₂ k) (r₂ k)).PosSemidef)
    (hlim₁ : Tendsto r₁ atTop (𝓝 (rOGM N))) (hlim₂ : Tendsto r₂ atTop (𝓝 (rOGM N))) : W₁ = W₂ := by
  obtain ⟨hTC₁', hPSD₁'⟩ := equation15_limit_certificate W₁ T₁ C₁ r₁ hW₁ hr₁ hTC₁ hPSD₁ hlim₁
  obtain ⟨hTC₂', hPSD₂'⟩ := equation15_limit_certificate W₂ T₂ C₂ r₂ hW₂ hr₂ hTC₂ hPSD₂ hlim₂
  exact equation15_optimal_method_unique W₁ _ _ W₂ _ _ hW₁ hW₂ hTC₁' hTC₂' hPSD₁' hPSD₂'

end GJP
