module
public import Continuation.GJP.Simplex
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact

@[expose] public section
noncomputable section
open Filter Topology
namespace GJP

variable {N : ℕ}

lemma continuous_partial_sum (N k : ℕ) : Continuous (fun δ : Fin (N+1) → ℝ => S N δ k) := by
  unfold S
  apply continuous_finset_sum
  intro i _
  by_cases hi : i.val ≤ k
  · simpa only [hi, ↓reduceIte] using continuous_apply i
  · simp only [hi, ↓reduceIte]
    exact continuous_const

lemma simplex_coordinate_le_one (δ : Fin (N+1) → ℝ) (hΔ : DeltaProp N δ) (i : Fin (N+1)) :
    δ i ≤ 1 := by
  have h := delta_le_S N δ hΔ.1 i N (by omega)
  rw [S_eq_total N δ N le_rfl, hΔ.2] at h
  exact h

lemma simplex_polynomial_bound (δ : Fin (N+1) → ℝ) (r : ℝ) (hΔ : DeltaProp N δ)
    (hPhi : Phi N δ ≤ r) (i : Fin (N+1)) (hi : i.val < N) :
    (δ i)^2 ≤ 2*r*S N δ i.val := by
  have h := delta_sq_le N δ hΔ (Phi N δ) rfl i hi
  exact h.trans (by gcongr; exact S_nonneg N δ hΔ.1 i.val)

lemma simplex_terminal_bound (δ : Fin (N+1) → ℝ) (r : ℝ) (hPhi : Phi N δ ≤ r) :
    (δ (Fin.last N))^2 ≤ r := by
  have h : phiTerm N δ (Fin.last N) ≤ Phi N δ := Finset.le_sup' _ (Finset.mem_univ _)
  have ht : (δ (Fin.last N))^2 ≤ Phi N δ := by simpa [phiTerm] using h
  exact ht.trans hPhi

lemma simplex_Phi_le_of_polynomial (δ : Fin (N+1) → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hΔ : DeltaProp N δ)
    (hpoly : ∀ i, i.val < N → (δ i)^2 ≤ 2*r*S N δ i.val)
    (hlast : (δ (Fin.last N))^2 ≤ r) : Phi N δ ≤ r := by
  apply Finset.sup'_le
  intro i _
  unfold phiTerm
  by_cases hi : i.val < N
  · simp only [hi, ↓reduceIte, partialSum]
    by_cases hs : S N δ i.val = 0
    · simp [hs, hr]
    · have hspos : 0 < S N δ i.val := lt_of_le_of_ne (S_nonneg N δ hΔ.1 i.val) (Ne.symm hs)
      apply (div_le_iff₀ (by positivity : 0 < 2*S N δ i.val)).mpr
      nlinarith [hpoly i hi]
  · simp only [hi, ↓reduceIte]
    have hilast : i = Fin.last N := Fin.ext (by simp; omega)
    simpa [hilast] using hlast

/-- The simplex constraints and polynomial projection inequalities pass to a limit. -/
theorem simplex_limit_eq_deltaStar (δs : ℕ → Fin (N+1) → ℝ) (rs : ℕ → ℝ)
    (δ : Fin (N+1) → ℝ) (hΔ : ∀ k, DeltaProp N (δs k))
    (hPhi : ∀ k, Phi N (δs k) ≤ rs k)
    (hδ : Tendsto δs atTop (𝓝 δ)) (hr : Tendsto rs atTop (𝓝 (rOGM N))) :
    δ = deltaStar N := by
  have hc (i : Fin (N+1)) : Tendsto (fun k => δs k i) atTop (𝓝 (δ i)) :=
    (tendsto_pi_nhds.mp hδ) i
  have hΔlim : DeltaProp N δ := by
    constructor
    · intro i
      exact le_of_tendsto_of_tendsto tendsto_const_nhds (hc i)
        (Eventually.of_forall (fun k => (hΔ k).1 i))
    · have hsum : Tendsto (fun k => ∑ i, δs k i) atTop (𝓝 (∑ i, δ i)) :=
        tendsto_finset_sum Finset.univ (fun i _ => hc i)
      have hsum1 : Tendsto (fun k => ∑ i, δs k i) atTop (𝓝 (1:ℝ)) := by
        simpa only [show (fun k => ∑ i, δs k i) = (fun _ => (1:ℝ)) from
          funext (fun k => (hΔ k).2)] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (1:ℝ)))
      exact tendsto_nhds_unique hsum hsum1
  have hpoly : ∀ i, i.val < N → (δ i)^2 ≤ 2*rOGM N*S N δ i.val := by
    intro i hi
    have hS : Tendsto (fun k => S N (δs k) i.val) atTop (𝓝 (S N δ i.val)) :=
      (continuous_partial_sum N i.val).tendsto δ |>.comp hδ
    exact le_of_tendsto_of_tendsto ((hc i).pow 2) ((tendsto_const_nhds.mul hr).mul hS)
      (Eventually.of_forall (fun k => simplex_polynomial_bound (δs k) (rs k) (hΔ k) (hPhi k) i hi))
  have hlast : (δ (Fin.last N))^2 ≤ rOGM N :=
    le_of_tendsto_of_tendsto ((hc (Fin.last N)).pow 2) hr
      (Eventually.of_forall (fun k => simplex_terminal_bound (δs k) (rs k) (hPhi k)))
  have hle := simplex_Phi_le_of_polynomial δ (rOGM N) (rOGM_nonneg N) hΔlim hpoly hlast
  exact funext (uniqueness N δ hΔlim (le_antisymm hle (rOGM_leq_Phi N δ hΔlim)))

/-- Near-optimal simplex projections converge to the unique optimal vector, without
assuming continuity of the `0/0` convention outside the simplex. -/
theorem simplex_stability (δs : ℕ → Fin (N+1) → ℝ) (rs : ℕ → ℝ)
    (hΔ : ∀ k, DeltaProp N (δs k)) (hPhi : ∀ k, Phi N (δs k) ≤ rs k)
    (hr : Tendsto rs atTop (𝓝 (rOGM N))) : Tendsto δs atTop (𝓝 (deltaStar N)) := by
  have hcompact : IsCompact (Set.Icc (0 : Fin (N+1) → ℝ) 1) := isCompact_Icc
  have hmem : ∀ᶠ k in atTop, δs k ∈ Set.Icc (0 : Fin (N+1) → ℝ) 1 :=
    Eventually.of_forall (fun k => ⟨(hΔ k).1, fun i => simplex_coordinate_le_one (δs k) (hΔ k) i⟩)
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt hmem
  intro δ _ hcluster
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  exact simplex_limit_eq_deltaStar (δs ∘ φ) (rs ∘ φ) δ
    (fun k => hΔ (φ k)) (fun k => hPhi (φ k)) hlim (hr.comp hφ.tendsto_atTop)

end GJP
