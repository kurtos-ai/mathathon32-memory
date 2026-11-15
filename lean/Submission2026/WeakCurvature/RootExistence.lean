module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace Submission2026.WeakCurvature

/-- Abstract root existence/uniqueness for strictly increasing continuous maps.
This is the reusable analysis core for the Appendix F scalar balance equation:
`F_N(ν) = capR^N(0) + sqrt((ν-4c)/(2a))`. Under the source hypotheses `F_N`
is continuous and strictly increasing on `[4c, u_c]` with `F_N(4c) < 1 < F_N(u_c)`.
The next two lemmas isolate the IVT + monotonicity argument so the concrete
capacity estimates can be supplied as separate hypotheses without creating a
dependency on unfinished modules. -/

-- Existence via IVT on a compact interval.
theorem exists_root_of_strictMonoOn
    {l u : ℝ} {F : ℝ → ℝ}
    (hlu : l ≤ u)
    (hcont : ContinuousOn F (Set.Icc l u))
    (hl : F l < 1) (hu : 1 < F u) :
    ∃ r ∈ Set.Icc l u, F r = 1 := by
  have h1 : (1 : ℝ) ∈ Set.Icc (F l) (F u) := ⟨le_of_lt hl, le_of_lt hu⟩
  exact intermediate_value_Icc hlu hcont h1

-- Uniqueness from strict monotonicity on the interval.
theorem unique_root_of_strictMonoOn
    {l u : ℝ} {F : ℝ → ℝ}
    (hmono : StrictMonoOn F (Set.Icc l u))
    (r₁ r₂ : ℝ) (hr₁ : r₁ ∈ Set.Icc l u) (hr₂ : r₂ ∈ Set.Icc l u)
    (hF₁ : F r₁ = 1) (hF₂ : F r₂ = 1) :
    r₁ = r₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hmono hr₁ hr₂ hlt
    rw [hF₁, hF₂] at this
    exact lt_irrefl _ this
  · have := hmono hr₂ hr₁ hgt
    rw [hF₁, hF₂] at this
    exact lt_irrefl _ this

-- Combined existence + uniqueness with interior location `(l,u)`.
theorem exists_unique_root_of_strictMonoOn
    {l u : ℝ} {F : ℝ → ℝ}
    (hlu : l < u)
    (hcont : ContinuousOn F (Set.Icc l u))
    (hmono : StrictMonoOn F (Set.Icc l u))
    (hl : F l < 1) (hu : 1 < F u) :
    ∃ r ∈ Set.Ioo l u, F r = 1 ∧
      ∀ r' ∈ Set.Icc l u, F r' = 1 → r' = r := by
  obtain ⟨r, hr_mem, hr_eq⟩ := exists_root_of_strictMonoOn (le_of_lt hlu) hcont hl hu
  have hr_ne_l : r ≠ l := by
    intro h
    rw [h] at hr_eq
    linarith
  have hr_ne_u : r ≠ u := by
    intro h
    rw [h] at hr_eq
    linarith
  have hr_lt_u : r < u := lt_of_le_of_ne hr_mem.2 hr_ne_u
  have hl_lt_r : l < r := lt_of_le_of_ne hr_mem.1 (Ne.symm hr_ne_l)
  have hr_oo : r ∈ Set.Ioo l u := ⟨hl_lt_r, hr_lt_u⟩
  refine ⟨r, hr_oo, hr_eq, ?_⟩
  intro r' hr'_mem hr'_eq
  exact unique_root_of_strictMonoOn hmono r' r hr'_mem hr_mem hr'_eq hr_eq

-- Packaging as `∃!` (exists unique) for convenience.
theorem existsUnique_root_of_strictMonoOn
    {l u : ℝ} {F : ℝ → ℝ}
    (hlu : l < u)
    (hcont : ContinuousOn F (Set.Icc l u))
    (hmono : StrictMonoOn F (Set.Icc l u))
    (hl : F l < 1) (hu : 1 < F u) :
    ∃! r, r ∈ Set.Ioo l u ∧ F r = 1 := by
  obtain ⟨r, hr_oo, hr_eq, huniq_closed⟩ := exists_unique_root_of_strictMonoOn hlu hcont hmono hl hu
  refine ⟨r, ⟨hr_oo, hr_eq⟩, ?_⟩
  intro y hy
  have hy_cc : y ∈ Set.Icc l u := Set.Ioo_subset_Icc_self hy.1
  have := huniq_closed y hy_cc hy.2
  rw [this]

#print axioms exists_root_of_strictMonoOn
#print axioms unique_root_of_strictMonoOn
#print axioms exists_unique_root_of_strictMonoOn
#print axioms existsUnique_root_of_strictMonoOn

end Submission2026.WeakCurvature
