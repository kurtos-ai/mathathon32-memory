module
public import Mathlib
@[expose] public section
noncomputable section
namespace FiniteConvexInterpolation
open scoped RealInnerProductSpace
variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def RelativeSubgradient (K : Set E) (f : E → ℝ) (x g : E) : Prop :=
  ∀ y ∈ K, f x + ⟪g, y-x⟫ ≤ f y

def plane (value : ℝ) (slope site : E) (x : E) : ℝ := value + ⟪slope,x-site⟫

def envelope (sites slopes : ι → E) (values : ι → ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => plane (values i) (slopes i) (sites i) x)

theorem plane_le_envelope (sites slopes : ι → E) (values : ι → ℝ) (i : ι) (x : E) :
    plane (values i) (slopes i) (sites i) x ≤ envelope sites slopes values x := by
  unfold envelope
  exact Finset.le_sup' (fun j => plane (values j) (slopes j) (sites j) x) (Finset.mem_univ i)

theorem envelope_at_site (sites slopes : ι → E) (values : ι → ℝ)
    (h : ∀ i j, values i + ⟪slopes i,sites j-sites i⟫ ≤ values j) (j : ι) :
    envelope sites slopes values (sites j) = values j := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => h i j)
  · simpa [plane] using plane_le_envelope sites slopes values j (sites j)

theorem plane_combination (value : ℝ) (slope site x y : E) (a b : ℝ) (hab : a+b=1) :
    plane value slope site (a • x + b • y) =
      a * plane value slope site x + b * plane value slope site y := by
  simp only [plane, inner_sub_right, inner_add_right, inner_smul_right]
  linear_combination -(value - ⟪slope,site⟫) * hab

theorem envelope_convex (sites slopes : ι → E) (values : ι → ℝ) :
    ConvexOn ℝ Set.univ (envelope sites slopes values) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply Finset.sup'_le
  intro i _
  rw [plane_combination _ _ _ _ _ a b hab]
  exact add_le_add (mul_le_mul_of_nonneg_left (plane_le_envelope sites slopes values i x) ha)
    (mul_le_mul_of_nonneg_left (plane_le_envelope sites slopes values i y) hb)

theorem active_slope_subgradient (sites slopes : ι → E) (values : ι → ℝ) (x : E) (i : ι)
    (h : envelope sites slopes values x = plane (values i) (slopes i) (sites i) x) :
    RelativeSubgradient Set.univ (envelope sites slopes values) x (slopes i) := by
  intro y _
  rw [h]
  have heq : plane (values i) (slopes i) (sites i) x + ⟪slopes i,y-x⟫ =
      plane (values i) (slopes i) (sites i) y := by
    simp only [plane,inner_sub_right]
    ring
  rw [heq]
  exact plane_le_envelope sites slopes values i y

theorem envelope_subgradient_everywhere (sites slopes : ι → E) (values : ι → ℝ) (x : E) :
    ∃ i : ι, RelativeSubgradient Set.univ (envelope sites slopes values) x (slopes i) := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => plane (values i) (slopes i) (sites i) x)
  exact ⟨i,active_slope_subgradient sites slopes values x i hi⟩

theorem envelope_data_subgradient (sites slopes : ι → E) (values : ι → ℝ)
    (h : ∀ i j, values i + ⟪slopes i,sites j-sites i⟫ ≤ values j) (i : ι) :
    RelativeSubgradient Set.univ (envelope sites slopes values) (sites i) (slopes i) := by
  apply active_slope_subgradient
  rw [envelope_at_site sites slopes values h]
  simp [plane]

theorem interpolation_iff (K : Set E) (hK : Convex ℝ K)
    (sites slopes : ι → E) (values : ι → ℝ) (hsite : ∀ i, sites i ∈ K) :
    (∀ i j, values i + ⟪slopes i,sites j-sites i⟫ ≤ values j) ↔
    ∃ f : E → ℝ, ConvexOn ℝ K f ∧
      (∀ x ∈ K, ∃ g, RelativeSubgradient K f x g) ∧
      ∀ i, f (sites i) = values i ∧ RelativeSubgradient K f (sites i) (slopes i) := by
  constructor
  · intro h
    refine ⟨envelope sites slopes values, ?_, ?_, ?_⟩
    · exact ⟨hK,fun x _ y _ a b ha hb hab =>
        (envelope_convex sites slopes values).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab⟩
    · intro x _
      obtain ⟨i,hi⟩ := envelope_subgradient_everywhere sites slopes values x
      exact ⟨slopes i,fun y _ => hi y (Set.mem_univ y)⟩
    · intro i
      exact ⟨envelope_at_site sites slopes values h i,
        fun y _ => envelope_data_subgradient sites slopes values h i y (Set.mem_univ y)⟩
  · rintro ⟨f,_,_,hf⟩ i j
    have h := (hf i).2 (sites j) (hsite j)
    rwa [(hf i).1,(hf j).1] at h

theorem bounded_subgradient_everywhere (sites slopes : ι → E) (values : ι → ℝ)
    (M : ℝ) (hM : ∀ i, ‖slopes i‖ ≤ M) (x : E) :
    ∃ g, RelativeSubgradient Set.univ (envelope sites slopes values) x g ∧ ‖g‖ ≤ M := by
  obtain ⟨i,hi⟩ := envelope_subgradient_everywhere sites slopes values x
  exact ⟨slopes i,hi,hM i⟩

theorem zero_slope_minimizer (sites slopes : ι → E) (values : ι → ℝ)
    (h : ∀ i j, values i + ⟪slopes i,sites j-sites i⟫ ≤ values j)
    (i : ι) (hi : slopes i = 0) :
    ∀ y, envelope sites slopes values (sites i) ≤ envelope sites slopes values y := by
  intro y
  simpa [hi] using envelope_data_subgradient sites slopes values h i y (Set.mem_univ y)

end FiniteConvexInterpolation
