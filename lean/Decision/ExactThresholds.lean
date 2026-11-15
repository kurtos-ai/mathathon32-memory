module

public import Mathlib

@[expose] public section
noncomputable section

namespace MemoryDecision

variable {D T Z : Type*}

/-- Supremum over a supplied feasible loss model, allowing infinite risk. -/
def risk (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (d : D) (t : T) : EReal :=
  ⨆ z : {z : Z // feasible d t z}, (loss d t z : EReal)

/-- The performance set is constructed from losses, without minimax values. -/
def performance (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (γ : ℝ) : Set T :=
  {t | ∃ d : D, ∃ b : ℝ, b < γ ∧ ∀ z, feasible d t z → loss d t z ≤ b}

def thresholds (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ) : Set ℝ :=
  {γ | (performance feasible loss γ ∩ memory m).Nonempty}

/-- Independent minimax definition, including the infinite-value case. -/
def value (feasible : D → T → Z → Prop) (loss : D → T → Z → ℝ)
    (memory : ℕ → Set T) (m : ℕ) : EReal :=
  ⨅ t : memory m, ⨅ d : D, risk feasible loss d t

theorem risk_le_iff (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (d : D) (t : T) (b : ℝ) :
    risk feasible loss d t ≤ (b : EReal) ↔
      ∀ z, feasible d t z → loss d t z ≤ b := by
  simp only [risk, iSup_le_iff, EReal.coe_le_coe_iff]
  exact ⟨fun h z hz => h ⟨z, hz⟩, fun h z => h z z.property⟩

theorem risk_lt_iff_uniform_bound (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (d : D) (t : T) (γ : ℝ) :
    risk feasible loss d t < (γ : EReal) ↔
      ∃ b : ℝ, b < γ ∧ ∀ z, feasible d t z → loss d t z ≤ b := by
  constructor
  · intro h
    obtain ⟨b, hb, hbγ⟩ := EReal.exists_between_coe_real h
    exact ⟨b, EReal.coe_lt_coe_iff.mp hbγ,
      (risk_le_iff feasible loss d t b).mp hb.le⟩
  · rintro ⟨b, hbγ, hb⟩
    exact ((risk_le_iff feasible loss d t b).mpr hb).trans_lt
      (EReal.coe_lt_coe_iff.mpr hbγ)

theorem mem_performance_iff (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (t : T) (γ : ℝ) :
    t ∈ performance feasible loss γ ↔ ∃ d, risk feasible loss d t < (γ : EReal) := by
  simp only [performance, Set.mem_ofPred_eq, risk_lt_iff_uniform_bound]

/-- The three-step intersection test detects exactly strict minimax thresholds.
No attainment, boundedness, compactness, or finite risk is assumed. -/
theorem threshold_iff_value_lt (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (memory : ℕ → Set T) (m : ℕ) (γ : ℝ) :
    γ ∈ thresholds feasible loss memory m ↔ value feasible loss memory m < (γ : EReal) := by
  simp only [thresholds, Set.mem_ofPred_eq, Set.inter_nonempty,
    mem_performance_iff, value, iInf_lt_iff]
  constructor
  · rintro ⟨t, ⟨d, hd⟩, ht⟩
    exact ⟨⟨t, ht⟩, d, hd⟩
  · rintro ⟨t, d, hd⟩
    exact ⟨t, ⟨d, hd⟩, t.property⟩

theorem thresholds_eq_ray_of_value_eq (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (memory : ℕ → Set T) (m : ℕ) (v : ℝ)
    (hv : value feasible loss memory m = (v : EReal)) :
    thresholds feasible loss memory m = Set.Ioi v := by
  ext γ
  simp [threshold_iff_value_lt, hv]

theorem thresholds_empty_iff_value_top (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (memory : ℕ → Set T) (m : ℕ) :
    thresholds feasible loss memory m = ∅ ↔ value feasible loss memory m = ⊤ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨γ, hγ, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hne)
    have := (threshold_iff_value_lt feasible loss memory m γ).mpr hγ
    simp [h] at this
  · intro h
    ext γ
    simp [threshold_iff_value_lt, h]

/-- Strict memory improvements are equivalent to a nonempty difference of
threshold sets, including when the worse minimax value is infinite. -/
theorem gain_iff (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (memory : ℕ → Set T) (m : ℕ) :
    value feasible loss memory (m+1) < value feasible loss memory m ↔
      (thresholds feasible loss memory (m+1) \ thresholds feasible loss memory m).Nonempty := by
  constructor
  · intro h
    obtain ⟨γ, hl, hu⟩ := EReal.exists_between_coe_real h
    refine ⟨γ, (threshold_iff_value_lt feasible loss memory (m+1) γ).mpr hl, ?_⟩
    intro hg
    exact (not_lt_of_ge hu.le) ((threshold_iff_value_lt feasible loss memory m γ).mp hg)
  · rintro ⟨γ, hl, hu⟩
    have hl' := (threshold_iff_value_lt feasible loss memory (m+1) γ).mp hl
    have hu' : (γ : EReal) ≤ value feasible loss memory m := by
      by_contra h
      exact hu ((threshold_iff_value_lt feasible loss memory m γ).mpr (lt_of_not_ge h))
    exact hl'.trans_le hu'

theorem risk_nonneg (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (d : D) (t : T)
    (hne : ∃ z, feasible d t z)
    (hnonneg : ∀ z, feasible d t z → 0 ≤ loss d t z) :
    0 ≤ risk feasible loss d t := by
  obtain ⟨z, hz⟩ := hne
  exact le_iSup_of_le ⟨z, hz⟩ (by exact_mod_cast hnonneg z hz)

theorem value_nonneg (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (memory : ℕ → Set T) (m : ℕ)
    (hne : ∀ d t, ∃ z, feasible d t z)
    (hnonneg : ∀ d t z, feasible d t z → 0 ≤ loss d t z) :
    0 ≤ value feasible loss memory m := by
  exact le_iInf fun t => le_iInf fun d =>
    risk_nonneg feasible loss d t (hne d t) (hnonneg d t)

/-- Increasing the allowed memory can only decrease the minimax value. -/
theorem value_antitone (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (memory : ℕ → Set T) (m n : ℕ)
    (h : memory m ⊆ memory n) :
    value feasible loss memory n ≤ value feasible loss memory m := by
  apply le_iInf
  intro t
  exact iInf_le_of_le ⟨t, h t.property⟩ le_rfl

theorem gain_has_rational_witness (feasible : D → T → Z → Prop)
    (loss : D → T → Z → ℝ) (memory : ℕ → Set T) (m : ℕ)
    (h : value feasible loss memory (m+1) < value feasible loss memory m) :
    ∃ q : ℚ, (q : ℝ) ∈ thresholds feasible loss memory (m+1) \
      thresholds feasible loss memory m := by
  obtain ⟨q, hl, hu⟩ := EReal.exists_rat_btwn_of_lt h
  refine ⟨q, (threshold_iff_value_lt feasible loss memory (m+1) q).mpr hl, ?_⟩
  intro hg
  exact (not_lt_of_ge hu.le) ((threshold_iff_value_lt feasible loss memory m q).mp hg)

/-- The final logical step in the smooth-convex separation proof. The
uniqueness and attainment hypotheses are substantive and explicit; this lemma
does not claim to formalize the cited optimization theorems establishing them. -/
theorem strict_separation_of_unique_attainment {W : Type*}
    (r : W → EReal) (A : Set W) (optimal : W) (v : EReal)
    (hlower : ∀ w, v ≤ r w)
    (hunique : ∀ w, r w = v → w = optimal)
    (hattain : ∃ w ∈ A, r w = sInf (r '' A))
    (hexclude : optimal ∉ A) :
    v < sInf (r '' A) := by
  obtain ⟨w, hw, hr⟩ := hattain
  rw [← hr]
  apply lt_of_le_of_ne (hlower w)
  intro heq
  exact hexclude ((hunique w heq.symm) ▸ hw)

#print axioms risk_le_iff
#print axioms risk_lt_iff_uniform_bound
#print axioms threshold_iff_value_lt
#print axioms thresholds_eq_ray_of_value_eq
#print axioms thresholds_empty_iff_value_top
#print axioms gain_iff
#print axioms risk_nonneg
#print axioms value_nonneg
#print axioms value_antitone
#print axioms gain_has_rational_witness
#print axioms strict_separation_of_unique_attainment

end MemoryDecision
