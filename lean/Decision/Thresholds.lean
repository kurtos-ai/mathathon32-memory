module

/-
Real-valued threshold helpers (partial formalization).

The declarations below treat a real-valued risk function with explicit
nonemptiness and bounded-below hypotheses. They do not formalize the report's
extended nonnegative risks, risk=+infinity, V_m=+infinity, finite loss model,
or full threshold theorem. A no-method lemma is not a model of infinite risk.
The strict-uniform-bound lemma is a real-valued implication only; it is not
the claimed extended-risk uniform equivalence.
-/
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace Decision
variable {T : Type*}
def feasibleThresholds (riskOf : T → ℝ) (Qm : ℕ → T → Prop) (m : ℕ) : Set ℝ :=
  { γ | ∃ t : T, Qm m t ∧ riskOf t < γ }
def minimaxValue (riskOf : T → ℝ) (Qm : ℕ → T → Prop) (m : ℕ) : ℝ :=
  sInf { r | ∃ t : T, Qm m t ∧ riskOf t = r }
def riskImage (riskOf : T → ℝ) (Qm : ℕ → T → Prop) (m : ℕ) : Set ℝ :=
  { r | ∃ t : T, Qm m t ∧ riskOf t = r }

theorem feasibleThresholds_empty_of_no_method (riskOf : T → ℝ)
    (Qm : ℕ → T → Prop) (m : ℕ) (hempty : ∀ t : T, ¬ Qm m t) :
    feasibleThresholds riskOf Qm m = ∅ := by
  ext γ
  simp only [feasibleThresholds, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  constructor
  · rintro ⟨_, ht, _⟩; exact absurd ht (hempty _)
  · intro h; exact absurd h (by simp)

theorem mem_feasibleThresholds_iff_lt_minimax (riskOf : T → ℝ)
    (Qm : ℕ → T → Prop) (m : ℕ) (γ : ℝ)
    (hne : (riskImage riskOf Qm m).Nonempty)
    (hbdd : BddBelow (riskImage riskOf Qm m)) :
    γ ∈ feasibleThresholds riskOf Qm m ↔ minimaxValue riskOf Qm m < γ := by
  unfold feasibleThresholds minimaxValue riskImage at *
  constructor
  · rintro ⟨t, ht, hlt⟩
    exact (csInf_le hbdd ⟨t, ht, rfl⟩).trans_lt hlt
  · intro hlt
    -- sInf S < γ → ∃ s ∈ S, s < γ  (otherwise γ ≤ sInf)
    have h_exists : ∃ s : ℝ, s ∈ { r : ℝ | ∃ t : T, Qm m t ∧ riskOf t = r } ∧ s < γ := by
      by_contra h_all
      -- h_all : ¬ ∃ s ∈ S, s < γ  →  ∀ s ∈ S, γ ≤ s
      have hge : ∀ s ∈ { r : ℝ | ∃ t : T, Qm m t ∧ riskOf t = r }, γ ≤ s := by
        intro s hs
        have hns : ¬ s < γ := fun hlt2 => h_all ⟨s, hs, hlt2⟩
        linarith
      have : γ ≤ sInf { r : ℝ | ∃ t : T, Qm m t ∧ riskOf t = r } := le_csInf hne hge
      linarith
    obtain ⟨s, hs_mem, hs_lt⟩ := h_exists
    obtain ⟨t, ht, rfl⟩ := hs_mem
    exact ⟨t, ht, hs_lt⟩

theorem feasibleThresholds_eq_Ioi (riskOf : T → ℝ)
    (Qm : ℕ → T → Prop) (m : ℕ)
    (hne : (riskImage riskOf Qm m).Nonempty)
    (hbdd : BddBelow (riskImage riskOf Qm m)) :
    feasibleThresholds riskOf Qm m = Set.Ioi (minimaxValue riskOf Qm m) := by
  ext γ
  rw [mem_feasibleThresholds_iff_lt_minimax riskOf Qm m γ hne hbdd]
  rfl

theorem gain_iff (riskOf : T → ℝ)
    (Qm : ℕ → T → Prop) (m : ℕ)
    (hne_m : (riskImage riskOf Qm m).Nonempty)
    (hbdd_m : BddBelow (riskImage riskOf Qm m))
    (hne_mp1 : (riskImage riskOf Qm (m+1)).Nonempty)
    (hbdd_mp1 : BddBelow (riskImage riskOf Qm (m+1))) :
    minimaxValue riskOf Qm (m + 1) < minimaxValue riskOf Qm m ↔
      (feasibleThresholds riskOf Qm (m + 1) \ feasibleThresholds riskOf Qm m).Nonempty := by
  have hFm := feasibleThresholds_eq_Ioi riskOf Qm m hne_m hbdd_m
  have hFmp1 := feasibleThresholds_eq_Ioi riskOf Qm (m+1) hne_mp1 hbdd_mp1
  rw [hFm, hFmp1]
  constructor
  · intro hlt
    refine ⟨(minimaxValue riskOf Qm m + minimaxValue riskOf Qm (m+1)) / 2, ?_⟩
    rw [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioi]
    constructor
    · linarith
    · intro h; linarith
  · intro ⟨γ, hmem⟩
    rw [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioi] at hmem
    obtain ⟨h1, h2⟩ := hmem
    linarith

theorem feasibleThresholds_mono (riskOf : T → ℝ) (Qm : ℕ → T → Prop)
    (hmono : ∀ m t, Qm m t → Qm (m + 1) t) (m : ℕ) :
    feasibleThresholds riskOf Qm m ⊆ feasibleThresholds riskOf Qm (m + 1) := by
  intro γ ⟨t, ht, hlt⟩
  exact ⟨t, hmono m t ht, hlt⟩

theorem uniform_of_sup_lt {S : Set ℝ} {b γ : ℝ}
    (hS : S.Nonempty) (hle : ∀ x ∈ S, x ≤ b) (hbγ : b < γ)
    (hS_bdd : BddAbove S) :
    sSup S < γ :=
  lt_of_le_of_lt (csSup_le hS hle) hbγ

end Decision
