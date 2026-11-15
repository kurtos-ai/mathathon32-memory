module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

/-!
# The semantic step of parameterized Fourier–Motzkin elimination

This module eliminates one real variable from finite conjunctions of weak or strict affine
inequalities. Coefficients may be arbitrary real functions of other parameters. It is a restricted
elimination theorem, not nonlinear real quantifier elimination.
-/

@[expose] public section
namespace MemorySemialgebraic.AffineElimination

/-- A uniform representation of weak and strict comparisons. -/
def Rel (strict : Bool) (a b : ℝ) : Prop := if strict then a < b else a ≤ b

lemma rel_le {s : Bool} {a b : ℝ} (h : Rel s a b) : a ≤ b := by
  cases s with
  | false => exact h
  | true => exact h.le

lemma rel_of_lt (s : Bool) {a b : ℝ} (h : a < b) : Rel s a b := by
  cases s <;> simp [Rel, h, h.le]

lemma rel_trans {s t : Bool} {a x b : ℝ} (h₁ : Rel s a x) (h₂ : Rel t x b) :
    Rel (s || t) a b := by
  cases s <;> cases t <;> simp [Rel] at * <;> linarith

lemma rel_sub (s : Bool) (a b : ℝ) : Rel s a b ↔ Rel s 0 (b - a) := by
  cases s <;> simp [Rel]

lemma rel_mul_pos (s : Bool) (k d : ℝ) (hk : 0 < k) :
    Rel s 0 (k * d) ↔ Rel s 0 d := by
  cases s <;> simp [Rel, mul_nonneg_iff_of_pos_left hk, mul_pos_iff_of_pos_left hk]

/-- A finite collection of open or closed lower and upper bounds is feasible exactly when
all opposing pairs are compatible. Empty collections and coincident closed endpoints are included. -/
theorem finite_bounds_iff (L U : Finset (ℝ × Bool)) :
    (∃ x : ℝ, (∀ l ∈ L, Rel l.2 l.1 x) ∧ (∀ u ∈ U, Rel u.2 x u.1)) ↔
      ∀ l ∈ L, ∀ u ∈ U, Rel (l.2 || u.2) l.1 u.1 := by
  classical
  constructor
  · rintro ⟨x, hL, hU⟩ l hl u hu
    exact rel_trans (hL l hl) (hU u hu)
  · intro h
    by_cases hL : L.Nonempty
    · obtain ⟨l, hl, hlmax⟩ := L.exists_max_image Prod.fst hL
      by_cases hU : U.Nonempty
      · obtain ⟨u, hu, humin⟩ := U.exists_min_image Prod.fst hU
        have hlu : l.1 ≤ u.1 := rel_le (h l hl u hu)
        by_cases hlt : l.1 < u.1
        · refine ⟨(l.1 + u.1) / 2, ?_, ?_⟩
          · intro c hc
            apply rel_of_lt
            have := hlmax c hc
            linarith
          · intro c hc
            apply rel_of_lt
            have := humin c hc
            linarith
        · have heq : l.1 = u.1 := le_antisymm hlu (le_of_not_gt hlt)
          refine ⟨l.1, ?_, ?_⟩
          · intro c hc
            cases hs : c.2 with
            | false => simpa [Rel, hs] using hlmax c hc
            | true =>
              have hh := h c hc u hu
              simpa [Rel, hs, ← heq] using hh
          · intro c hc
            cases hs : c.2 with
            | false => simpa [Rel, hs, heq] using humin c hc
            | true =>
              have hh := h l hl c hc
              simpa [Rel, hs] using hh
      · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
        refine ⟨l.1 + 1, ?_, ?_⟩
        · intro c hc
          apply rel_of_lt
          have := hlmax c hc
          linarith
        · simp [hU0]
    · have hL0 : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      by_cases hU : U.Nonempty
      · obtain ⟨u, hu, humin⟩ := U.exists_min_image Prod.fst hU
        refine ⟨u.1 - 1, ?_, ?_⟩
        · simp [hL0]
        · intro c hc
          apply rel_of_lt
          have := humin c hc
          linarith
      · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
        exact ⟨0, by simp [hL0], by simp [hU0]⟩

lemma positive_affine_iff (s : Bool) (a b x : ℝ) (ha : 0 < a) :
    Rel s 0 (a * x + b) ↔ Rel s (-b / a) x := by
  cases s with
  | false =>
    change 0 ≤ a * x + b ↔ -b / a ≤ x
    rw [div_le_iff₀ ha]
    constructor <;> intro h <;> nlinarith
  | true =>
    change 0 < a * x + b ↔ -b / a < x
    rw [div_lt_iff₀ ha]
    constructor <;> intro h <;> nlinarith

lemma negative_affine_iff (s : Bool) (a b x : ℝ) (ha : a < 0) :
    Rel s 0 (a * x + b) ↔ Rel s x (-b / a) := by
  cases s with
  | false =>
    change 0 ≤ a * x + b ↔ x ≤ -b / a
    rw [le_div_iff_of_neg ha]
    constructor <;> intro h <;> nlinarith
  | true =>
    change 0 < a * x + b ↔ x < -b / a
    rw [lt_div_iff_of_neg ha]
    constructor <;> intro h <;> nlinarith

lemma opposing_bounds_iff (s : Bool) (a b c d : ℝ) (ha : 0 < a) (hc : c < 0) :
    Rel s (-b / a) (-d / c) ↔ Rel s (b * c) (d * a) := by
  have heq : d * a - b * c = -(a * c) * ((-d / c) - (-b / a)) := by
    field_simp [ha.ne', hc.ne]
    ring
  have hpos : 0 < -(a * c) := neg_pos.mpr (mul_neg_of_pos_of_neg ha hc)
  rw [rel_sub s (-b / a) (-d / c), rel_sub s (b * c) (d * a), heq,
    rel_mul_pos s _ _ hpos]

/-- Complete one-variable Fourier–Motzkin elimination with arbitrary real coefficients,
including zero coefficients and arbitrary mixtures of strict and weak constraints. -/
theorem feasible_iff {ι : Type*} (S : Finset ι) (a b : ι → ℝ) (strict : ι → Bool) :
    (∃ x : ℝ, ∀ i ∈ S, Rel (strict i) 0 (a i * x + b i)) ↔
      (∀ i ∈ S, a i = 0 → Rel (strict i) 0 (b i)) ∧
      (∀ i ∈ S, ∀ j ∈ S, 0 < a i → a j < 0 →
        Rel (strict i || strict j) (b i * a j) (b j * a i)) := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    constructor
    · intro i hi hai
      simpa [hai] using hx i hi
    · intro i hi j hj hai haj
      apply (opposing_bounds_iff _ _ _ _ _ hai haj).mp
      exact rel_trans ((positive_affine_iff _ _ _ _ hai).mp (hx i hi))
        ((negative_affine_iff _ _ _ _ haj).mp (hx j hj))
  · rintro ⟨hzero, hpairs⟩
    let L : Finset (ℝ × Bool) := (S.filter (fun i => 0 < a i)).image
      (fun i => (-b i / a i, strict i))
    let U : Finset (ℝ × Bool) := (S.filter (fun i => a i < 0)).image
      (fun i => (-b i / a i, strict i))
    have hcompat : ∀ l ∈ L, ∀ u ∈ U, Rel (l.2 || u.2) l.1 u.1 := by
      intro l hl u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hiS, hai⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjS, haj⟩ := Finset.mem_filter.mp hj
      exact (opposing_bounds_iff _ _ _ _ _ hai haj).mpr (hpairs i hiS j hjS hai haj)
    obtain ⟨x, hxL, hxU⟩ := (finite_bounds_iff L U).mpr hcompat
    refine ⟨x, ?_⟩
    intro i hi
    rcases lt_trichotomy (a i) 0 with ha | ha | ha
    · apply (negative_affine_iff _ _ _ _ ha).mpr
      exact hxU _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩, rfl⟩)
    · simpa [ha] using hzero i hi ha
    · apply (positive_affine_iff _ _ _ _ ha).mpr
      exact hxL _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩, rfl⟩)

end MemorySemialgebraic.AffineElimination
