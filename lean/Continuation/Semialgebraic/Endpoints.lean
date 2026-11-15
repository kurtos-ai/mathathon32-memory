module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Concrete rational-polynomial formulas and algebraicity of their frontier.
No quantifier-elimination algorithm or root-isolation algorithm is assumed or
implemented in this module. -/
@[expose] public section
namespace MemorySemialgebraic

noncomputable section

def toPoly (p : MvPolynomial (Fin 1) ℚ) : Polynomial ℚ :=
  (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) p

lemma toPoly_injective : Function.Injective toPoly := by
  intro a b hab
  exact (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).injective hab

lemma toPoly_eq_zero_iff {p : MvPolynomial (Fin 1) ℚ} : toPoly p = 0 ↔ p = 0 := by
  have h_inj : Function.Injective toPoly := toPoly_injective
  have h0 : toPoly (0 : MvPolynomial (Fin 1) ℚ) = 0 := by simp [toPoly]
  constructor
  · intro h
    have : toPoly p = toPoly 0 := by rw [h, h0]
    exact h_inj this
  · intro h
    rw [h, h0]

lemma toPoly_ne_zero_of_ne_zero {p : MvPolynomial (Fin 1) ℚ} (h : p ≠ 0) : toPoly p ≠ 0 := by
  intro h0
  exact h ((toPoly_eq_zero_iff (p := p)).mp h0)

def evalSingle (p : MvPolynomial (Fin 1) ℚ) (r : ℝ) : ℝ :=
  Polynomial.aeval r (toPoly p)

lemma evalSingle_continuous (p : MvPolynomial (Fin 1) ℚ) :
    Continuous (fun r : ℝ => evalSingle p r) := by
  simp only [evalSingle]
  exact Polynomial.continuous_aeval (toPoly p)

lemma evalSingle_eq_MvPolynomial_eval (p : MvPolynomial (Fin 1) ℚ) (γ : ℝ) :
    evalSingle p γ = p.eval₂ (algebraMap ℚ ℝ) (fun _ => γ) := by
  have h := MvPolynomial.eval₂_const_uniqueAlgEquiv (R := ℚ) (σ := Fin 1)
    (f := p) (φ := algebraMap ℚ ℝ) (a := γ)
  unfold evalSingle toPoly
  have haeval_eq : Polynomial.aeval γ ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) p) =
      ((MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) p).eval₂ (algebraMap ℚ ℝ) γ := rfl
  rw [haeval_eq]
  exact h

def evalPolyQ {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ) : ℝ :=
  p.eval₂ (algebraMap ℚ ℝ) x

lemma evalPolyQ_single_eq (p : MvPolynomial (Fin 1) ℚ) (γ : ℝ) :
    evalPolyQ p (fun _ => γ) = evalSingle p γ := by
  have h := evalSingle_eq_MvPolynomial_eval p γ
  simp only [evalPolyQ]
  rw [h]

inductive QFFormula : ℕ → Type where
  | atomEq : MvPolynomial (Fin n) ℚ → QFFormula n
  | atomLt : MvPolynomial (Fin n) ℚ → QFFormula n
  | atomLe : MvPolynomial (Fin n) ℚ → QFFormula n
  | and : QFFormula n → QFFormula n → QFFormula n
  | or : QFFormula n → QFFormula n → QFFormula n
  | not : QFFormula n → QFFormula n
  | tru : QFFormula n
  | fls : QFFormula n

namespace QFFormula

def eval {n : ℕ} : QFFormula n → (Fin n → ℝ) → Prop
  | atomEq p => fun x => evalPolyQ p x = 0
  | atomLt p => fun x => evalPolyQ p x < 0
  | atomLe p => fun x => evalPolyQ p x ≤ 0
  | and φ ψ => fun x => eval φ x ∧ eval ψ x
  | or φ ψ => fun x => eval φ x ∨ eval ψ x
  | not φ => fun x => ¬ eval φ x
  | tru => fun _ => True
  | fls => fun _ => False

def solutionSet {n : ℕ} (φ : QFFormula n) : Set (Fin n → ℝ) :=
  { x | φ.eval x }

def solutionSet1 (φ : QFFormula 1) : Set ℝ :=
  { r | φ.eval (fun _ => r) }

def polySet {n : ℕ} : QFFormula n → Set (MvPolynomial (Fin n) ℚ)
  | atomEq p => {p}
  | atomLt p => {p}
  | atomLe p => {p}
  | and φ ψ => polySet φ ∪ polySet ψ
  | or φ ψ => polySet φ ∪ polySet ψ
  | not φ => polySet φ
  | tru => ∅
  | fls => ∅

end QFFormula

section ZeroLocus

def zeroSet (Ps : Finset (MvPolynomial (Fin 1) ℚ)) : Set ℝ :=
  { γ : ℝ | ∀ p ∈ Ps, evalSingle p γ = 0 }

lemma isClosed_singleton_zero (p : MvPolynomial (Fin 1) ℚ) :
    IsClosed { γ : ℝ | evalSingle p γ = 0 } := by
  have hcont := evalSingle_continuous p
  have : { γ : ℝ | evalSingle p γ = 0 } = (fun γ => evalSingle p γ) ⁻¹' {0} := rfl
  rw [this]
  exact IsClosed.preimage hcont isClosed_singleton

lemma isClosed_zeroSet (Ps : Finset (MvPolynomial (Fin 1) ℚ)) :
    IsClosed (zeroSet Ps) := by
  have h_inter : zeroSet Ps = ⋂ p ∈ Ps, { γ | evalSingle p γ = 0 } := by
    ext γ
    simp [zeroSet, Set.mem_iInter]
  rw [h_inter]
  apply isClosed_biInter
  intro p _
  exact isClosed_singleton_zero p

lemma frontier_subset_zeroSet (Ps : Finset (MvPolynomial (Fin 1) ℚ)) :
    frontier (zeroSet Ps) ⊆ zeroSet Ps := by
  have hclosed := isClosed_zeroSet Ps
  have hcl : closure (zeroSet Ps) = zeroSet Ps := hclosed.closure_eq
  intro x hx
  have hx_closure : x ∈ closure (zeroSet Ps) := by
    have hfront_eq : frontier (zeroSet Ps) = closure (zeroSet Ps) \ interior (zeroSet Ps) := rfl
    rw [hfront_eq] at hx
    exact hx.1
  rw [hcl] at hx_closure
  exact hx_closure

end ZeroLocus

section Algebraic

theorem zero_mem_algebraic (p : MvPolynomial (Fin 1) ℚ) (γ : ℝ)
    (hp_ne : p ≠ 0) (hzero : evalSingle p γ = 0) : IsAlgebraic (R := ℚ) γ := by
  have hpoly_ne : toPoly p ≠ 0 := toPoly_ne_zero_of_ne_zero hp_ne
  have hzero' : Polynomial.aeval γ (toPoly p) = 0 := hzero
  exact ⟨toPoly p, hpoly_ne, hzero'⟩

theorem frontier_zeroSet_algebraic
    (Ps : Finset (MvPolynomial (Fin 1) ℚ))
    (h_nonzero : ∃ p ∈ Ps, p ≠ 0)
    (γ : ℝ) (hmem : γ ∈ frontier (zeroSet Ps)) : IsAlgebraic (R := ℚ) γ := by
  have h_sub := frontier_subset_zeroSet Ps hmem
  have h_all : ∀ p ∈ Ps, evalSingle p γ = 0 := h_sub
  obtain ⟨p, hp_mem, hp_ne⟩ := h_nonzero
  have hzero : evalSingle p γ = 0 := h_all p hp_mem
  exact zero_mem_algebraic p γ hp_ne hzero

end Algebraic

section QFFrontier

def QF_zeroLocus (φ : QFFormula 1) : Set ℝ :=
  { γ | ∃ p ∈ φ.polySet, evalSingle p γ = 0 }

def QF_zeroLocus_nonZero (φ : QFFormula 1) : Set ℝ :=
  { γ | ∃ p ∈ φ.polySet, p ≠ 0 ∧ evalSingle p γ = 0 }

lemma poly_sign_stable {p : MvPolynomial (Fin 1) ℚ} {γ : ℝ} (h : evalSingle p γ ≠ 0) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε → evalSingle p y ≠ 0 ∧
      (0 < evalSingle p γ → 0 < evalSingle p y) ∧
      (evalSingle p γ < 0 → evalSingle p y < 0) := by
  have hcont := evalSingle_continuous p
  by_cases hpos : 0 < evalSingle p γ
  · have hmem : γ ∈ (fun y => evalSingle p y) ⁻¹' Set.Ioi 0 := by simp [Set.mem_preimage, hpos]
    have hopen : IsOpen ((fun y => evalSingle p y) ⁻¹' Set.Ioi 0) := isOpen_Ioi.preimage hcont
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
    refine ⟨ε, hε_pos, fun y hy => ?_⟩
    have hy_mem : y ∈ (fun y => evalSingle p y) ⁻¹' Set.Ioi 0 := hball hy
    simp [Set.mem_preimage] at hy_mem
    refine ⟨ne_of_gt hy_mem, fun _ => hy_mem, fun hneg => ?_⟩
    have : 0 < evalSingle p y := hy_mem
    linarith
  · by_cases hneg : evalSingle p γ < 0
    · have hmem : γ ∈ (fun y => evalSingle p y) ⁻¹' Set.Iio 0 := by simp [Set.mem_preimage, hneg]
      have hopen : IsOpen ((fun y => evalSingle p y) ⁻¹' Set.Iio 0) := isOpen_Iio.preimage hcont
      obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
      refine ⟨ε, hε_pos, fun y hy => ?_⟩
      have hy_mem : y ∈ (fun y => evalSingle p y) ⁻¹' Set.Iio 0 := hball hy
      simp [Set.mem_preimage] at hy_mem
      refine ⟨ne_of_lt hy_mem, fun hpos2 => ?_, fun _ => hy_mem⟩
      have : 0 < evalSingle p y := by linarith [hy_mem]
      linarith
    · exfalso
      exact h (by
        have h_zero : evalSingle p γ = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        exact h_zero)

lemma atom_stable_of_nonzero {p : MvPolynomial (Fin 1) ℚ} {γ : ℝ} (h : evalSingle p γ ≠ 0) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε →
      ((evalSingle p y = 0) ↔ (evalSingle p γ = 0)) ∧
      ((evalSingle p y < 0) ↔ (evalSingle p γ < 0)) ∧
      ((evalSingle p y ≤ 0) ↔ (evalSingle p γ ≤ 0)) := by
  obtain ⟨ε, hε_pos, hstable⟩ := poly_sign_stable h
  refine ⟨ε, hε_pos, fun y hy => ?_⟩
  have ⟨hne, hpos_imp, hneg_imp⟩ := hstable y hy
  have h_eq_false : evalSingle p y ≠ 0 := hne
  have h_eq_false_γ : evalSingle p γ ≠ 0 := h
  constructor
  · constructor
    · intro heq; exact (h_eq_false heq).elim
    · intro heq; exact (h_eq_false_γ heq).elim
  constructor
  · constructor
    · intro hlt
      by_contra h_not_neg
      have h_ge : 0 ≤ evalSingle p γ := not_lt.mp h_not_neg
      have h_gt : 0 < evalSingle p γ := lt_of_le_of_ne h_ge (Ne.symm h_eq_false_γ)
      have : 0 < evalSingle p y := hpos_imp h_gt
      exact not_lt.mpr (le_of_lt this) hlt
    · intro hlt
      exact hneg_imp hlt
  · constructor
    · intro hle
      have hlt : evalSingle p y < 0 := lt_of_le_of_ne hle h_eq_false
      have hlt_γ : evalSingle p γ < 0 := by
        by_contra h_not
        have h_ge_γ : 0 ≤ evalSingle p γ := not_lt.mp h_not
        have h_gt_γ : 0 < evalSingle p γ := lt_of_le_of_ne h_ge_γ (Ne.symm h_eq_false_γ)
        have : 0 < evalSingle p y := hpos_imp h_gt_γ
        exact not_lt.mpr (le_of_lt this) hlt
      exact le_of_lt hlt_γ
    · intro hle
      have hlt_γ' : evalSingle p γ < 0 := by
        have h_ne_γ : evalSingle p γ ≠ 0 := h_eq_false_γ
        exact lt_of_le_of_ne hle h_ne_γ
      have : evalSingle p y < 0 := hneg_imp hlt_γ'
      exact le_of_lt this

lemma atom_stable_zero_poly (p : MvPolynomial (Fin 1) ℚ) (hp_zero : p = 0) (γ : ℝ) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε →
      ((evalSingle p y = 0) ↔ (evalSingle p γ = 0)) ∧
      ((evalSingle p y < 0) ↔ (evalSingle p γ < 0)) ∧
      ((evalSingle p y ≤ 0) ↔ (evalSingle p γ ≤ 0)) := by
  have h_eq : ∀ y, evalSingle p y = 0 := by
    intro y
    rw [hp_zero]
    simp [evalSingle, toPoly]
  refine ⟨1, by norm_num, fun y _ => ?_⟩
  simp [h_eq y, h_eq γ]

lemma atom_stable {p : MvPolynomial (Fin 1) ℚ} {γ : ℝ}
    (h : γ ∉ QF_zeroLocus_nonZero (QFFormula.atomEq p)) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε →
      ((evalSingle p y = 0) ↔ (evalSingle p γ = 0)) ∧
      ((evalSingle p y < 0) ↔ (evalSingle p γ < 0)) ∧
      ((evalSingle p y ≤ 0) ↔ (evalSingle p γ ≤ 0)) := by
  simp only [QFFormula.polySet, QF_zeroLocus_nonZero, Set.mem_setOf_eq] at h
  by_cases hp_ne : p ≠ 0
  · have h_not_zero : evalSingle p γ ≠ 0 := by
      intro heq
      exact h ⟨p, rfl, hp_ne, heq⟩
    exact atom_stable_of_nonzero h_not_zero
  · have hp_zero : p = 0 := by push_neg at hp_ne; exact hp_ne
    exact atom_stable_zero_poly p hp_zero γ

lemma eval_atomEq_stable {p : MvPolynomial (Fin 1) ℚ} {γ : ℝ}
    (h : γ ∉ QF_zeroLocus_nonZero (QFFormula.atomEq p)) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε → ((evalSingle p y = 0) ↔ (evalSingle p γ = 0)) := by
  obtain ⟨ε, hε, hstab⟩ := atom_stable (p:=p) (γ:=γ) h
  exact ⟨ε, hε, fun y hy => (hstab y hy).1⟩

lemma eval_atomLt_stable {p : MvPolynomial (Fin 1) ℚ} {γ : ℝ}
    (h : γ ∉ QF_zeroLocus_nonZero (QFFormula.atomLt p)) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε → ((evalSingle p y < 0) ↔ (evalSingle p γ < 0)) := by
  simp only [QFFormula.polySet, QF_zeroLocus_nonZero, Set.mem_setOf_eq] at h
  by_cases hp_ne : p ≠ 0
  · have h_not_zero : evalSingle p γ ≠ 0 := by
      intro heq
      exact h ⟨p, rfl, hp_ne, heq⟩
    obtain ⟨ε, hε, hstab⟩ := atom_stable_of_nonzero h_not_zero
    exact ⟨ε, hε, fun y hy => (hstab y hy).2.1⟩
  · have hp_zero : p = 0 := by push_neg at hp_ne; exact hp_ne
    obtain ⟨ε, hε, hstab⟩ := atom_stable_zero_poly p hp_zero γ
    exact ⟨ε, hε, fun y hy => (hstab y hy).2.1⟩

lemma eval_atomLe_stable {p : MvPolynomial (Fin 1) ℚ} {γ : ℝ}
    (h : γ ∉ QF_zeroLocus_nonZero (QFFormula.atomLe p)) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε → ((evalSingle p y ≤ 0) ↔ (evalSingle p γ ≤ 0)) := by
  simp only [QFFormula.polySet, QF_zeroLocus_nonZero, Set.mem_setOf_eq] at h
  by_cases hp_ne : p ≠ 0
  · have h_not_zero : evalSingle p γ ≠ 0 := by
      intro heq
      exact h ⟨p, rfl, hp_ne, heq⟩
    obtain ⟨ε, hε, hstab⟩ := atom_stable_of_nonzero h_not_zero
    exact ⟨ε, hε, fun y hy => (hstab y hy).2.2⟩
  · have hp_zero : p = 0 := by push_neg at hp_ne; exact hp_ne
    obtain ⟨ε, hε, hstab⟩ := atom_stable_zero_poly p hp_zero γ
    exact ⟨ε, hε, fun y hy => (hstab y hy).2.2⟩

theorem qf_formula_stable_nonZero {φ : QFFormula 1} {γ : ℝ}
    (h : γ ∉ QF_zeroLocus_nonZero φ) :
    ∃ ε > 0, ∀ y : ℝ, dist y γ < ε → (φ.eval (fun _ => y) ↔ φ.eval (fun _ => γ)) := by
  induction φ with
  | atomEq p =>
    obtain ⟨ε, hε, hstab⟩ := eval_atomEq_stable (p:=p) (γ:=γ) h
    refine ⟨ε, hε, fun y hy => ?_⟩
    simp only [QFFormula.eval, evalPolyQ_single_eq]
    exact hstab y hy
  | atomLt p =>
    obtain ⟨ε, hε, hstab⟩ := eval_atomLt_stable (p:=p) (γ:=γ) h
    refine ⟨ε, hε, fun y hy => ?_⟩
    simp only [QFFormula.eval, evalPolyQ_single_eq]
    exact hstab y hy
  | atomLe p =>
    obtain ⟨ε, hε, hstab⟩ := eval_atomLe_stable (p:=p) (γ:=γ) h
    refine ⟨ε, hε, fun y hy => ?_⟩
    simp only [QFFormula.eval, evalPolyQ_single_eq]
    exact hstab y hy
  | and φ ψ ihφ ihψ =>
    have hφ : γ ∉ QF_zeroLocus_nonZero φ := by
      intro hφ_mem
      obtain ⟨p, hp_mem, hp_ne, heq⟩ := hφ_mem
      exact h ⟨p, Or.inl hp_mem, hp_ne, heq⟩
    have hψ : γ ∉ QF_zeroLocus_nonZero ψ := by
      intro hψ_mem
      obtain ⟨p, hp_mem, hp_ne, heq⟩ := hψ_mem
      exact h ⟨p, Or.inr hp_mem, hp_ne, heq⟩
    obtain ⟨ε1, hε1, h1⟩ := ihφ hφ
    obtain ⟨ε2, hε2, h2⟩ := ihψ hψ
    refine ⟨min ε1 ε2, lt_min hε1 hε2, fun y hy => ?_⟩
    have hy1 : dist y γ < ε1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y γ < ε2 := lt_of_lt_of_le hy (min_le_right _ _)
    simp only [QFFormula.eval]
    rw [h1 y hy1, h2 y hy2]
  | or φ ψ ihφ ihψ =>
    have hφ : γ ∉ QF_zeroLocus_nonZero φ := by
      intro hφ_mem
      obtain ⟨p, hp_mem, hp_ne, heq⟩ := hφ_mem
      exact h ⟨p, Or.inl hp_mem, hp_ne, heq⟩
    have hψ : γ ∉ QF_zeroLocus_nonZero ψ := by
      intro hψ_mem
      obtain ⟨p, hp_mem, hp_ne, heq⟩ := hψ_mem
      exact h ⟨p, Or.inr hp_mem, hp_ne, heq⟩
    obtain ⟨ε1, hε1, h1⟩ := ihφ hφ
    obtain ⟨ε2, hε2, h2⟩ := ihψ hψ
    refine ⟨min ε1 ε2, lt_min hε1 hε2, fun y hy => ?_⟩
    have hy1 : dist y γ < ε1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y γ < ε2 := lt_of_lt_of_le hy (min_le_right _ _)
    simp only [QFFormula.eval]
    rw [h1 y hy1, h2 y hy2]
  | not φ ih =>
    obtain ⟨ε, hε, hstab⟩ := ih h
    refine ⟨ε, hε, fun y hy => ?_⟩
    simp only [QFFormula.eval]
    rw [hstab y hy]
  | tru =>
    refine ⟨1, by norm_num, fun y _ => Iff.rfl⟩
  | fls =>
    refine ⟨1, by norm_num, fun y _ => Iff.rfl⟩

theorem frontier_solutionSet_subset_zeroLocus_nonZero (φ : QFFormula 1) :
    frontier (φ.solutionSet1) ⊆ QF_zeroLocus_nonZero φ := by
  intro γ hmem
  by_contra h_not
  obtain ⟨ε, hε_pos, hstable⟩ := qf_formula_stable_nonZero h_not
  have h_ball_subset : Metric.ball γ ε ⊆ φ.solutionSet1 ∨ Metric.ball γ ε ⊆ (φ.solutionSet1)ᶜ := by
    by_cases hγ : φ.eval (fun _ => γ)
    · left
      intro y hy
      have hy' : dist y γ < ε := Metric.mem_ball.mp hy
      have h_iff := hstable y hy'
      have h_y : φ.eval (fun _ => y) := h_iff.mpr hγ
      exact h_y
    · right
      intro y hy
      have hy' : dist y γ < ε := Metric.mem_ball.mp hy
      have h_iff := hstable y hy'
      have h_y_not : ¬ φ.eval (fun _ => y) := by
        intro h_y
        have := h_iff.mp h_y
        exact hγ this
      exact h_y_not
  have h_not_frontier : γ ∉ frontier (φ.solutionSet1) := by
    cases h_ball_subset with
    | inl hsub =>
      have h_interior : γ ∈ interior (φ.solutionSet1) := mem_interior.mpr ⟨Metric.ball γ ε, hsub, Metric.isOpen_ball, Metric.mem_ball_self hε_pos⟩
      have h_front : frontier (φ.solutionSet1) = closure (φ.solutionSet1) \ interior (φ.solutionSet1) := rfl
      intro hfront
      rw [h_front] at hfront
      exact hfront.2 h_interior
    | inr hsub =>
      have h_compl_interior : γ ∈ interior (φ.solutionSet1)ᶜ := mem_interior.mpr ⟨Metric.ball γ ε, hsub, Metric.isOpen_ball, Metric.mem_ball_self hε_pos⟩
      have h_not_closure : γ ∉ closure (φ.solutionSet1) := by
        rw [closure_eq_compl_interior_compl]
        simp only [Set.mem_compl_iff, h_compl_interior, not_not, not_false_eq_true]
      have h_front : frontier (φ.solutionSet1) = closure (φ.solutionSet1) \ interior (φ.solutionSet1) := rfl
      intro hfront
      rw [h_front] at hfront
      exact h_not_closure hfront.1
  exact h_not_frontier hmem

theorem frontier_solutionSet_subset_zeroLocus (φ : QFFormula 1) :
    frontier (φ.solutionSet1) ⊆ QF_zeroLocus φ := by
  intro γ hmem
  have h_nonZero := frontier_solutionSet_subset_zeroLocus_nonZero φ hmem
  simp only [QF_zeroLocus_nonZero, QF_zeroLocus, Set.mem_setOf_eq] at h_nonZero ⊢
  obtain ⟨p, hp_mem, hp_ne, hzero⟩ := h_nonZero
  exact ⟨p, hp_mem, hzero⟩

def IsRealAlgebraicEndpoint (φ : QFFormula 1) (x : ℝ) : Prop :=
  IsAlgebraic (R := ℚ) x ∧ x ∈ frontier (φ.solutionSet1)

theorem qf_endpoint_algebraic (φ : QFFormula 1)
    (γ : ℝ) (hmem : γ ∈ frontier (φ.solutionSet1)) : IsAlgebraic (R := ℚ) γ := by
  have h_in_zeroLocus := frontier_solutionSet_subset_zeroLocus_nonZero φ hmem
  simp only [QF_zeroLocus_nonZero, Set.mem_setOf_eq] at h_in_zeroLocus
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ := h_in_zeroLocus
  exact zero_mem_algebraic p γ hp_ne hp_zero

lemma frontier_empty_of_all_zero {φ : QFFormula 1} (h : ∀ p ∈ φ.polySet, p = 0) :
    frontier (φ.solutionSet1) = ∅ := by
  have h_subset : QF_zeroLocus_nonZero φ = ∅ := by
    ext γ
    simp only [QF_zeroLocus_nonZero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro p hp_mem hp_ne hzero
    have hp_zero := h p hp_mem
    exact hp_ne hp_zero
  have h_front_subset := frontier_solutionSet_subset_zeroLocus_nonZero φ
  have : frontier (φ.solutionSet1) ⊆ ∅ := by
    intro γ hmem
    have := h_front_subset hmem
    rw [h_subset] at this
    exact this
  exact Set.subset_eq_empty this rfl

lemma frontier_tru_empty : frontier ((QFFormula.tru : QFFormula 1).solutionSet1) = ∅ := by
  have h : (QFFormula.tru : QFFormula 1).solutionSet1 = Set.univ := by
    ext r
    simp [QFFormula.solutionSet1, QFFormula.eval]
  rw [h]
  simp

end QFFrontier

section LinearRoot

def linearPoly (a b : ℚ) : Polynomial ℚ :=
  Polynomial.C a * Polynomial.X + Polynomial.C b

lemma linearPoly_ne_zero {a b : ℚ} (ha : a ≠ 0) : linearPoly a b ≠ 0 := by
  intro h
  have h_coeff : (linearPoly a b).coeff 1 = a := by
    simp [linearPoly]
  rw [h] at h_coeff
  simp at h_coeff
  exact ha h_coeff.symm

lemma linearPoly_aeval {a b : ℚ} (γ : ℝ)
    (hroot : (a : ℝ) * γ + (b : ℝ) = 0) : Polynomial.aeval γ (linearPoly a b) = 0 := by
  simp only [linearPoly, Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  exact hroot

theorem linear_root_algebraic (a b : ℚ) (ha : a ≠ 0) (γ : ℝ)
    (hroot : (a : ℝ) * γ + (b : ℝ) = 0) : IsAlgebraic (R := ℚ) γ := by
  exact ⟨linearPoly a b, linearPoly_ne_zero ha, linearPoly_aeval γ hroot⟩

theorem explicit_linear_root_algebraic (a b : ℚ) (ha : a ≠ 0) :
    IsAlgebraic (R := ℚ) ((-(b : ℝ) / (a : ℝ))) := by
  have hroot : (a : ℝ) * (-(b : ℝ) / (a : ℝ)) + (b : ℝ) = 0 := by
    have ha_real : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    field_simp
    ring
  exact linear_root_algebraic a b ha _ hroot

end LinearRoot




end
end MemorySemialgebraic
