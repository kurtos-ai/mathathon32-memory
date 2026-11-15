module
public import Continuation.RootIsolation.ExecutableIsolation
public meta import Continuation.RootIsolation.ExecutableIsolation

/-!
# Executable zero testing at an isolated real algebraic root

An isolating cell of a nonzero rational polynomial represents its unique real root. This module
computes whether a second rational polynomial vanishes at that root. Open cells are tested by
squarefree gcd and exact rational endpoint signs; point cells use rational evaluation directly.
This is the first component of sign determination for arbitrary Boolean univariate formulas.
-/

@[expose] public section
open Polynomial RootIsolation.SimpleRoots
namespace RootIsolation.Executable

lemma squarefreePart_aeval_iff (p : Poly) (hp : denote p ≠ 0) (x : ℝ) :
    (denote (squarefreePart p)).aeval x = 0 ↔ (denote p).aeval x = 0 := by
  rw [squarefreePart_refines, RootIsolation.Effective.squarefree_parts_eq]
  exact (SquarefreePreprocessing.squarefree_aeval_root_iff (denote p) hp x).symm

lemma squarefreePart_derivative_ne_zero (p : Poly) (hp : denote p ≠ 0) (x : ℝ)
    (hx : (denote (squarefreePart p)).aeval x = 0) :
    (denote (squarefreePart p)).derivative.aeval x ≠ 0 := by
  rw [squarefreePart_refines, RootIsolation.Effective.squarefree_parts_eq] at hx ⊢
  exact SquarefreePreprocessing.squarefree_deriv_ne_zero (denote p) hp x hx

lemma gcd_denote_ne_zero (f p : Poly) (hf : denote f ≠ 0) : denote (gcd f p) ≠ 0 := by
  rw [gcd_refines]
  intro h
  exact hf ((EuclideanDomain.gcd_eq_zero_iff (R := ℚ[X])).mp h).1

lemma squarefree_gcd_aeval_iff (f p : Poly) (hf : denote f ≠ 0) (x : ℝ) :
    (denote (squarefreePart (gcd f p))).aeval x = 0 ↔
      (denote f).aeval x = 0 ∧ (denote p).aeval x = 0 := by
  rw [squarefreePart_aeval_iff _ (gcd_denote_ne_zero f p hf), gcd_refines]
  exact Polynomial.root_gcd_iff_root_left_right

lemma roots_eq_of_mem_interval (f : Poly) (hf : denote f ≠ 0) (I : IsoInterval)
    (hI : I ∈ intervals f) (x y : ℝ)
    (hx : (denote f).aeval x = 0) (hy : (denote f).aeval y = 0)
    (hxI : x ∈ I.toSet) (hyI : y ∈ I.toSet) : x = y := by
  obtain ⟨z, hz, huniq⟩ := existsUnique_root_of_mem_intervals f hf I hI
  exact (huniq x ⟨hx, hxI⟩).trans (huniq y ⟨hy, hyI⟩).symm

lemma open_mem_intervals_sign (f : Poly) (a b : ℚ)
    (hI : IsoInterval.openInterval a b ∈ intervals f) :
    eval (squarefreePart f) a * eval (squarefreePart f) b < 0 := by
  rw [intervals, filteredIntervals, List.mem_append, List.mem_map, List.mem_map] at hI
  rcases hI with ⟨r, hr, heq⟩ | ⟨⟨c, d⟩, hcd, heq⟩
  · cases heq
  · cases heq
    exact of_decide_eq_true (List.mem_filter.mp hcd).2

lemma open_mem_intervals_endpoints_nonzero (f : Poly) (hf : denote f ≠ 0) (a b : ℚ)
    (hI : IsoInterval.openInterval a b ∈ intervals f) :
    (denote f).aeval (a : ℝ) ≠ 0 ∧ (denote f).aeval (b : ℝ) ≠ 0 := by
  have hs := open_mem_intervals_sign f a b hI
  have hne := mul_ne_zero_iff.mp (ne_of_lt hs)
  have haneq : (denote (squarefreePart f)).aeval (a : ℝ) ≠ 0 := by
    rw [aeval_coe_eq_coe_eval]
    rw [eval_refines] at hne
    exact_mod_cast hne.1
  have hbneq : (denote (squarefreePart f)).aeval (b : ℝ) ≠ 0 := by
    rw [aeval_coe_eq_coe_eval]
    rw [eval_refines, eval_refines] at hne
    exact_mod_cast hne.2
  exact ⟨fun h => haneq ((squarefreePart_aeval_iff f hf _).mpr h),
    fun h => hbneq ((squarefreePart_aeval_iff f hf _).mpr h)⟩

lemma exists_root_of_eval_product_neg (q : Poly) (a b : ℚ) (hab : (a : ℝ) < (b : ℝ))
    (hs : eval q a * eval q b < 0) :
    ∃ x ∈ Set.Ioo (a : ℝ) (b : ℝ), (denote q).aeval x = 0 := by
  have hsign : (denote q).aeval (a : ℝ) * (denote q).aeval (b : ℝ) < 0 := by
    rw [aeval_coe_eq_coe_eval, aeval_coe_eq_coe_eval]
    simp only [eval_refines] at hs
    exact_mod_cast hs
  have hcont : ContinuousOn (fun x : ℝ => (denote q).aeval x)
      (Set.Icc (a : ℝ) (b : ℝ)) := (poly_aeval_continuous _).continuousOn
  rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hab.le hcont (show
        (0 : ℝ) ∈ Set.Ioo ((denote q).aeval (b : ℝ)) ((denote q).aeval (a : ℝ)) from ⟨hb, ha⟩)
    exact ⟨x, hx, hx0⟩
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hab.le hcont (show
        (0 : ℝ) ∈ Set.Ioo ((denote q).aeval (a : ℝ)) ((denote q).aeval (b : ℝ)) from ⟨ha, hb⟩)
    exact ⟨x, hx, hx0⟩

/-- An exact, executable equality test at a root represented by an isolating cell of `f`. -/
def rootZero (f p : Poly) : IsoInterval → Bool
  | .point a => decide (eval p a = 0)
  | .openInterval a b =>
    let q := squarefreePart (gcd f p)
    decide (eval q a * eval q b < 0)

/-- The zero test is valid for every second polynomial, including the zero polynomial. -/
theorem rootZero_correct (f p : Poly) (hf : denote f ≠ 0) (I : IsoInterval)
    (hI : I ∈ intervals f) (x : ℝ) (hx : (denote f).aeval x = 0) (hxI : x ∈ I.toSet) :
    rootZero f p I = true ↔ (denote p).aeval x = 0 := by
  cases I with
  | point a =>
    change x = (a : ℝ) at hxI
    subst x
    simp only [rootZero, decide_eq_true_eq, eval_refines, aeval_coe_eq_coe_eval]
    exact_mod_cast (Iff.rfl : (denote p).eval a = 0 ↔ (denote p).eval a = 0)
  | openInterval a b =>
    change (a : ℝ) < x ∧ x < (b : ℝ) at hxI
    simp only [rootZero, decide_eq_true_eq]
    let q := squarefreePart (gcd f p)
    have hqiff := squarefree_gcd_aeval_iff f p hf
    have hends := open_mem_intervals_endpoints_nonzero f hf a b hI
    constructor
    · intro hs
      obtain ⟨y, hyI, hyq⟩ := exists_root_of_eval_product_neg q a b
        (lt_trans hxI.1 hxI.2) hs
      have hy := (hqiff y).mp hyq
      have hyx := roots_eq_of_mem_interval f hf (.openInterval a b) hI y x hy.1 hx hyI hxI
      exact hyx ▸ hy.2
    · intro hpx
      have hqx : (denote q).aeval x = 0 := (hqiff x).mpr ⟨hx, hpx⟩
      have hd := squarefreePart_derivative_ne_zero (gcd f p)
        (gcd_denote_ne_zero f p hf) x hqx
      have hqa : (denote q).aeval (a : ℝ) ≠ 0 := fun h => hends.1 ((hqiff _).mp h).1
      have hqb : (denote q).aeval (b : ℝ) ≠ 0 := fun h => hends.2 ((hqiff _).mp h).1
      have huniq : ∀ y, (denote q).aeval y = 0 →
          y ∈ Set.Icc (a : ℝ) (b : ℝ) → y = x := by
        intro y hy hyI
        have hyf := ((hqiff y).mp hy).1
        have hya : y ≠ (a : ℝ) := by
          intro heq
          exact hends.1 (heq ▸ hyf)
        have hyb : y ≠ (b : ℝ) := by
          intro heq
          exact hends.2 (heq ▸ hyf)
        have hyopen : y ∈ Set.Ioo (a : ℝ) (b : ℝ) :=
          ⟨lt_of_le_of_ne hyI.1 (Ne.symm hya), lt_of_le_of_ne hyI.2 hyb⟩
        exact roots_eq_of_mem_interval f hf (.openInterval a b) hI y x hyf hx hyopen hxI
      have hs := endpoint_sign_of_unique_simple_root (denote q) x (a : ℝ) (b : ℝ)
        hqx hd hxI.1 hxI.2 huniq hqa hqb
      rw [aeval_coe_eq_coe_eval, aeval_coe_eq_coe_eval] at hs
      simp only [eval_refines]
      exact_mod_cast hs

end RootIsolation.Executable

/-- info: some [true, true] -/
#guard_msgs in
#eval (RootIsolation.Executable.isolate [1, 0, -2]).map
  (fun cells => cells.map (RootIsolation.Executable.rootZero [1, 0, -2] [1, 0, -2]))
/-- info: some [false, false] -/
#guard_msgs in
#eval (RootIsolation.Executable.isolate [1, 0, -2]).map
  (fun cells => cells.map (RootIsolation.Executable.rootZero [1, 0, -2] [1, -1]))
/-- info: some [true] -/
#guard_msgs in
#eval (RootIsolation.Executable.isolate [1, -2, 1]).map
  (fun cells => cells.map (RootIsolation.Executable.rootZero [1, -2, 1] [2, -2]))
