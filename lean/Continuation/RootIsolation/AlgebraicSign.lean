module
public import Continuation.RootIsolation.AlgebraicZeroTest
public meta import Continuation.RootIsolation.AlgebraicZeroTest

/-!
# Exact signs at represented real algebraic roots

For a polynomial family, isolate a nonzero polynomial divisible by every nonzero family member.
This module computes every family member's sign at each isolated algebraic root. The result uses
only rational arithmetic and the certified zero test, and is proved equal to its real sign.
-/

@[expose] public section
open Polynomial RootIsolation.SimpleRoots
namespace RootIsolation.Executable

/-- Exact rational sign encoding: `-1`, `0`, or `1`. -/
def rationalSign (r : ℚ) : ℤ := if r < 0 then -1 else if r = 0 then 0 else 1

/-- Real sign used only in the specification. -/
noncomputable def realSign (r : ℝ) : ℤ := if r < 0 then -1 else if r = 0 then 0 else 1

@[simp] lemma realSign_cast (r : ℚ) : realSign (r : ℝ) = rationalSign r := by
  simp [realSign, rationalSign]

@[simp] lemma realSign_zero : realSign 0 = 0 := by simp [realSign]

lemma realSign_eq_of_no_root (p : ℚ[X]) (a b : ℝ) (hab : a ≤ b)
    (hno : ∀ x ∈ Set.Icc a b, p.aeval x ≠ 0) : realSign (p.aeval a) = realSign (p.aeval b) := by
  have ha0 : p.aeval a ≠ 0 := hno a ⟨le_rfl, hab⟩
  have hb0 : p.aeval b ≠ 0 := hno b ⟨hab, le_rfl⟩
  have hcont : ContinuousOn (fun x : ℝ => p.aeval x) (Set.Icc a b) :=
    (poly_aeval_continuous p).continuousOn
  have hsign : p.aeval a < 0 ↔ p.aeval b < 0 := by
    constructor
    · intro ha
      by_contra hb
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hab hcont
        (show (0 : ℝ) ∈ Set.Icc (p.aeval a) (p.aeval b) from ⟨ha.le, le_of_not_gt hb⟩)
      exact hno x hx hx0
    · intro hb
      by_contra ha
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hab hcont
        (show (0 : ℝ) ∈ Set.Icc (p.aeval b) (p.aeval a) from ⟨hb.le, le_of_not_gt ha⟩)
      exact hno x hx hx0
  simp only [realSign, ha0, hb0, ite_false]
  simp only [hsign]

/-- Exact sign at an isolating cell. Nonzero signs use its rational left endpoint. -/
def rootSign (f p : Poly) (I : IsoInterval) : ℤ :=
  if rootZero f p I then 0 else
    match I with
    | .point a => rationalSign (eval p a)
    | .openInterval a _ => rationalSign (eval p a)

/-- The family condition is satisfied by each factor of a nonzero product. Zero family
members are included explicitly and do not have to divide a nonzero polynomial. -/
theorem rootSign_correct (f p : Poly) (hf : denote f ≠ 0)
    (hpf : denote p = 0 ∨ denote p ∣ denote f) (I : IsoInterval)
    (hI : I ∈ intervals f) (x : ℝ) (hx : (denote f).aeval x = 0) (hxI : x ∈ I.toSet) :
    rootSign f p I = realSign ((denote p).aeval x) := by
  have hz := rootZero_correct f p hf I hI x hx hxI
  by_cases hpx : (denote p).aeval x = 0
  · have hztrue := hz.mpr hpx
    simp [rootSign, hztrue, hpx]
  · have hzfalse : rootZero f p I = false := Bool.eq_false_iff.mpr (mt hz.mp hpx)
    simp only [rootSign, hzfalse, Bool.false_eq_true, ite_false]
    rcases hpf with hp0 | hpf
    · simp [hp0] at hpx
    cases I with
    | point a =>
      change x = (a : ℝ) at hxI
      subst x
      change rationalSign (eval p a) = realSign ((denote p).aeval (a : ℝ))
      rw [aeval_coe_eq_coe_eval, realSign_cast, eval_refines]
    | openInterval a b =>
      change (a : ℝ) < x ∧ x < (b : ℝ) at hxI
      have hends := open_mem_intervals_endpoints_nonzero f hf a b hI
      have hno : ∀ y ∈ Set.Icc (a : ℝ) x, (denote p).aeval y ≠ 0 := by
        intro y hyI hyp
        have hyf : (denote f).aeval y = 0 := by
          obtain ⟨r, hr⟩ := hpf
          rw [hr, Polynomial.aeval_mul, hyp, zero_mul]
        have hay : (a : ℝ) < y := lt_of_le_of_ne hyI.1 (by
          intro heq
          exact hends.1 (heq.symm ▸ hyf))
        have hyb : y < (b : ℝ) := lt_of_le_of_lt hyI.2 hxI.2
        have hyx := roots_eq_of_mem_interval f hf (.openInterval a b) hI y x hyf hx
          ⟨hay, hyb⟩ hxI
        exact hpx (hyx ▸ hyp)
      have hs := realSign_eq_of_no_root (denote p) (a : ℝ) x hxI.1.le hno
      rw [aeval_coe_eq_coe_eval, realSign_cast, ← eval_refines] at hs
      exact hs

end RootIsolation.Executable

/-- info: some [0, -1, 1] -/
#guard_msgs in
#eval (RootIsolation.Executable.isolate [1, 0, -2, 0]).map
  (fun cells => cells.map (RootIsolation.Executable.rootSign [1, 0, -2, 0] [1, 0]))
/-- info: some [0, 0] -/
#guard_msgs in
#eval (RootIsolation.Executable.isolate [1, 0, -2]).map
  (fun cells => cells.map (RootIsolation.Executable.rootSign [1, 0, -2] [0]))
/-- info: some [-1, -1] -/
#guard_msgs in
#eval (RootIsolation.Executable.isolate [1, 0, -2]).map
  (fun cells => cells.map (RootIsolation.Executable.rootSign [1, 0, -2] [-1]))
