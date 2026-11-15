module
public import Continuation.Semialgebraic.SymbolicAffineQE
public import Continuation.RootIsolation.SignSamples
public meta import Continuation.Semialgebraic.SymbolicAffineQE
public meta import Continuation.RootIsolation.SignSamples

/-!
# Executable arbitrary-degree univariate real decision

This is a complete decision procedure for an existential or universal real quantifier over an
arbitrary Boolean combination of rational univariate polynomial comparisons. It uses the certified
isolator, exact algebraic-root signs, and representatives of every root-free sign region.
It does not perform symbolic elimination of nonlinear polynomials with free parameters.
-/

@[expose] public section
open Polynomial RootIsolation.SimpleRoots RootIsolation.Executable
namespace MemorySemialgebraic.SymbolicQE

namespace Expr

/-- Compile one-variable polynomial syntax to the executable rational arithmetic representation. -/
def compileUnivariate : Expr 1 → Poly
  | .constant q => [q]
  | .variable _ => [1, 0]
  | .add p q => RootIsolation.Executable.add (compileUnivariate p) (compileUnivariate q)
  | .neg p => scale (-1) (compileUnivariate p)
  | .mul p q => RootIsolation.Executable.mul (compileUnivariate p) (compileUnivariate q)

@[simp] theorem compileUnivariate_correct (p : Expr 1) (x : ℝ) :
    (RootIsolation.Executable.denote (compileUnivariate p)).aeval x =
      evalReal (fun _ => x) p := by
  induction p <;>
    simp_all [-evalReal_refines, compileUnivariate, evalReal, denote_cons]

end Expr

lemma realSign_eq_neg_one_iff (x : ℝ) : realSign x = -1 ↔ x < 0 := by
  by_cases hn : x < 0
  · simp [realSign, hn]
  · by_cases hz : x = 0 <;> simp [realSign, hn, hz]

lemma realSign_eq_zero_iff (x : ℝ) : realSign x = 0 ↔ x = 0 := by
  by_cases hn : x < 0
  · simp [realSign, hn, ne_of_lt hn]
  · by_cases hz : x = 0 <;> simp [realSign, hn, hz]

lemma realSign_eq_one_iff (x : ℝ) : realSign x = 1 ↔ 0 < x := by
  by_cases hn : x < 0
  · simp [realSign, hn, not_lt_of_ge hn.le]
  · by_cases hz : x = 0
    · simp [realSign, hz]
    · have hx : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [realSign, hn, hz, hx]

namespace Formula

/-- The finite family whose common root arrangement determines the formula. -/
def atomPolys : Formula 1 → List Poly
  | .eqZero p => [p.compileUnivariate]
  | .positive p => [p.compileUnivariate]
  | .nonnegative p => [p.compileUnivariate]
  | .conj f g => atomPolys f ++ atomPolys g
  | .disj f g => atomPolys f ++ atomPolys g
  | .neg f => atomPolys f
  | .tru => []
  | .fls => []

/-- Evaluate a Boolean formula from an exact sign assignment to its atomic polynomials. -/
def evalSigns (sg : Poly → ℤ) : Formula 1 → Bool
  | .eqZero p => decide (sg p.compileUnivariate = 0)
  | .positive p => decide (sg p.compileUnivariate = 1)
  | .nonnegative p => decide (sg p.compileUnivariate ≠ -1)
  | .conj f g => evalSigns sg f && evalSigns sg g
  | .disj f g => evalSigns sg f || evalSigns sg g
  | .neg f => !evalSigns sg f
  | .tru => true
  | .fls => false

/-- A finite sign table suffices to interpret all Boolean structure exactly. -/
theorem evalSigns_correct (sg : Poly → ℤ) (f : Formula 1) (x : ℝ)
    (hsg : ∀ p ∈ atomPolys f, sg p = realSign ((denote p).aeval x)) :
    evalSigns sg f = true ↔ evalReal (fun _ => x) f := by
  induction f generalizing sg with
  | eqZero p =>
    simp only [evalSigns, decide_eq_true_eq]
    rw [hsg _ (by simp [atomPolys]), realSign_eq_zero_iff, Expr.compileUnivariate_correct]
    rfl
  | positive p =>
    simp only [evalSigns, decide_eq_true_eq]
    rw [hsg _ (by simp [atomPolys]), realSign_eq_one_iff, Expr.compileUnivariate_correct]
    rfl
  | nonnegative p =>
    simp only [evalSigns, decide_eq_true_eq]
    rw [hsg _ (by simp [atomPolys]), ne_eq, realSign_eq_neg_one_iff, not_lt,
      Expr.compileUnivariate_correct]
    rfl
  | conj f g ihf ihg =>
    simp only [evalSigns, Bool.and_eq_true, evalReal]
    exact and_congr (ihf sg (fun p hp => hsg p (List.mem_append_left _ hp)))
      (ihg sg (fun p hp => hsg p (List.mem_append_right _ hp)))
  | disj f g ihf ihg =>
    simp only [evalSigns, Bool.or_eq_true, evalReal]
    exact or_congr (ihf sg (fun p hp => hsg p (List.mem_append_left _ hp)))
      (ihg sg (fun p hp => hsg p (List.mem_append_right _ hp)))
  | neg f ih =>
    simp only [evalSigns, Bool.not_eq_true', Bool.eq_false_iff, evalReal]
    exact not_congr (ih sg hsg)
  | tru => simp [evalSigns, evalReal]
  | fls => simp [evalSigns, evalReal]

/-- Decide an existential real quantifier by finite exact sign determination. -/
def decideExists (f : Formula 1) : Bool :=
  let p := familyProduct (atomPolys f)
  (signSamples p).any (fun r => evalSigns (fun q => rationalSign (eval q r)) f) ||
    (intervals p).any (fun I => evalSigns (fun q => rootSign p q I) f)

/-- Correctness for arbitrary Boolean combinations and arbitrary polynomial degrees. -/
theorem decideExists_correct (f : Formula 1) :
    decideExists f = true ↔ ∃ x : ℝ, evalReal (fun _ => x) f := by
  let p := familyProduct (atomPolys f)
  have hp : denote p ≠ 0 := familyProduct_ne_zero _
  have hcover (q : Poly) (hq : q ∈ atomPolys f) : denote q = 0 ∨ denote q ∣ denote p :=
    familyProduct_covers _ _ hq
  change ((signSamples p).any (fun r => evalSigns (fun q => rationalSign (eval q r)) f) ||
    (intervals p).any (fun I => evalSigns (fun q => rootSign p q I) f)) = true ↔ _
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro (⟨r, hr, hf⟩ | ⟨I, hI, hf⟩)
    · refine ⟨(r : ℝ), (evalSigns_correct _ f _ ?_).mp hf⟩
      intro q hq
      simp only [aeval_coe_eq_coe_eval, realSign_cast, eval_refines]
    · obtain ⟨x, hx, huniq⟩ := existsUnique_root_of_mem_intervals p hp I hI
      refine ⟨x, (evalSigns_correct _ f x ?_).mp hf⟩
      intro q hq
      exact rootSign_correct p q hp (hcover q hq) I hI x hx.1 hx.2
  · rintro ⟨x, hfx⟩
    by_cases hpx : (denote p).aeval x = 0
    · obtain ⟨I, hI, hxI⟩ := every_root_mem_intervals p hp x hpx
      right
      refine ⟨I, hI, (evalSigns_correct _ f x ?_).mpr hfx⟩
      intro q hq
      exact rootSign_correct p q hp (hcover q hq) I hI x hpx hxI
    · obtain ⟨r, hr, hrs⟩ := exists_sample_same_signs p hp x hpx
      left
      refine ⟨r, hr, (evalSigns_correct _ f x ?_).mpr hfx⟩
      intro q hq
      exact (hrs q (hcover q hq)).symm

/-- The executable decision also applies directly to the established QF semantics. -/
theorem decideExists_toQF (f : Formula 1) :
    decideExists f = true ↔ ∃ x : ℝ, (toQF f).eval (fun _ => x) := by
  simpa only [toQF_refines] using decideExists_correct f

/-- Universal decision is dual to existential decision of the negated formula. -/
def decideForall (f : Formula 1) : Bool := !decideExists (.neg f)

theorem decideForall_correct (f : Formula 1) :
    decideForall f = true ↔ ∀ x : ℝ, evalReal (fun _ => x) f := by
  classical
  simp only [decideForall, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, decideExists_correct,
    evalReal, not_exists, not_not]

end Formula
end MemorySemialgebraic.SymbolicQE

open MemorySemialgebraic.SymbolicQE

/-- info: true -/
#guard_msgs in
#eval
  let x : Expr 1 := .variable 0
  Formula.decideExists (.conj (.eqZero (.sub (.mul x x) (.constant 2))) (.positive x))
/-- info: false -/
#guard_msgs in
#eval
  let x : Expr 1 := .variable 0
  Formula.decideExists (.eqZero (.add (.mul x x) (.constant 1)))
/-- info: true -/
#guard_msgs in
#eval
  let x : Expr 1 := .variable 0
  Formula.decideForall (.nonnegative (.mul x x))
/-- info: false -/
#guard_msgs in
#eval Formula.decideExists (.positive (.constant 0))
/-- info: true -/
#guard_msgs in
#eval Formula.decideExists (.eqZero (.constant 0))
