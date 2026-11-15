module
public import Continuation.Semialgebraic.UnivariateDecision
public import Continuation.Semialgebraic.ThresholdEndpoints
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Interval.Set.Disjoint

@[expose] public section
open Polynomial RootIsolation.SimpleRoots RootIsolation.Executable
namespace MemorySemialgebraic.EndpointSelection
open SymbolicQE

/-- A rational ordering key for disjoint isolating cells. -/
def center : IsoInterval → ℚ
  | .point a => a
  | .openInterval a b => (a+b)/2

/-- Rational cell centers have the same order as their isolated real roots. -/
theorem center_lt_of_disjoint (I J : IsoInterval) (x y : ℝ)
    (hx : x ∈ I.toSet) (hy : y ∈ J.toSet) (hd : Disjoint I.toSet J.toSet) (hxy : x < y) :
    center I < center J := by
  cases I with
  | point a =>
    change x = (a:ℝ) at hx
    subst x
    cases J with
    | point c =>
      change y = (c:ℝ) at hy
      subst y
      exact_mod_cast hxy
    | openInterval c d =>
      change (c:ℝ)<y ∧ y<(d:ℝ) at hy
      have hnot : (a:ℝ) ∉ Set.Ioo (c:ℝ) d := Set.disjoint_left.mp hd (by rfl)
      have hac : (a:ℝ) ≤ c := by
        by_contra! hca
        exact hnot ⟨hca,hxy.trans hy.2⟩
      change a < (c+d)/2
      have hreal : (a:ℝ) < ((c:ℝ)+d)/2 := by linarith
      exact_mod_cast hreal
  | openInterval a b =>
    change (a:ℝ)<x ∧ x<(b:ℝ) at hx
    cases J with
    | point c =>
      change y = (c:ℝ) at hy
      subst y
      have hnot : (c:ℝ) ∉ Set.Ioo (a:ℝ) b := Set.disjoint_right.mp hd (by rfl)
      have hbc : (b:ℝ) ≤ c := by
        by_contra! hcb
        exact hnot ⟨hx.1.trans hxy,hcb⟩
      change (a+b)/2 < c
      have hreal : ((a:ℝ)+b)/2 < (c:ℝ) := by linarith
      exact_mod_cast hreal
    | openInterval c d =>
      change (c:ℝ)<y ∧ y<(d:ℝ) at hy
      have hdis := Set.Ioo_disjoint_Ioo.mp hd
      have hbc : (b:ℝ) ≤ c := by
        by_contra! hcb
        have hmax : max (a:ℝ) c < min (b:ℝ) d :=
          max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨hx.1.trans hx.2,hx.1.trans (hxy.trans hy.2)⟩,
            lt_min_iff.mpr ⟨hcb,hy.1.trans hy.2⟩⟩
        exact (not_lt_of_ge hdis) hmax
      change (a+b)/2 < (c+d)/2
      have hreal : ((a:ℝ)+b)/2 < ((c:ℝ)+d)/2 := by linarith
      exact_mod_cast hreal

lemma compileUnivariate_toPoly (p : Expr 1) :
    RootIsolation.Executable.denote p.compileUnivariate = toPoly p.denote := by
  induction p with
  | constant q => simp [Expr.compileUnivariate,Expr.denote,toPoly]
  | «variable» i => fin_cases i; simp [Expr.compileUnivariate,Expr.denote,toPoly]
  | add p q hp hq => simp [Expr.compileUnivariate,Expr.denote,toPoly] at *; rw [hp,hq]
  | neg p hp => simp [Expr.compileUnivariate,Expr.denote,toPoly] at *; rw [hp]
  | mul p q hp hq => simp [Expr.compileUnivariate,Expr.denote,toPoly] at *; rw [hp,hq]

lemma qf_root_covered (f : Formula 1) (x : ℝ) (q : MvPolynomial (Fin 1) ℚ)
    (hq : q ∈ f.toQF.polySet) (hq0 : q ≠ 0) (hqx : evalSingle q x = 0) :
    ∃ p ∈ f.atomPolys, RootIsolation.Executable.denote p ≠ 0 ∧
      (RootIsolation.Executable.denote p).aeval x = 0 := by
  induction f with
  | eqZero p =>
    simp only [Formula.toQF,QFFormula.polySet,Set.mem_singleton_iff] at hq
    subst q
    exact ⟨p.compileUnivariate,by simp [Formula.atomPolys],
      by simpa [compileUnivariate_toPoly] using toPoly_ne_zero_of_ne_zero hq0,
      by simpa [compileUnivariate_toPoly,evalSingle] using hqx⟩
  | positive p =>
    simp only [Formula.toQF,QFFormula.polySet,Set.mem_singleton_iff] at hq
    subst q
    refine ⟨p.compileUnivariate,by simp [Formula.atomPolys],?_,?_⟩
    · rw [compileUnivariate_toPoly]
      exact toPoly_ne_zero_of_ne_zero (by simpa using hq0)
    · simpa [compileUnivariate_toPoly,evalSingle,toPoly] using hqx
  | nonnegative p =>
    simp only [Formula.toQF,QFFormula.polySet,Set.mem_singleton_iff] at hq
    subst q
    refine ⟨p.compileUnivariate,by simp [Formula.atomPolys],?_,?_⟩
    · rw [compileUnivariate_toPoly]
      exact toPoly_ne_zero_of_ne_zero (by simpa using hq0)
    · simpa [compileUnivariate_toPoly,evalSingle,toPoly] using hqx
  | conj f g ihf ihg =>
    rcases hq with hq | hq
    · obtain ⟨p,hp,hp0,hpx⟩ := ihf hq
      exact ⟨p,List.mem_append_left _ hp,hp0,hpx⟩
    · obtain ⟨p,hp,hp0,hpx⟩ := ihg hq
      exact ⟨p,List.mem_append_right _ hp,hp0,hpx⟩
  | disj f g ihf ihg =>
    rcases hq with hq | hq
    · obtain ⟨p,hp,hp0,hpx⟩ := ihf hq
      exact ⟨p,List.mem_append_left _ hp,hp0,hpx⟩
    · obtain ⟨p,hp,hp0,hpx⟩ := ihg hq
      exact ⟨p,List.mem_append_right _ hp,hp0,hpx⟩
  | neg f ih => exact ih hq
  | tru => exact (Set.notMem_empty q hq).elim
  | fls => exact (Set.notMem_empty q hq).elim

/-- The boundary of a finite strict threshold ray is a root of the executable family product. -/
theorem ray_endpoint_is_root (f : Formula 1) (v : ℝ)
    (hf : ∀ x : ℝ, Formula.evalReal (fun _ => x) f ↔ v < x) :
    (RootIsolation.Executable.denote (familyProduct f.atomPolys)).aeval v = 0 := by
  have hset : f.toQF.solutionSet1 = Set.Ioi v := by
    ext x
    simpa only [QFFormula.solutionSet1,Set.mem_setOf_eq,Formula.toQF_refines,Set.mem_Ioi] using hf x
  have hfront : v ∈ frontier f.toQF.solutionSet1 := by
    rw [hset,frontier_Ioi]
    exact Set.mem_singleton v
  obtain ⟨q,hq,hq0,hqx⟩ := frontier_solutionSet_subset_zeroLocus_nonZero f.toQF hfront
  obtain ⟨p,hp,hp0,hpx⟩ := qf_root_covered f v q hq hq0 hqx
  rcases familyProduct_covers f.atomPolys p hp with hzero | hdiv
  · exact (hp0 hzero).elim
  · obtain ⟨r,hr⟩ := hdiv
    rw [hr,Polynomial.aeval_mul,hpx,zero_mul]

end MemorySemialgebraic.EndpointSelection
