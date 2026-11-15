module
public import Submission2026.QuadraticReplacement.PolynomialDomination
@[expose] public section
noncomputable section
namespace QuadraticReplacement
open Polynomial

def normalizeConstant (p : ℝ[X]) : ℝ[X] := C (p.eval 0)⁻¹*p

lemma normalizeConstant_eval_zero (p : ℝ[X]) (hp : p.eval 0 ≠ 0) :
    (normalizeConstant p).eval 0=1 := by simp [normalizeConstant,hp]

lemma normalizeConstant_natDegree (p : ℝ[X]) (hp : p.eval 0 ≠ 0) :
    (normalizeConstant p).natDegree=p.natDegree := by
  exact natDegree_C_mul (inv_ne_zero hp)

lemma normalizeConstant_mul (p q : ℝ[X]) :
    normalizeConstant (p*q)=normalizeConstant p*normalizeConstant q := by
  simp only [normalizeConstant,eval_mul,mul_inv_rev,map_mul]
  ring

/-- Real polynomials with nonzero constant term factor into normalized pieces of degree one or two,
without losing the total degree budget. -/
theorem exists_normalized_low_degree_factors (p : ℝ[X]) (hp : p.eval 0 ≠ 0) :
    ∃ fs : List ℝ[X],fs.prod=normalizeConstant p ∧
      (∀ f ∈ fs,f.eval 0=1 ∧ 1  ≤  f.natDegree ∧ f.natDegree  ≤  2) ∧
      (fs.map Polynomial.natDegree).sum=p.natDegree := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at hp
  | unit p hu =>
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    have he : p=C (p.eval 0) := by simpa only [coeff_zero_eq_eval_zero] using Polynomial.eq_C_of_natDegree_eq_zero hd
    refine ⟨[],?_,by simp,by simpa using hd.symm⟩
    rw [normalizeConstant,he]
    simp only [eval_C,← C_mul,inv_mul_cancel₀ hp,C_1,List.prod_nil]
  | mul p f hp0 hf ih =>
    have hfp : f.eval 0 ≠ 0 ∧ p.eval 0 ≠ 0 := by
      simpa only [eval_mul,mul_ne_zero_iff] using hp
    obtain ⟨fs,hprod,hall,hdeg⟩ := ih hfp.2
    refine ⟨normalizeConstant f::fs,?_,?_,?_⟩
    · simp only [List.prod_cons,hprod,normalizeConstant_mul]
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · refine ⟨normalizeConstant_eval_zero f hfp.1,?_,?_⟩
        · rw [normalizeConstant_natDegree f hfp.1]
          exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hf)
        · rw [normalizeConstant_natDegree f hfp.1]
          exact hf.natDegree_le_two
      · exact hall g hg
    · simp only [List.map_cons,List.sum_cons,normalizeConstant_natDegree f hfp.1,hdeg,
        Polynomial.natDegree_mul hf.ne_zero hp0]

/-- The factorization statement specialized to residual polynomials normalized at zero. -/
theorem exists_normalized_factors (p : ℝ[X]) (hp : p.eval 0=1) :
    ∃ fs : List ℝ[X],fs.prod=p ∧
      (∀ f ∈ fs,f.eval 0=1 ∧ 1  ≤  f.natDegree ∧ f.natDegree  ≤  2) ∧
      (fs.map Polynomial.natDegree).sum=p.natDegree := by
  obtain ⟨fs,hprod,hall,hdeg⟩ := exists_normalized_low_degree_factors p (by rw [hp]; norm_num)
  exact ⟨fs,by simpa [normalizeConstant,hp] using hprod,hall,hdeg⟩

lemma low_degree_form (p : ℝ[X]) (hp : p.eval 0=1) (hd : p.natDegree  ≤  2) :
    p=1+C (p.coeff 1)*X+C (p.coeff 2)*X^2 := by
  apply Polynomial.funext
  intro x
  have he := Polynomial.eval_eq_sum_range' (show p.natDegree < 3 by omega) x
  simpa [Finset.sum_range_succ,coeff_zero_eq_eval_zero,hp] using he

lemma linear_form (p : ℝ[X]) (hp : p.eval 0=1) (hd : p.natDegree  ≤  1) :
    p=1+C (p.coeff 1)*X := by
  calc
    p=1+C (p.coeff 1)*X+C (p.coeff 2)*X^2 := low_degree_form p hp (by omega)
    _=1+C (p.coeff 1)*X := by
      rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < 2 by omega)]
      simp

end QuadraticReplacement
