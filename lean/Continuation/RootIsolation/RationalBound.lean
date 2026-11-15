module
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section
open Polynomial Finset
namespace RootIsolation

def rationalRootBound (p : ℚ[X]) : ℚ :=
  (∑ i ∈ Finset.range p.natDegree, |p.coeff i|) / |p.leadingCoeff| + 1

lemma rationalRootBound_one_le (p : ℚ[X]) : 1 ≤ rationalRootBound p := by
  unfold rationalRootBound
  have : 0 ≤ (∑ i ∈ Finset.range p.natDegree, |p.coeff i|) / |p.leadingCoeff| := by
    positivity
  linarith

lemma cauchyBound_le_rationalRootBound (p : ℚ[X]) :
    ((p.map (algebraMap ℚ ℝ)).cauchyBound : ℝ) ≤ (rationalRootBound p : ℝ) := by
  let q := p.map (algebraMap ℚ ℝ)
  have hdeg : q.natDegree = p.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective p
  have hl : q.leadingCoeff = (p.leadingCoeff : ℝ) := by
    exact Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ ℝ).injective p
  have hc (i : ℕ) : q.coeff i = (p.coeff i : ℝ) := by simp [q]
  have hsum : (0:ℝ) ≤ ((∑ i ∈ Finset.range p.natDegree, |p.coeff i| : ℚ) : ℝ) := by positivity
  have hsNN : (Finset.range q.natDegree).sup (fun i => ‖q.coeff i‖₊) ≤
      (⟨((∑ i ∈ Finset.range p.natDegree, |p.coeff i| : ℚ) : ℝ), hsum⟩ : NNReal) := by
    apply Finset.sup_le
    intro i hi
    change ‖q.coeff i‖ ≤ _
    rw [hc, Real.norm_eq_abs]
    rw [hdeg] at hi
    have hi' := Finset.single_le_sum (fun j (_ : j ∈ Finset.range p.natDegree) => abs_nonneg (p.coeff j)) hi
    change |(p.coeff i : ℝ)| ≤ ((∑ i ∈ Finset.range p.natDegree, |p.coeff i| : ℚ) : ℝ)
    exact_mod_cast hi'
  have hs : (((Finset.range q.natDegree).sup (fun i => ‖q.coeff i‖₊) : NNReal) : ℝ) ≤
      ((∑ i ∈ Finset.range p.natDegree, |p.coeff i| : ℚ) : ℝ) := hsNN
  unfold Polynomial.cauchyBound
  push_cast
  rw [hl]
  unfold rationalRootBound
  push_cast
  rw [Real.norm_eq_abs]
  gcongr
  simpa [q] using hs

lemma root_norm_lt_rationalRootBound (p : ℚ[X]) (hp : p ≠ 0) (x : ℝ)
    (hx : p.aeval x = 0) : ‖x‖ < (rationalRootBound p : ℝ) := by
  have hp' : p.map (algebraMap ℚ ℝ) ≠ 0 := Polynomial.map_ne_zero hp
  have hx' : (p.map (algebraMap ℚ ℝ)).IsRoot x := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hx
  have h := hx'.norm_lt_cauchyBound hp'
  exact lt_of_lt_of_le (show ‖x‖ < ((p.map (algebraMap ℚ ℝ)).cauchyBound : ℝ) from h)
    (cauchyBound_le_rationalRootBound p)
end RootIsolation
