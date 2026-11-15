module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Continuation.Quadratic.Foundations
@[expose] public section
noncomputable section
namespace QuadraticReplacement
open Polynomial

/-- Normalized complex root factors reproduce a polynomial whose constant term is one. -/
lemma complex_normalized_roots (p : ℂ[X]) (hp : p.eval 0 = 1) (x : ℂ) :
    (p.roots.map (fun r => 1 - x/r)).prod = p.eval x := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hs : p.Splits := IsAlgClosed.splits p
  have hl : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hz : p.leadingCoeff * (p.roots.map (fun r => -r)).prod = 1 := by
    simpa using (hs.eval_eq_prod_roots 0).symm.trans hp
  have hr (r : ℂ) (hr : r ∈ p.roots) : r ≠ 0 := by
    intro h
    subst r
    have hh := (mem_roots hp0).mp hr
    change p.eval 0=0 at hh
    rw [hp] at hh
    exact one_ne_zero hh
  have he : p.roots.map (fun r => 1-x/r) = p.roots.map (fun r => (x-r)/(-r)) := by
    apply Multiset.map_congr rfl
    intro r h
    field_simp [hr r h]
    ring
  have hB0 : (p.roots.map (fun r => -r)).prod ≠ 0 := by
    intro h
    rw [h,mul_zero] at hz
    exact zero_ne_one hz
  rw [he,Multiset.prod_map_div]
  apply (div_eq_iff hB0).mpr
  apply (mul_left_cancel₀ hl)
  calc
    p.leadingCoeff * (p.roots.map (fun r => x-r)).prod = p.eval x :=
      (hs.eval_eq_prod_roots x).symm
    _ = p.eval x * 1 := (mul_one _).symm
    _ = p.eval x * (p.leadingCoeff * (p.roots.map (fun r => -r)).prod) := by rw [hz]
    _ = p.leadingCoeff * (p.eval x * (p.roots.map (fun r => -r)).prod) := by ring

/-- Taking real parts of normalized complex linear factors never increases their magnitude. -/
lemma real_factor_le_complex (r : ℂ) (x : ℝ) :
    |1 + (-r⁻¹).re*x| ≤ ‖1-(x:ℂ)/r‖ := by
  have h := Complex.abs_re_le_norm (1-(x:ℂ)/r)
  have he : (1-(x:ℂ)/r).re = 1+(-r⁻¹).re*x := by
    simp only [Complex.sub_re,Complex.one_re,div_eq_mul_inv,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.neg_re]
    ring
  rwa [he] at h

lemma list_real_factors_le (rs : List ℂ) (x : ℝ) :
    |(rs.map (fun r => 1+(-r⁻¹).re*x)).prod| ≤
      ‖(rs.map (fun r => 1-(x:ℂ)/r)).prod‖ := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons,List.prod_cons,abs_mul,norm_mul]
    exact mul_le_mul (real_factor_le_complex r x) ih (abs_nonneg _) (norm_nonneg _)

/-- Every normalized real polynomial admits a product of real gradient-step factors,
with the same factor count as its degree and no larger magnitude anywhere on ℝ. -/
theorem exists_list_product_dominated (p : ℝ[X]) (hp : p.eval 0=1) :
    ∃ a : List ℝ,a.length=p.natDegree ∧
      ∀ x : ℝ,|(a.map (fun d => 1+d*x)).prod| ≤ |p.eval x| := by
  let q : ℂ[X] := p.map Complex.ofRealHom
  have hq : q.eval 0=1 := by simpa [q] using congrArg Complex.ofReal hp
  let rs := q.roots.toList
  refine ⟨rs.map (fun r => (-r⁻¹).re),?_,?_⟩
  · simp only [List.length_map,rs,Multiset.length_toList]
    rw [← (IsAlgClosed.splits q).natDegree_eq_card_roots]
    exact Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective p
  · intro x
    have h := list_real_factors_le rs x
    have he : (rs.map (fun r => 1-(x:ℂ)/r)).prod = (↑(p.eval x : ℝ) : ℂ) := by
      rw [show rs=q.roots.toList from rfl,Multiset.prod_map_toList,complex_normalized_roots q hq]
      exact Polynomial.eval_map_apply (p:=p) Complex.ofRealHom x
    simpa only [List.map_map,Function.comp_def,he,Complex.norm_real,Real.norm_eq_abs] using h

lemma ofFn_of_length {α : Type*} (a : List α) (N : ℕ) (h : a.length=N) :
    ∃ d : Fin N → α,List.ofFn d=a := by
  subst N
  exact ⟨a.get,List.ofFn_get a⟩

/-- Padding by zero steps gives a dominating real schedule at any prescribed degree budget. -/
theorem exists_productPoly_dominated (N : ℕ) (p : ℝ[X])
    (hp : p.eval 0=1) (hdeg : p.natDegree ≤ N) :
    ∃ d : Fin N → ℝ,∀ x : ℝ,|(QuadraticFoundations.productPoly d).eval x| ≤ |p.eval x| := by
  obtain ⟨a,ha,hdom⟩ := exists_list_product_dominated p hp
  let b := a ++ List.replicate (N-a.length) (0:ℝ)
  have hb : b.length=N := by simp only [b,List.length_append,List.length_replicate]; omega
  obtain ⟨d,hd⟩ := ofFn_of_length b N hb
  refine ⟨d,?_⟩
  intro x
  have he : (b.map (fun s => 1+s*x)).prod=(a.map (fun s => 1+s*x)).prod := by
    simp [b]
  have hg : (QuadraticFoundations.productPoly d).eval x = (b.map (fun s => 1+s*x)).prod := by
    rw [← hd,List.map_ofFn,List.prod_ofFn]
    exact QuadraticFoundations.productPoly_eval d x
  rw [hg,he]
  exact hdom x

end QuadraticReplacement
