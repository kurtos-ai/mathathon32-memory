module
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.WholeLine
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Roots
public import TauCeti.Algebra.Polynomial.Eval.Infinity
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Polynomial Finset SignType
open scoped Matrix
namespace MemorySemialgebraic.InfinitySamples
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The outer samples used by the real-closed-field sampling theorem. -/
def outerBound (p : R[X]) : R := (∑ x ∈ p.roots.toFinset, |x|)+1

lemma root_abs_lt_outerBound (p : R[X]) (hp : p ≠ 0) (x : R) (hx : p.eval x=0) :
    |x| < outerBound p := by
  have hm : x ∈ p.roots.toFinset := by simpa [Polynomial.mem_roots hp] using hx
  have h := Finset.single_le_sum (fun y _ => abs_nonneg y) hm
  dsimp [outerBound]
  linarith

lemma divisor_no_root_right (p q : R[X]) (hp : p ≠ 0) (hd : q ∣ p)
    (x : R) (hx : outerBound p ≤ x) : q.eval x ≠ 0 := by
  intro hq
  have h := root_abs_lt_outerBound p hp x (eval_eq_zero_of_dvd_of_eval_eq_zero hd hq)
  have ha := le_abs_self x
  linarith

lemma divisor_no_root_left (p q : R[X]) (hp : p ≠ 0) (hd : q ∣ p)
    (x : R) (hx : x ≤ -outerBound p) : q.eval x ≠ 0 := by
  intro hq
  have h := root_abs_lt_outerBound p hp x (eval_eq_zero_of_dvd_of_eval_eq_zero hd hq)
  have ha := neg_abs_le x
  linarith

/-- The outer right sample has the computable leading-coefficient sign. -/
theorem sign_outer_right (p q : R[X]) (hp : p ≠ 0) (hd : q=0 ∨ q ∣ p) :
    sign (q.eval (outerBound p)) = sign q.leadingCoeff := by
  rcases hd with rfl | hd
  · simp
  obtain ⟨b,hb⟩ := q.exists_sign_atTop
  let x := max b (outerBound p)+1
  have hx : outerBound p ≤ x := by dsimp [x]; linarith [le_max_right b (outerBound p)]
  have hb' : b < x := by dsimp [x]; linarith [le_max_left b (outerBound p)]
  exact (q.sign_eval_const hx (fun z hz => divisor_no_root_right p q hp hd z hz.1)).trans (hb x hb')

/-- The outer left sample has the leading sign multiplied by degree parity. -/
theorem sign_outer_left (p q : R[X]) (hp : p ≠ 0) (hd : q=0 ∨ q ∣ p) :
    sign (q.eval (-outerBound p)) = sign (q.leadingCoeff * (-1)^q.natDegree) := by
  rcases hd with rfl | hd
  · simp
  obtain ⟨b,hb⟩ := q.exists_sign_atBot
  let x := min b (-outerBound p)-1
  have hx : x ≤ -outerBound p := by dsimp [x]; linarith [min_le_right b (-outerBound p)]
  have hb' : x < b := by dsimp [x]; linarith [min_le_left b (-outerBound p)]
  exact (q.sign_eval_const hx (fun z hz => divisor_no_root_left p q hp hd z hz.2)).symm.trans (hb x hb')

open TauCeti.SignDetermination
variable {J : Type*} [Fintype J]

lemma family_signs_atTop (Q : J → R[X]) :
    ∃ x : R, ∀ j,sign ((Q j).eval x)=sign (Q j).leadingCoeff := by
  classical
  obtain ⟨b,hb⟩ := List.exists_signs_atTop (Finset.univ.toList.map Q)
  refine ⟨b+1,fun j => hb (Q j) ?_ _ (by linarith)⟩
  simp

lemma family_signs_atBot (Q : J → R[X]) :
    ∃ x : R, ∀ j,sign ((Q j).eval x)=sign ((Q j).leadingCoeff * (-1)^(Q j).natDegree) := by
  classical
  obtain ⟨b,hb⟩ := List.exists_signs_atBot (Finset.univ.toList.map Q)
  refine ⟨b-1,fun j => hb (Q j) ?_ _ (by linarith)⟩
  simp

/-- Whole-line sign realizability reduces to two signs at infinity and two finite root sets.
The derivative may vanish identically; its roots multiset is then empty. -/
theorem realized_iff_infinity_or_roots (Q : J → R[X]) (σ : J → SignType) :
    (∃ x : R, ∀ j,sign ((Q j).eval x)=σ j) ↔
      (∀ j,sign (Q j).leadingCoeff=σ j) ∨
      (∀ j,sign ((Q j).leadingCoeff * (-1)^(Q j).natDegree)=σ j) ∨
      (∃ x ∈ (sampleProduct Q).roots.toFinset,∀ j,sign ((Q j).eval x)=σ j) ∨
      (∃ x ∈ (sampleProduct Q).derivative.roots.toFinset,∀ j,sign ((Q j).eval x)=σ j) := by
  classical
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,hs⟩ := exists_mem_signSamples_sign_eq Q x
    have hpat (j : J) : sign ((Q j).eval y)=σ j := (hs j).trans (hx j)
    rcases ((sampleProduct Q).mem_signSamples y).mp hy with hp | hd | hl | hr
    · exact Or.inr (Or.inr (Or.inl ⟨y,hp,hpat⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨y,hd,hpat⟩))
    · right; left
      intro j
      rw [hl] at hpat
      have hdiv : Q j=0 ∨ Q j ∣ sampleProduct Q :=
        (eq_or_ne (Q j) 0).imp_right (dvd_sampleProduct Q)
      exact (sign_outer_left (sampleProduct Q) (Q j) (sampleProduct_ne_zero Q) hdiv).symm.trans (hpat j)
    · left
      intro j
      rw [hr] at hpat
      have hdiv : Q j=0 ∨ Q j ∣ sampleProduct Q :=
        (eq_or_ne (Q j) 0).imp_right (dvd_sampleProduct Q)
      exact (sign_outer_right (sampleProduct Q) (Q j) (sampleProduct_ne_zero Q) hdiv).symm.trans (hpat j)
  · rintro (ht | hb | ⟨x,hx,hs⟩ | ⟨x,hx,hs⟩)
    · obtain ⟨x,hx⟩ := family_signs_atTop Q
      exact ⟨x,fun j => (hx j).trans (ht j)⟩
    · obtain ⟨x,hx⟩ := family_signs_atBot Q
      exact ⟨x,fun j => (hx j).trans (hb j)⟩
    · exact ⟨x,hs⟩
    · exact ⟨x,hs⟩

/-- The root alternative is a sum of two nonnegative BKR tables, hence finitely many Tarski queries. -/
theorem realized_iff_infinity_or_tarski [DecidableEq J] (Q : J → R[X]) (σ : J → SignType) :
    (∃ x : R, ∀ j,sign ((Q j).eval x)=σ j) ↔
      (∀ j,sign (Q j).leadingCoeff=σ j) ∨
      (∀ j,sign ((Q j).leadingCoeff * (-1)^(Q j).natDegree)=σ j) ∨
      0 < (fullInverse J *ᵥ (fun e =>
        (tarskiQuery (sampleProduct Q) (∏ j,Q j^(e j).val) : ℚ))) σ +
        (fullInverse J *ᵥ (fun e =>
        (tarskiQuery (sampleProduct Q).derivative (∏ j,Q j^(e j).val) : ℚ))) σ := by
  rw [realized_iff_infinity_or_roots,fullInverse_mulVec_tarskiQuery,fullInverse_mulVec_tarskiQuery]
  rw [← Nat.cast_add, Nat.cast_pos, Nat.add_pos_iff_pos_or_pos,
    Finset.signCount_pos,Finset.signCount_pos]

end MemorySemialgebraic.InfinitySamples
