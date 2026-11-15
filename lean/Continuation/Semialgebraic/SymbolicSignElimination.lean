module
public import Continuation.Semialgebraic.SymbolicSignCounts
public meta import Continuation.Semialgebraic.SymbolicSignCounts

/-! # Nonlinear elimination of a finite sign condition

This produces rational quantifier-free syntax in the parameters for the existence
of a real head variable realizing an arbitrary finite family of polynomial signs.
No degree restriction or unknown projection/feasibility hypothesis is imposed.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
open Polynomial SignType TauCeti.SignDetermination
variable {n m : ℕ}

namespace SymbolicPoly

def infinityCondition (Q : Fin m → SymbolicPoly n) (σ : Fin m → SignType)
    (positive : Bool) : Formula n :=
  Formula.all (List.ofFn fun j => (infinitySigns (Q j)).toFormula fun s =>
    decide ((if positive then s.2 else s.1) = σ j))

theorem infinityCondition_correct (v : Fin n → ℝ) (Q : Fin m → SymbolicPoly n)
    (σ : Fin m → SignType) (positive : Bool) :
    (infinityCondition Q σ positive).evalReal v ↔
      ∀ j, (if positive then sign (denote v (Q j)).leadingCoeff
        else sign ((denote v (Q j)).leadingCoeff * (-1) ^ (denote v (Q j)).natDegree)) = σ j := by
  simp only [infinityCondition, Formula.all_eval, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, SignTree.toFormula_correct, infinitySigns_correct,
    decide_eq_true_eq]

def rootCondition (Q : Fin m → SymbolicPoly n) (σ : Fin m → SignType) : Formula n :=
  ((familyProduct Q).pruneConstants.bind fun p =>
    SignTree.sumRational [count p Q σ, count (derivative p) Q σ]).toFormula (fun a => decide (0 < a))

theorem rootCondition_correct (v : Fin n → ℝ) (Q : Fin m → SymbolicPoly n)
    (σ : Fin m → SignType) :
    (rootCondition Q σ).evalReal v ↔
      0 < (Finset.signCount (sampleProduct (fun j => denote v (Q j))).roots.toFinset
          (fun j => denote v (Q j)) σ : ℚ) +
        (Finset.signCount (sampleProduct (fun j => denote v (Q j))).derivative.roots.toFinset
          (fun j => denote v (Q j)) σ : ℚ) := by
  simp only [rootCondition, SignTree.toFormula_correct, SignTree.evalReal_bind,
    SignTree.pruneConstants_correct,
    SignTree.sumRational_correct, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, count_correct, denote_derivative, familyProduct_correct,
    decide_eq_true_eq]

def eliminateSignCondition (Q : Fin m → SymbolicPoly n) (σ : Fin m → SignType) : Formula n :=
  .disj (infinityCondition Q σ true)
    (.disj (infinityCondition Q σ false) (rootCondition Q σ))

theorem eliminateSignCondition_correct (v : Fin n → ℝ) (Q : Fin m → SymbolicPoly n)
    (σ : Fin m → SignType) :
    (eliminateSignCondition Q σ).evalReal v ↔
      ∃ x : ℝ, ∀ j, sign ((denote v (Q j)).eval x) = σ j := by
  simp only [eliminateSignCondition, Formula.evalReal, infinityCondition_correct,
    rootCondition_correct, ↓reduceIte, Bool.false_eq_true]
  rw [MemorySemialgebraic.InfinitySamples.realized_iff_infinity_or_tarski,
    fullInverse_mulVec_tarskiQuery, fullInverse_mulVec_tarskiQuery]

end SymbolicPoly
end MemorySemialgebraic.SymbolicQE
