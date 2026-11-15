module
public import Continuation.Semialgebraic.SymbolicSigns
public import Continuation.Semialgebraic.SymbolicHeadCompilation
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Roots
public import TauCeti.FieldTheory.IsRealClosed.Real
public meta import Continuation.Semialgebraic.SymbolicSigns
public meta import Continuation.Semialgebraic.SymbolicHeadCompilation

/-!
# Executable symbolic Tarski queries

The output is a finite tree whose branches test rational polynomial expressions
in the parameters and whose leaves are integers. It computes the signed number
of distinct real roots, including all degree drops and the zero polynomial.
The proof uses the unchanged, attributed TauCeti Sturm–Tarski theorem.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.SymbolicPoly
open Polynomial TauCeti.Sturm
variable {n : ℕ}

def query (p f : SymbolicPoly n) : SignTree n ℤ :=
  (normalizeCoeffs p).bind fun p' => match p' with
  | [] => .leaf 0
  | a :: as =>
    let q := pseudoRemainder (mul f (derivative (a :: as))) (a :: as)
    (chainAux q.length (a :: as) q).bind infinityVariations

theorem query_correct (v : Fin n → ℝ) (p f : SymbolicPoly n) :
    (query p f).evalReal v = (denote v p).tarskiQuery (denote v f) := by
  simp only [query, SignTree.evalReal_bind]
  have hnorm := denote_normalize v p
  cases hnormp : (normalizeCoeffs p).evalReal v with
  | nil =>
    have hp : denote v p = 0 := by simpa only [hnormp, denote_nil] using hnorm.symm
    simp [SignTree.evalReal, hp]
  | cons a as =>
    rw [hnormp] at hnorm
    dsimp only
    rw [SignTree.evalReal_bind, infinityVariations_correct]
    let p' := a :: as
    let q := pseudoRemainder (mul f (derivative p')) p'
    have ha := normalizeCoeffs_head_ne_zero v p a as hnormp
    have hp' : denote v p' ≠ 0 := by
      intro hz
      have hd := degree_cons v a as ha
      rw [hz, degree_zero] at hd
      exact WithBot.bot_ne_coe hd
    have hs := chainAux_signed v q.length p' q hp' le_rfl
    have hh := chainAux_head v q.length p' q
    have hsecond := chainAux_second v q.length p' q le_rfl
    cases hc : (chainAux q.length p' q).evalReal v with
    | nil => simp [hc] at hh
    | cons b bs =>
      have hb : b = p' := by simpa only [hc, List.head?_cons, Option.some.injEq] using hh
      subst b
      have hseed : IsTarskiSeed (denote v p') (denote v f)
          ((bs.map (denote v)).head?.getD 0) := by
        have hhd : ((bs.map (denote v)).head?.getD 0) = denote v (bs.headD []) := by
          cases bs <;> simp
        rw [hhd]
        simp only [hc, List.tail_cons] at hsecond
        rw [hsecond]
        obtain ⟨c, hc, u, hu⟩ := pseudoRemainder_identity v (mul f (derivative p')) a as ha
        apply IsTarskiSeed.of_identity c 1 u hc zero_lt_one
        simpa only [p', q, denote_mul, denote_derivative, map_one, one_mul] using hu
      simp only [hc, List.map_cons] at hs
      have ht := sum_sign_univ hs hseed
      rw [← tarskiQuery_eq_sum, hnorm] at ht
      simpa only [List.map_cons, p', hnorm] using ht


/-- info: [1, 0, 1] -/
#guard_msgs in
#eval ([-1, 0, 1] : List ℚ).map fun y =>
  (query ([.variable 0, .constant 1] : SymbolicPoly 1) [.constant 1]).evalRat (fun _ => y)

/-- info: 0 -/
#guard_msgs in
#eval (query ([] : SymbolicPoly 0) [.constant 1]).evalRat Fin.elim0

end MemorySemialgebraic.SymbolicQE.SymbolicPoly
