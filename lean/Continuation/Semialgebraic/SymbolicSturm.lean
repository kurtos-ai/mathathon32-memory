module
public import Continuation.Semialgebraic.SymbolicPseudoDivision
public import TauCeti.Algebra.Polynomial.Sturm.Infinity
public meta import Continuation.Semialgebraic.SymbolicPseudoDivision

/-!
# Symbolic signed pseudo-remainder chains

The finite sign tree normalizes each specialized remainder before proceeding.
Its fuel is bounded by the original coefficient-list length, independently of
the parameter values. Every leaf selected by real parameters refines an exact
positively scaled signed remainder chain.
-/

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.SymbolicPoly
open Polynomial TauCeti.Sturm
variable {n : ℕ}

def chainAux : ℕ → SymbolicPoly n → SymbolicPoly n → SignTree n (List (SymbolicPoly n))
  | 0, p, _ => .leaf [p]
  | k + 1, p, q => (normalizeCoeffs q).bind fun q' =>
    match q' with
    | [] => .leaf [p]
    | b :: bs => (chainAux k (b :: bs) (neg (pseudoRemainder p (b :: bs)))).map (p :: ·)

theorem chainAux_head (v : Fin n → ℝ) (k : ℕ) (p q : SymbolicPoly n) :
    ((chainAux k p q).evalReal v).head? = some p := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [chainAux, SignTree.evalReal_bind]
    cases (normalizeCoeffs q).evalReal v with
    | nil => rfl
    | cons b bs => simp only [SignTree.evalReal_map, List.head?_cons]

theorem chainAux_second (v : Fin n → ℝ) (k : ℕ) (p q : SymbolicPoly n)
    (h : q.length ≤ k) :
    denote v (((chainAux k p q).evalReal v).tail.headD []) = denote v q := by
  cases k with
  | zero =>
    have hq : q = [] := List.length_eq_zero_iff.mp (by omega)
    subst q
    rfl
  | succ k =>
    simp only [chainAux, SignTree.evalReal_bind]
    cases hq : (normalizeCoeffs q).evalReal v with
    | nil =>
      simpa only [hq, SignTree.evalReal, List.tail_cons, List.headD_nil] using
        denote_normalize v q
    | cons b bs =>
      simp only [SignTree.evalReal_map, List.tail_cons]
      have hh := chainAux_head v k (b :: bs) (neg (pseudoRemainder p (b :: bs)))
      have hd : ((chainAux k (b :: bs) (neg (pseudoRemainder p (b :: bs)))).evalReal v).headD [] =
          b :: bs := by
        rw [List.headD_eq_head?_getD, hh]
        rfl
      rw [hd]
      simpa only [hq] using denote_normalize v q

private theorem signed_prepend {p q : ℝ[X]} {cs : List ℝ[X]}
    (hp : p ≠ 0) (h : IsSignedRemainderSeq (q :: cs))
    (hr : IsRemainder p q (cs.headD 0)) : IsSignedRemainderSeq (p :: q :: cs) := by
  cases cs with
  | nil =>
    apply IsSignedRemainderSeq.pair hp
    exact hr.dvd dvd_rfl (dvd_zero _)
  | cons r cs => exact IsSignedRemainderSeq.cons hp hr h

private theorem map_headD_denote (v : Fin n → ℝ) (cs : List (SymbolicPoly n)) :
    (cs.map (denote v)).headD 0 = denote v (cs.headD []) := by
  cases cs <;> simp

theorem chainAux_signed (v : Fin n → ℝ) (k : ℕ) (p q : SymbolicPoly n)
    (hp : denote v p ≠ 0) (h : q.length ≤ k) :
    IsSignedRemainderSeq (((chainAux k p q).evalReal v).map (denote v)) := by
  induction k generalizing p q with
  | zero => exact IsSignedRemainderSeq.singleton hp
  | succ k ih =>
    simp only [chainAux, SignTree.evalReal_bind]
    cases hq : (normalizeCoeffs q).evalReal v with
    | nil => exact IsSignedRemainderSeq.singleton hp
    | cons b bs =>
      simp only [SignTree.evalReal_map]
      have hb := normalizeCoeffs_head_ne_zero v q b bs hq
      have hqne : denote v (b :: bs) ≠ 0 := by
        intro hz
        have hd := degree_cons v b bs hb
        rw [hz, degree_zero] at hd
        exact WithBot.bot_ne_coe hd
      have hlen : (neg (pseudoRemainder p (b :: bs))).length ≤ k := by
        have hnorm := normalizeCoeffs_length v q
        rw [hq] at hnorm
        have hrem := pseudoRemainder_length p b bs
        rw [length_neg]
        omega
      have hs := ih (b :: bs) (neg (pseudoRemainder p (b :: bs))) hqne hlen
      have hh := chainAux_head v k (b :: bs) (neg (pseudoRemainder p (b :: bs)))
      have hsecond := chainAux_second v k (b :: bs)
        (neg (pseudoRemainder p (b :: bs))) hlen
      cases hc : (chainAux k (b :: bs) (neg (pseudoRemainder p (b :: bs)))).evalReal v with
      | nil => simp [hc] at hh
      | cons c cs =>
        have he : c = b :: bs := by simpa only [hc, List.head?_cons, Option.some.injEq] using hh
        subst c
        simp only [hc, List.map_cons] at hs ⊢
        apply signed_prepend hp hs
        rw [map_headD_denote]
        have hsd : denote v (cs.headD []) = denote v (neg (pseudoRemainder p (b :: bs))) := by
          simpa only [hc, List.tail_cons] using hsecond
        rw [hsd]
        exact pseudoRemainder_signed v p b bs hb

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval ((chainAux 2 ([.constant 1, .constant 0, .constant (-2)] : SymbolicPoly 0)
  [.constant 2, .constant 0]).evalRat Fin.elim0).map List.length

end MemorySemialgebraic.SymbolicQE.SymbolicPoly
