module
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.List.GetD

@[expose] public section
open Polynomial
namespace RootIsolation.Executable

/-- Executable rational polynomials, with the highest coefficient first.
Leading zero coefficients are allowed at the public input boundary. -/
abbrev Poly := List ℚ

/-- Mathematical interpretation; this map is used only in specifications and proofs. -/
noncomputable def denote (p : Poly) : ℚ[X] := ofCoeffList p.reverse

@[simp] theorem denote_nil : denote [] = 0 := by simp [denote]

lemma ofCoeffList_append (p q : List ℚ) :
    ofCoeffList (p ++ q) = ofCoeffList p + X ^ p.length * ofCoeffList q := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.cons_append, ofCoeffList_cons, List.length_cons, ih, pow_succ]
    ring

@[simp] theorem denote_cons (a : ℚ) (p : Poly) :
    denote (a :: p) = C a * X ^ p.length + denote p := by
  simp only [denote, List.reverse_cons, ofCoeffList_append, List.length_reverse,
    ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero]
  ring

lemma degree_denote_lt_length (p : Poly) : (denote p).degree < (p.length : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  simp only [denote, coeff_ofCoeffList]
  exact List.getD_eq_default p.reverse 0 (by simpa using hn)

lemma degree_denote_cons (a : ℚ) (p : Poly) (ha : a ≠ 0) :
    (denote (a :: p)).degree = (p.length : WithBot ℕ) := by
  rw [denote_cons, degree_add_eq_left_of_degree_lt]
  · exact degree_C_mul_X_pow _ ha
  · rw [degree_C_mul_X_pow _ ha]
    exact degree_denote_lt_length p

lemma leadingCoeff_denote_cons (a : ℚ) (p : Poly) (ha : a ≠ 0) :
    (denote (a :: p)).leadingCoeff = a := by
  rw [denote_cons, leadingCoeff_add_of_degree_lt']
  · simp
  · rw [degree_C_mul_X_pow _ ha]
    exact degree_denote_lt_length p

/-- Remove leading zero coefficients. -/
def trim : Poly → Poly
  | [] => []
  | a :: p => if a = 0 then trim p else a :: p

@[simp] theorem denote_trim (p : Poly) : denote (trim p) = denote p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    by_cases ha : a = 0
    · simp [trim, ha, ih]
    · simp [trim, ha]

lemma trim_head_ne_zero (p : Poly) : ∀ a q, trim p = a :: q → a ≠ 0 := by
  induction p with
  | nil => simp [trim]
  | cons b p ih =>
    by_cases hb : b = 0
    · simpa [trim, hb] using ih
    · intro a q h
      simp only [trim, hb, ↓reduceIte, List.cons.injEq] at h
      exact h.1 ▸ hb

lemma trim_eq_nil_iff (p : Poly) : trim p = [] ↔ denote p = 0 := by
  constructor
  · intro h
    rw [← denote_trim p, h, denote_nil]
  · intro h
    cases ht : trim p with
    | nil => rfl
    | cons a q =>
      have ha := trim_head_ne_zero p a q ht
      have hd := degree_denote_cons a q ha
      rw [← ht, denote_trim, h, degree_zero] at hd
      exact False.elim (WithBot.bot_ne_coe hd)

/-- Computable degree, using the usual convention `natDegree 0 = 0`. -/
def natDegree (p : Poly) : ℕ := (trim p).length - 1

/-- Computable leading coefficient, including `leadingCoeff 0 = 0`. -/
def leadingCoeff (p : Poly) : ℚ := (trim p).headD 0

@[simp] theorem natDegree_refines (p : Poly) : natDegree p = (denote p).natDegree := by
  cases ht : trim p with
  | nil =>
    have hp := (trim_eq_nil_iff p).mp ht
    simp [natDegree, ht, hp]
  | cons a q =>
    have hd := degree_denote_cons a q (trim_head_ne_zero p a q ht)
    rw [← ht, denote_trim] at hd
    simp only [natDegree, ht, List.length_cons, Nat.add_sub_cancel]
    exact (natDegree_eq_of_degree_eq_some hd).symm

@[simp] theorem leadingCoeff_refines (p : Poly) : leadingCoeff p = (denote p).leadingCoeff := by
  cases ht : trim p with
  | nil =>
    have hp := (trim_eq_nil_iff p).mp ht
    simp [leadingCoeff, ht, hp]
  | cons a q =>
    have hl := leadingCoeff_denote_cons a q (trim_head_ne_zero p a q ht)
    rw [← ht, denote_trim] at hl
    simpa [leadingCoeff, ht] using hl.symm

/-- Addition, subtraction, scalar multiplication, and monomials use rational list operations. -/
def add (p q : Poly) : Poly :=
  (List.zipWithAll (fun a b => a.getD 0 + b.getD 0) p.reverse q.reverse).reverse

def sub (p q : Poly) : Poly :=
  (List.zipWithAll (fun a b => a.getD 0 - b.getD 0) p.reverse q.reverse).reverse

def scale (a : ℚ) (p : Poly) : Poly := p.map (a * ·)

def monomial (a : ℚ) (n : ℕ) : Poly := a :: List.replicate n 0

@[simp] theorem denote_add (p q : Poly) : denote (add p q) = denote p + denote q := by
  simp [denote, add]

@[simp] theorem denote_sub (p q : Poly) : denote (sub p q) = denote p - denote q := by
  simp [denote, sub]

@[simp] theorem denote_scale (a : ℚ) (p : Poly) : denote (scale a p) = C a * denote p := by
  simp [denote, scale, ← List.map_reverse]

@[simp] theorem denote_replicate_zero (n : ℕ) : denote (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

@[simp] theorem denote_monomial (a : ℚ) (n : ℕ) :
    denote (monomial a n) = C a * X ^ n := by
  simp [monomial]

def shift (p : Poly) (n : ℕ) : Poly := p ++ List.replicate n 0

@[simp] theorem denote_shift (p : Poly) (n : ℕ) : denote (shift p n) = denote p * X ^ n := by
  induction p with
  | nil => simp [shift]
  | cons a p ih =>
    simp only [shift, List.cons_append, denote_cons, List.length_append, List.length_replicate] at *
    rw [ih, pow_add]
    ring

/-- Full multiplication, by a structurally recursive Horner computation. -/
def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (shift (scale a q) p.length) (mul p q)

@[simp] theorem denote_mul (p q : Poly) : denote (mul p q) = denote p * denote q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp only [mul, denote_add, denote_shift, denote_scale, ih, denote_cons]; ring

/-- A computable degree with a separate value for the zero polynomial. -/
def degree (p : Poly) : WithBot ℕ := if trim p = [] then ⊥ else (natDegree p : WithBot ℕ)

@[simp] theorem degree_refines (p : Poly) : degree p = (denote p).degree := by
  by_cases hp : trim p = []
  · simp [degree, hp, (trim_eq_nil_iff p).mp hp]
  · simp only [degree, hp, ↓reduceIte, natDegree_refines]
    exact (degree_eq_natDegree (mt (trim_eq_nil_iff p).mpr hp)).symm

/-- Executable monic long division. The mathematical interpretation occurs only in erased
proofs of monicity and termination, never in the executable body. -/
def monicDivMod (p q : Poly) (hq : (denote q).Monic) : Poly × Poly :=
  if _h : degree q ≤ degree p ∧ trim p ≠ [] then
    let z := monomial (leadingCoeff p) (natDegree p - natDegree q)
    let dm := monicDivMod (sub p (mul q z)) q hq
    (add z dm.1, dm.2)
  else ([], p)
termination_by denote p
decreasing_by
  have h' : (denote q).degree ≤ (denote p).degree ∧ denote p ≠ 0 := by
    simpa only [degree_refines, ne_eq, trim_eq_nil_iff] using _h
  simpa only [denote_sub, denote_mul, denote_monomial, leadingCoeff_refines,
    natDegree_refines] using Polynomial.div_wf_lemma h' hq

/-- Refinement of the complete pair, rather than only a reconstruction identity. -/
theorem monicDivMod_refines (p q : Poly) (hq : (denote q).Monic) :
    (denote (monicDivMod p q hq).1, denote (monicDivMod p q hq).2) =
      Polynomial.divModByMonicAux (denote p) hq := by
  rw [monicDivMod, Polynomial.divModByMonicAux]
  dsimp only
  by_cases h : degree q ≤ degree p ∧ trim p ≠ []
  · have h' : (denote q).degree ≤ (denote p).degree ∧ denote p ≠ 0 := by
      simpa only [degree_refines, ne_eq, trim_eq_nil_iff] using h
    simp only [dite_eq_left h, dite_eq_left h', denote_add]
    have ih := monicDivMod_refines
      (sub p (mul q (monomial (leadingCoeff p) (natDegree p - natDegree q)))) q hq
    simp only [denote_sub, denote_mul, denote_monomial, leadingCoeff_refines,
      natDegree_refines] at ih ⊢
    rw [Prod.mk.injEq] at ih ⊢
    exact ⟨congrArg (fun r => C (denote p).leadingCoeff *
      X ^ ((denote p).natDegree - (denote q).natDegree) + r) ih.1, ih.2⟩
  · have h' : ¬ ((denote q).degree ≤ (denote p).degree ∧ denote p ≠ 0) := by
      simpa only [degree_refines, ne_eq, trim_eq_nil_iff] using h
    simp only [dite_eq_right h, dite_eq_right h', denote_nil]
termination_by denote p
decreasing_by
  have h' : (denote q).degree ≤ (denote p).degree ∧ denote p ≠ 0 := by
    simpa only [degree_refines, ne_eq, trim_eq_nil_iff] using h
  simpa only [denote_sub, denote_mul, denote_monomial, leadingCoeff_refines,
    natDegree_refines] using Polynomial.div_wf_lemma h' hq

theorem monicDivMod_quotient (p q : Poly) (hq : (denote q).Monic) :
    denote (monicDivMod p q hq).1 = denote p /ₘ denote q := by
  simpa only [Polynomial.divByMonic, dite_eq_left hq] using
    congrArg Prod.fst (monicDivMod_refines p q hq)

theorem monicDivMod_remainder (p q : Poly) (hq : (denote q).Monic) :
    denote (monicDivMod p q hq).2 = denote p %ₘ denote q := by
  simpa only [Polynomial.modByMonic, dite_eq_left hq] using
    congrArg Prod.snd (monicDivMod_refines p q hq)

lemma normalized_monic (q : Poly) (hq : trim q ≠ []) :
    (denote (scale (leadingCoeff q)⁻¹ q)).Monic := by
  have hq' : denote q ≠ 0 := mt (trim_eq_nil_iff q).mpr hq
  simpa only [denote_scale, leadingCoeff_refines, mul_comm] using
    Polynomial.monic_mul_leadingCoeff_inv hq'

/-- General rational long division, with the Mathlib convention `(0, p)` when the divisor is zero.
The only runtime inputs are finite lists of rational coefficients. -/
def divMod (p q : Poly) : Poly × Poly :=
  if hq : trim q = [] then ([], trim p)
  else
    let dm := monicDivMod p (scale (leadingCoeff q)⁻¹ q) (normalized_monic q hq)
    (trim (scale (leadingCoeff q)⁻¹ dm.1), trim dm.2)

/-- The executable quotient agrees with field polynomial division for every input. -/
@[simp] theorem divMod_quotient (p q : Poly) :
    denote (divMod p q).1 = denote p / denote q := by
  by_cases hq : trim q = []
  · simp only [divMod, dite_eq_left hq, denote_nil]
    rw [(trim_eq_nil_iff q).mp hq, EuclideanDomain.div_zero]
  · simp only [divMod, dite_eq_right hq, denote_trim, denote_scale, monicDivMod_quotient,
      leadingCoeff_refines, Polynomial.div_def]
    rw [mul_comm (C (denote q).leadingCoeff⁻¹) (denote q)]

/-- The executable remainder agrees with field polynomial remainder for every input. -/
@[simp] theorem divMod_remainder (p q : Poly) :
    denote (divMod p q).2 = denote p % denote q := by
  by_cases hq : trim q = []
  · simp only [divMod, dite_eq_left hq, denote_trim]
    rw [(trim_eq_nil_iff q).mp hq, EuclideanDomain.mod_zero]
  · simp only [divMod, dite_eq_right hq, denote_trim, monicDivMod_remainder,
      denote_scale, leadingCoeff_refines, Polynomial.mod_def]
    rw [mul_comm (C (denote q).leadingCoeff⁻¹) (denote q)]

/-- Simultaneous refinement, including both zero dividend and zero divisor. -/
theorem divMod_refines (p q : Poly) :
    (denote (divMod p q).1, denote (divMod p q).2) =
      (denote p / denote q, denote p % denote q) := by
  simp

/-- Every Mathlib rational polynomial has a concrete input representation. -/
theorem denote_surjective : Function.Surjective denote := by
  intro p
  exact ⟨p.coeffList, Polynomial.ofCoeffList_reverse_coeffList p⟩

/-- Reconstruction is a corollary of full quotient/remainder refinement. -/
theorem divMod_reconstructs (p q : Poly) :
    denote q * denote (divMod p q).1 + denote (divMod p q).2 = denote p := by
  simp only [divMod_quotient, divMod_remainder]
  exact EuclideanDomain.div_add_mod _ _

/-- Degree reduction, needed by executable Euclidean and Bezout algorithms. -/
theorem divMod_remainder_lt (p q : Poly) (hq : trim q ≠ []) :
    (denote (divMod p q).2).degree < (denote q).degree := by
  rw [divMod_remainder]
  exact EuclideanDomain.mod_lt _ (mt (trim_eq_nil_iff q).mpr hq)

/-- Executable Euclidean gcd, with the same unnormalized convention as Mathlib. -/
def gcd (p q : Poly) : Poly :=
  if _hp : trim p = [] then trim q
  else gcd (divMod q p).2 p
termination_by denote p
decreasing_by exact divMod_remainder_lt q p _hp

@[simp] theorem gcd_refines (p q : Poly) :
    denote (gcd p q) = EuclideanDomain.gcd (denote p) (denote q) := by
  rw [gcd, EuclideanDomain.gcd]
  by_cases hp : trim p = []
  · have hp' := (trim_eq_nil_iff p).mp hp
    simp only [dite_eq_left hp, dite_eq_left hp', denote_trim]
  · have hp' := mt (trim_eq_nil_iff p).mpr hp
    simp only [dite_eq_right hp, dite_eq_right hp']
    rw [gcd_refines, divMod_remainder]
termination_by denote p
decreasing_by exact divMod_remainder_lt q p hp

/-- Extended Euclid, using only the executable arithmetic operations above. -/
def xgcdAux (r s t r' s' t' : Poly) : Poly × Poly × Poly :=
  if _hr : trim r = [] then (trim r', trim s', trim t')
  else
    let dm := divMod r' r
    xgcdAux dm.2 (sub s' (mul dm.1 s)) (sub t' (mul dm.1 t)) r s t
termination_by denote r
decreasing_by exact divMod_remainder_lt r' r _hr

theorem xgcdAux_refines (r s t r' s' t' : Poly) :
    (denote (xgcdAux r s t r' s' t').1,
      denote (xgcdAux r s t r' s' t').2.1,
      denote (xgcdAux r s t r' s' t').2.2) =
      EuclideanDomain.xgcdAux (denote r) (denote s) (denote t)
        (denote r') (denote s') (denote t') := by
  rw [xgcdAux, EuclideanDomain.xgcdAux]
  by_cases hr : trim r = []
  · have hr' := (trim_eq_nil_iff r).mp hr
    simp only [dite_eq_left hr, dite_eq_left hr', denote_trim]
  · have hr' := mt (trim_eq_nil_iff r).mpr hr
    simp only [dite_eq_right hr, dite_eq_right hr']
    have ih := xgcdAux_refines (divMod r' r).2
      (sub s' (mul (divMod r' r).1 s)) (sub t' (mul (divMod r' r).1 t)) r s t
    simpa only [denote_sub, denote_mul, divMod_quotient, divMod_remainder] using ih
termination_by denote r
decreasing_by exact divMod_remainder_lt r' r hr

/-- Both Bezout coefficients are produced in one extended-Euclidean run. -/
def xgcd (p q : Poly) : Poly × Poly := (xgcdAux p [1] [] q [] [1]).2

def gcdA (p q : Poly) : Poly := (xgcd p q).1

def gcdB (p q : Poly) : Poly := (xgcd p q).2

@[simp] theorem denote_one : denote [1] = 1 := by simp

@[simp] theorem xgcd_refines (p q : Poly) :
    (denote (xgcd p q).1, denote (xgcd p q).2) =
      EuclideanDomain.xgcd (denote p) (denote q) := by
  simpa only [xgcd, EuclideanDomain.xgcd, denote_one, denote_nil] using
    congrArg Prod.snd (xgcdAux_refines p [1] [] q [] [1])

@[simp] theorem gcdA_refines (p q : Poly) :
    denote (gcdA p q) = EuclideanDomain.gcdA (denote p) (denote q) :=
  congrArg Prod.fst (xgcd_refines p q)

@[simp] theorem gcdB_refines (p q : Poly) :
    denote (gcdB p q) = EuclideanDomain.gcdB (denote p) (denote q) :=
  congrArg Prod.snd (xgcd_refines p q)

theorem gcd_bezout (p q : Poly) :
    denote (gcd p q) = denote p * denote (gcdA p q) + denote q * denote (gcdB p q) := by
  simp only [gcd_refines, gcdA_refines, gcdB_refines]
  exact EuclideanDomain.gcd_eq_gcd_ab _ _

/-- Coefficient lookup is a concrete list lookup. -/
def coeff (p : Poly) (n : ℕ) : ℚ := p.reverse.getD n 0

@[simp] theorem coeff_refines (p : Poly) (n : ℕ) : coeff p n = (denote p).coeff n := by
  simp [coeff, denote]

/-- The deliberately simple derivative uses the already verified arithmetic layer. -/
def derivative : Poly → Poly
  | [] => []
  | a :: p => add (monomial (a * (p.length : ℚ)) (p.length - 1)) (derivative p)

@[simp] theorem derivative_refines (p : Poly) : denote (derivative p) = (denote p).derivative := by
  induction p with
  | nil => simp [derivative]
  | cons a p ih =>
    simp only [derivative, denote_add, denote_monomial, ih, denote_cons,
      Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow]

/-- Exact rational evaluation, with no calls to Mathlib's polynomial implementation. -/
def eval (p : Poly) (x : ℚ) : ℚ :=
  p.foldl (fun acc a => acc * x + a) 0

lemma eval_foldl (p : Poly) (x v : ℚ) :
    p.foldl (fun acc a => acc * x + a) v = v * x ^ p.length + (denote p).eval x := by
  induction p generalizing v with
  | nil => simp
  | cons a p ih =>
    simp only [List.foldl_cons, ih, List.length_cons, denote_cons,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, pow_succ]
    ring

@[simp] theorem eval_refines (p : Poly) (x : ℚ) : eval p x = (denote p).eval x := by
  simp [eval, eval_foldl]

end RootIsolation.Executable

-- Runtime regression checks: these use actual code generation, never proof reflection.
/-- info: ([1, 1 / 2], []) -/
#guard_msgs in
#eval RootIsolation.Executable.divMod [2, 3, 1] [2, 2]
/-- info: ([1 / 2, 0], [-1 / 2, -2]) -/
#guard_msgs in
#eval RootIsolation.Executable.divMod [1, 0, 0, -2] [2, 0, 1]
/-- info: ([], [1, 2]) -/
#guard_msgs in
#eval RootIsolation.Executable.divMod [0, 0, 1, 2] [0, 0]
/-- info: ([], []) -/
#guard_msgs in
#eval RootIsolation.Executable.divMod [0, 0] [1, 2]
/-- info: ([1, 2, 3], []) -/
#guard_msgs in
#eval RootIsolation.Executable.divMod [3, 6, 9] [3]


/-- info: [-2] -/
#guard_msgs in
#eval RootIsolation.Executable.gcd [1, 0, -2] [2, 0]
/-- info: ([1], [-1 / 2, 0]) -/
#guard_msgs in
#eval RootIsolation.Executable.xgcd [1, 0, -2] [2, 0]
/-- info: [3, -6, 3] -/
#guard_msgs in
#eval RootIsolation.Executable.derivative [1, -3, 3, -1]
/-- info: 1 -/
#guard_msgs in
#eval RootIsolation.Executable.eval [1, -3, 3, -1] 2
