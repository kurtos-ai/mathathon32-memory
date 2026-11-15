module
public import Continuation.Semialgebraic.SymbolicAffineQE
public import Mathlib.Basic.Sign.Basic
public meta import Continuation.Semialgebraic.SymbolicAffineQE

@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
namespace Formula

abbrev SignClause (n : ℕ) := List (Expr n × SignType)
abbrev SignDNF (n : ℕ) := List (SignClause n)

def clauseHolds {n : ℕ} (v : Fin n → ℝ) (c : SignClause n) : Prop :=
  ∀ es ∈ c, SignType.sign (es.1.evalReal v) = es.2

def dnfHolds {n : ℕ} (v : Fin n → ℝ) (cs : SignDNF n) : Prop :=
  ∃ c ∈ cs, clauseHolds v c

/-- Cartesian conjunction concatenates exact sign clauses. -/
def andDNF {n : ℕ} (cs ds : SignDNF n) : SignDNF n :=
  cs.flatMap (fun c => ds.map (fun d => c++d))

lemma andDNF_holds {n : ℕ} (v : Fin n → ℝ) (cs ds : SignDNF n) :
    dnfHolds v (andDNF cs ds) ↔ dnfHolds v cs ∧ dnfHolds v ds := by
  constructor
  · rintro ⟨e,he,hh⟩
    obtain ⟨c,hc,he⟩ := List.mem_flatMap.mp he
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
    exact ⟨⟨c,hc,fun es hes => hh es (List.mem_append_left _ hes)⟩,
      ⟨d,hd,fun es hes => hh es (List.mem_append_right _ hes)⟩⟩
  · rintro ⟨⟨c,hc,hcval⟩,⟨d,hd,hdval⟩⟩
    refine ⟨c++d,List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨d,hd,rfl⟩⟩,?_⟩
    intro es hes
    rcases List.mem_append.mp hes with h | h
    · exact hcval es h
    · exact hdval es h

lemma appendDNF_holds {n : ℕ} (v : Fin n → ℝ) (cs ds : SignDNF n) :
    dnfHolds v (cs++ds) ↔ dnfHolds v cs ∨ dnfHolds v ds := by
  constructor
  · rintro ⟨c,hc,hval⟩
    rcases List.mem_append.mp hc with h | h
    · exact Or.inl ⟨c,h,hval⟩
    · exact Or.inr ⟨c,h,hval⟩
  · rintro (⟨c,hc,hval⟩ | ⟨c,hc,hval⟩)
    · exact ⟨c,List.mem_append_left _ hc,hval⟩
    · exact ⟨c,List.mem_append_right _ hc,hval⟩

/-- Enumerate precisely the allowed signs of one atom. -/
def signCases {n : ℕ} (p : Expr n) (ss : List SignType) : SignDNF n :=
  ss.map (fun s => [(p,s)])

lemma signCases_holds {n : ℕ} (v : Fin n → ℝ) (p : Expr n) (ss : List SignType) :
    dnfHolds v (signCases p ss) ↔ SignType.sign (p.evalReal v) ∈ ss := by
  constructor
  · rintro ⟨c,hc,hval⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hc
    have he := hval (p,s) (by simp)
    simpa only [he] using hs
  · intro hs
    refine ⟨[(p,SignType.sign (p.evalReal v))],List.mem_map.mpr ⟨_,hs,rfl⟩,?_⟩
    intro es hes
    simpa only [List.mem_singleton.mp hes] using (rfl : SignType.sign (p.evalReal v) = _)

/-- Polarity-passing DNF avoids constructing negated polynomial predicates. -/
def toSignDNFWith {n : ℕ} : Bool → Formula n → SignDNF n
  | b,.eqZero p => signCases p (if b then [0] else [-1,1])
  | b,.positive p => signCases p (if b then [1] else [-1,0])
  | b,.nonnegative p => signCases p (if b then [0,1] else [-1])
  | true,.conj f g => andDNF (toSignDNFWith true f) (toSignDNFWith true g)
  | false,.conj f g => toSignDNFWith false f ++ toSignDNFWith false g
  | true,.disj f g => toSignDNFWith true f ++ toSignDNFWith true g
  | false,.disj f g => andDNF (toSignDNFWith false f) (toSignDNFWith false g)
  | b,.neg f => toSignDNFWith (!b) f
  | b,.tru => if b then [[]] else []
  | b,.fls => if b then [] else [[]]

/-- Every clause contains only exact sign equalities, including under arbitrary Boolean negation. -/
theorem toSignDNFWith_correct {n : ℕ} (f : Formula n) (b : Bool) (v : Fin n → ℝ) :
    dnfHolds v (toSignDNFWith b f) ↔ if b then f.evalReal v else ¬f.evalReal v := by
  classical
  induction f generalizing b with
  | eqZero p =>
    cases b <;> simp [-Expr.evalReal_refines,toSignDNFWith,signCases_holds,evalReal,
      sign_eq_neg_one_iff,sign_eq_one_iff,sign_eq_zero_iff]
  | positive p =>
    cases b <;> simp [-Expr.evalReal_refines,toSignDNFWith,signCases_holds,evalReal,
      sign_eq_neg_one_iff,sign_eq_one_iff,sign_eq_zero_iff,← le_iff_lt_or_eq]
  | nonnegative p =>
    cases b <;> simp [-Expr.evalReal_refines,toSignDNFWith,signCases_holds,evalReal,
      sign_eq_neg_one_iff,sign_eq_one_iff,sign_eq_zero_iff]
    simpa only [eq_comm] using (le_iff_eq_or_lt (a := (0:ℝ)) (b := p.evalReal v)).symm
  | conj f g ihf ihg =>
    cases b <;> simp [toSignDNFWith,andDNF_holds,appendDNF_holds,ihf,ihg,evalReal] <;> tauto
  | disj f g ihf ihg =>
    cases b <;> simp [toSignDNFWith,andDNF_holds,appendDNF_holds,ihf,ihg,evalReal]
  | neg f ih => cases b <;> simp [toSignDNFWith,ih,evalReal]
  | tru => cases b <;> simp [toSignDNFWith,dnfHolds,clauseHolds,evalReal]
  | fls => cases b <;> simp [toSignDNFWith,dnfHolds,clauseHolds,evalReal]

/-- Executable Boolean-to-sign-equality normalization consumed by sign determination. -/
def toSignDNF {n : ℕ} (f : Formula n) : List (List (Expr n × SignType)) :=
  toSignDNFWith true f

theorem toSignDNF_correct {n : ℕ} (f : Formula n) (v : Fin n → ℝ) :
    f.evalReal v ↔ ∃ c ∈ f.toSignDNF, ∀ es ∈ c, SignType.sign (es.1.evalReal v) = es.2 := by
  exact (toSignDNFWith_correct f true v).symm

end Formula
end MemorySemialgebraic.SymbolicQE
