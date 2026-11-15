module
public import Continuation.Semialgebraic.FirstOrderBlocks
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE
namespace Expr

def renameVariables {n m : ℕ} (ρ : Fin n → Fin m) : Expr n → Expr m
  | .constant q => .constant q
  | .variable i => .variable (ρ i)
  | .add p q => .add (renameVariables ρ p) (renameVariables ρ q)
  | .neg p => .neg (renameVariables ρ p)
  | .mul p q => .mul (renameVariables ρ p) (renameVariables ρ q)

@[simp] theorem renameVariables_correct {n m : ℕ} (ρ : Fin n → Fin m)
    (e : Expr n) (v : Fin m → ℝ) :
    evalReal v (renameVariables ρ e) = evalReal (v ∘ ρ) e := by
  induction e <;> simp_all [-Expr.evalReal_refines,renameVariables,evalReal]
end Expr
namespace Formula

def renameVariables {n m : ℕ} (ρ : Fin n → Fin m) : Formula n → Formula m
  | .eqZero p => .eqZero (p.renameVariables ρ)
  | .positive p => .positive (p.renameVariables ρ)
  | .nonnegative p => .nonnegative (p.renameVariables ρ)
  | .conj f g => .conj (renameVariables ρ f) (renameVariables ρ g)
  | .disj f g => .disj (renameVariables ρ f) (renameVariables ρ g)
  | .neg f => .neg (renameVariables ρ f)
  | .tru => .tru
  | .fls => .fls

@[simp] theorem renameVariables_correct {n m : ℕ} (ρ : Fin n → Fin m)
    (f : Formula n) (v : Fin m → ℝ) :
    evalReal v (renameVariables ρ f) ↔ evalReal (v ∘ ρ) f := by
  induction f <;> simp_all [-Expr.evalReal_refines,renameVariables,evalReal]
end Formula
namespace FirstOrder

def liftRenaming {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

lemma cons_comp_liftRenaming {n m : ℕ} (ρ : Fin n → Fin m)
    (x : ℝ) (v : Fin m → ℝ) :
    (Fin.cons x v) ∘ liftRenaming ρ = Fin.cons x (v ∘ ρ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def renameVariables : {n m : ℕ} → (Fin n → Fin m) → FirstOrder n → FirstOrder m
  | _,_,ρ,.atom f => .atom (f.renameVariables ρ)
  | _,_,ρ,.conj f g => .conj (renameVariables ρ f) (renameVariables ρ g)
  | _,_,ρ,.disj f g => .disj (renameVariables ρ f) (renameVariables ρ g)
  | _,_,ρ,.neg f => .neg (renameVariables ρ f)
  | _,_,ρ,.ex f => .ex (renameVariables (liftRenaming ρ) f)
  | _,_,ρ,.all f => .all (renameVariables (liftRenaming ρ) f)

@[simp] theorem renameVariables_correct {n m : ℕ} (ρ : Fin n → Fin m)
    (f : FirstOrder n) (v : Fin m → ℝ) :
    evalReal v (renameVariables ρ f) ↔ evalReal (v ∘ ρ) f := by
  induction f generalizing m with
  | atom f => exact Formula.renameVariables_correct ρ f v
  | conj f g ihf ihg => exact and_congr (ihf ρ v) (ihg ρ v)
  | disj f g ihf ihg => exact or_congr (ihf ρ v) (ihg ρ v)
  | neg f ih => exact not_congr (ih ρ v)
  | ex f ih =>
    change (∃ x, evalReal (Fin.cons x v) (renameVariables (liftRenaming ρ) f)) ↔ _
    simp_rw [ih,cons_comp_liftRenaming]
    rfl
  | all f ih =>
    change (∀ x, evalReal (Fin.cons x v) (renameVariables (liftRenaming ρ) f)) ↔ _
    simp_rw [ih,cons_comp_liftRenaming]
    rfl

end FirstOrder
end MemorySemialgebraic.SymbolicQE
