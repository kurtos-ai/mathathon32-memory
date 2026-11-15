module
public import Continuation.Semialgebraic.FirstOrder
@[expose] public section
namespace MemorySemialgebraic.SymbolicQE.FirstOrder

def cast {n m : ℕ} (h : n = m) (f : FirstOrder n) : FirstOrder m := h ▸ f

lemma evalReal_cast {n m : ℕ} (h : n = m) (f : FirstOrder n) (v : Fin m → ℝ) :
    evalReal v (cast h f) ↔ evalReal (v ∘ Fin.cast h) f := by subst m; rfl

lemma cons_addCases_cast (k n : ℕ) (x : ℝ) (a : Fin k → ℝ) (v : Fin n → ℝ)
    (h : (k+1)+n = (k+n)+1) :
    (Fin.cons x (Fin.addCases a v)) ∘ Fin.cast h = Fin.addCases (Fin.cons x a) v := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · induction j using Fin.cases with
    | zero =>
      have he : Fin.cast h (Fin.castAdd n (0 : Fin (k+1))) = 0 := by ext; rfl
      simp [he]
    | succ j =>
      have he : Fin.cast h (Fin.castAdd n j.succ) = (Fin.castAdd n j).succ := by ext; rfl
      simp [he]
  · have he : Fin.cast h (Fin.natAdd (k+1) j) = (Fin.natAdd k j).succ := by ext; simp; omega
    simp [he]

/-- Existentially bind the first k coordinates. -/
def existsBlock : (k n : ℕ) → FirstOrder (k+n) → FirstOrder n
  | 0,n,f => cast (Nat.zero_add n) f
  | k+1,n,f => existsBlock k n (.ex (cast (by omega) f))

/-- The block syntax agrees exactly with existential quantification over a finite vector. -/
theorem existsBlock_correct (k n : ℕ) (f : FirstOrder (k+n)) (v : Fin n → ℝ) :
    evalReal v (existsBlock k n f) ↔ ∃ a : Fin k → ℝ, evalReal (Fin.addCases a v) f := by
  induction k with
  | zero =>
    rw [existsBlock,evalReal_cast]
    have he (a : Fin 0 → ℝ) : v ∘ Fin.cast (Nat.zero_add n) = Fin.addCases a v := by
      funext i
      refine Fin.addCases (fun j => Fin.elim0 j) (fun j => ?_) i
      have hj : Fin.cast (Nat.zero_add n) (Fin.natAdd 0 j) = j := by ext; simp
      simp only [Function.comp_apply,hj,Fin.addCases_right]
    constructor
    · intro h
      exact ⟨Fin.elim0,he _ ▸ h⟩
    · rintro ⟨a,ha⟩
      rwa [← he a] at ha
  | succ k ih =>
    rw [existsBlock,ih]
    simp only [evalReal,evalReal_cast]
    simp_rw [cons_addCases_cast]
    constructor
    · rintro ⟨a,x,hx⟩
      exact ⟨Fin.cons x a,hx⟩
    · rintro ⟨a,ha⟩
      refine ⟨fun j => a j.succ,a 0,?_⟩
      have he : Fin.cons (a 0) (fun j => a j.succ) = a := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rwa [he]

end MemorySemialgebraic.SymbolicQE.FirstOrder
