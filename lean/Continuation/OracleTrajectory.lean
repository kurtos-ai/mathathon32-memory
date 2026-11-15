module
public import RealizationCore.VectorRealization
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section

namespace OracleTrajectory
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- All query points and the terminal point, evaluated with the actual oracle. -/
noncomputable def run (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : V → V) (x0 : V) : Fin (N+1) → V :=
  (measure (fun i : Fin (N+1) => i.val)).wf.fix fun i rec =>
    x0 + ∑ j : Fin i.val, W i ⟨j.val, by omega⟩ • G (rec ⟨j.val, by omega⟩ j.isLt)

theorem run_eq (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : V → V) (x0 : V) (i : Fin (N+1)) :
    run W G x0 i = x0 + ∑ j : Fin i.val, W i ⟨j.val, by omega⟩ • G (run W G x0 ⟨j.val, by omega⟩) := by
  unfold run
  rw [WellFounded.fix_eq]

theorem run_zero (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : V → V) (x0 : V) : run W G x0 0 = x0 := by
  rw [run_eq]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro j _
  exact Fin.elim0 j

theorem unique (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : V → V) (x0 : V) (y : Fin (N+1) → V)
    (hy : ∀ i : Fin (N+1), y i = x0 + ∑ j : Fin i.val,
      W i ⟨j.val, by omega⟩ • G (y ⟨j.val, by omega⟩)) : y = run W G x0 := by
  funext i
  induction i using (measure (fun i : Fin (N+1) => i.val)).wf.induction with
  | h i ih =>
    rw [hy, run_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih ⟨j.val, by omega⟩ j.isLt]

/-- A fixed zero-chain suffices for every predetermined linear-history method. -/
theorem zero_chain (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : V → V) (S : ℕ → Submodule ℝ V) (hS : Monotone S)
    (hG : ∀ k < N, ∀ z ∈ S k, G z ∈ S (k+1)) (i : Fin (N+1)) :
    run W G 0 i ∈ S i.val := by
  induction i using (measure (fun i : Fin (N+1) => i.val)).wf.induction with
  | h i ih =>
    rw [run_eq, zero_add]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    apply hS (show j.val+1 ≤ i.val by omega)
    apply hG j.val (by omega)
    exact ih ⟨j.val, by omega⟩ j.isLt

theorem run_eq_vectorTarget {d : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : (Fin d → ℝ) → (Fin d → ℝ)) (x0 : Fin d → ℝ) (i : Fin (N+1)) :
    run W G x0 i = RegisterMachine.vectorTarget W x0
      (fun j : Fin N => G (run W G x0 j.castSucc)) i := by
  rw [run_eq]
  funext a
  simp only [RegisterMachine.vectorTarget, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  congr 1

theorem realization_executes_oracle {d s : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : RegisterMachine.Machine N s)
    (hM : RegisterMachine.VectorRealizes N s W M)
    (G : (Fin d → ℝ) → (Fin d → ℝ)) (x0 : Fin d → ℝ) :
    let g := fun j : Fin N => G (run W G x0 j.castSucc)
    (∀ k : Fin N, RegisterMachine.vectorReadout (M.c k)
      (RegisterMachine.vectorStateNat M x0 g k.val) = run W G x0 k.castSucc) ∧
    RegisterMachine.vectorReadout M.o (RegisterMachine.vectorStateNat M x0 g N) =
      run W G x0 (Fin.last N) := by
  dsimp only
  obtain ⟨hq,ho⟩ := hM.2 d x0 (fun j : Fin N => G (run W G x0 j.castSucc))
  constructor
  · intro k
    rw [run_eq_vectorTarget]
    exact hq k
  · rw [run_eq_vectorTarget]
    exact ho

end OracleTrajectory
