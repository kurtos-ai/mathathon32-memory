module

public import RealizationCore.Coordinates
public import Continuation.OracleTrajectory

@[expose] public section

noncomputable section

/-!
# Two-register realization of the Lemniscate coefficient array

This file proves the memory assertion in Appendix E directly from its displayed
coefficient formula.  Its row differences separate into a row factor and a
column factor.  Consequently every strict-history increment cut has rank at
most one, and the operational realization theorem supplies two total registers
(one auxiliary register).

The algebra works for every choice of real parameters.  The final definitions
substitute the actual Lemniscate formula `φ i = (1 + ζ i ^ 2) / (2 * ζ i)`.
No assertion about the calibrated parameters, optimality, or the minimax value
is needed or proved here.
-/

namespace LemniscateMemory

open Matrix RegisterMachine
open scoped BigOperators Matrix

/-- The Appendix E coefficient formula, before substituting the Lemniscate
parameters.  Natural-number indexing avoids irrelevant endpoint extensions. -/
def phiCoefficients (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j =>
  if j.val < i.val then
    -(1 / L) * (1 + ω * (φ (j.val + 1) - φ j.val) *
      (φ (N - j.val) - φ (N - i.val)))
  else 0

theorem phiCoefficients_strict (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ)
    (i j : Fin (N + 1)) (hij : i.val ≤ j.val) :
    phiCoefficients N L ω φ i j = 0 := by
  simp [phiCoefficients, show ¬ j.val < i.val by omega]

/-- Exact factorization of each strict-history row difference. -/
theorem phi_increment_entry (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ)
    (i j : Fin N) (hji : j.val < i.val) :
    RealizationCore.T_of N (phiCoefficients N L ω φ) i j =
      -(ω / L) * (φ (j.val + 1) - φ j.val) *
        (φ (N - i.val) - φ (N - i.val - 1)) := by
  simp only [RealizationCore.T_of, Matrix.of_apply, hji, dite_true,
    phiCoefficients, show j.val < i.val + 1 by omega, ite_true]
  rw [show N - (i.val + 1) = N - i.val - 1 by omega]
  ring

/-- Every increment cut is explicitly the outer product of two vectors. -/
theorem phi_cut_eq_outer (N k : ℕ) (hk : k ≤ N) (L ω : ℝ) (φ : ℕ → ℝ) :
    MemoryRank.Incremental.S_k N k
        (RealizationCore.T_of N (phiCoefficients N L ω φ)) =
      Matrix.vecMulVec
        (fun i : Fin (N - k) =>
          -(ω / L) * (φ (N - (k + i.val)) - φ (N - (k + i.val) - 1)))
        (fun j : Fin k => φ (j.val + 1) - φ j.val) := by
  ext i j
  simp only [MemoryRank.Incremental.S_k, Matrix.of_apply, hk, dite_true,
    Matrix.vecMulVec_apply]
  rw [phi_increment_entry N L ω φ _ _ (by dsimp; omega)]
  ring

theorem phi_cut_rank_le_one (N k : ℕ) (hk : k ≤ N) (L ω : ℝ) (φ : ℕ → ℝ) :
    (MemoryRank.Incremental.S_k N k
      (RealizationCore.T_of N (phiCoefficients N L ω φ))).rank ≤ 1 := by
  rw [phi_cut_eq_outer N k hk L ω φ]
  exact Matrix.rank_vecMulVec_le _ _

theorem phi_increment_mem_one (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ) :
    MemoryRank.Incremental.Q N 1
      (RealizationCore.T_of N (phiCoefficients N L ω φ)) := by
  intro k _ hk
  exact phi_cut_rank_le_one N k (Nat.le_of_lt hk) L ω φ

/-- An actual recursive implementation exists with two total registers. -/
theorem phi_has_two_register_realization (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ) :
    RegisterMachine.HasRealization N (phiCoefficients N L ω φ) 2 := by
  exact (RegisterMachine.realization_iff_incrementLocus N
    (phiCoefficients N L ω φ) 1).mpr (phi_increment_mem_one N L ω φ)

/-- Explicit implementation: the registers accumulate the two separable parts
of each history coefficient.  They start at `(x0,0)` and use identity transitions. -/
def phiMachine (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ) : Machine N 2 where
  F _ := 1
  b j := ![-(1 / L) * (1 + ω * (φ (j.val + 1) - φ j.val) * φ (N - j.val)),
    (ω / L) * (φ (j.val + 1) - φ j.val)]
  c k := ![1, φ (N - k.val)]
  o := ![1, φ 0]

theorem phiMachine_state (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ)
    (x0 : ℝ) (g : Fin N → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ N),
      stateNat N 2 (phiMachine N L ω φ) x0 g k = fun r =>
        e1 2 r * x0 + ∑ j : Fin k,
          (phiMachine N L ω φ).b ⟨j.val, by omega⟩ r * g ⟨j.val, by omega⟩ := by
  intro k
  induction k with
  | zero => intro hk; simp [stateNat]
  | succ k ih =>
    intro hk
    rw [stateNat_succ N 2 _ _ _ k (by omega)]
    funext r
    change ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
        stateNat N 2 (phiMachine N L ω φ) x0 g k) r + _ = _
    rw [Matrix.one_mulVec, ih (by omega), Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring

theorem phiMachine_readout (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ)
    (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N + 1)) :
    dot ![1, φ (N - k.val)] (stateFin N 2 (phiMachine N L ω φ) x0 g k) =
      target N (phiCoefficients N L ω φ) x0 g k := by
  rw [stateFin, phiMachine_state N L ω φ x0 g k.val (by omega)]
  simp only [dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    e1, Fin.val_zero, Fin.val_one, ite_true,
    show ¬ (1 : ℕ) = 0 by decide, ite_false, one_mul, zero_mul, zero_add]
  simp only [phiMachine, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.mul_sum]
  unfold target
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [phiCoefficients, j.isLt, ite_true]
  ring

/-- The displayed machine reproduces every query and the final output of the
coefficient array, for all formal oracle inputs. -/
theorem phiMachine_realizes (N : ℕ) (L ω : ℝ) (φ : ℕ → ℝ) :
    Realizes N 2 (phiCoefficients N L ω φ) (phiMachine N L ω φ) := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro x0 g k
    exact phiMachine_readout N L ω φ x0 g k.castSucc
  · intro x0 g
    simpa only [phiMachine, Nat.sub_self] using
      phiMachine_readout N L ω φ x0 g (⟨N, by omega⟩ : Fin (N + 1))
  · intro x0 g
    rfl

/-- The scalar parameters appearing in the cited Lemniscate method. -/
def phi (ζ : ℕ → ℝ) (i : ℕ) : ℝ := (1 + ζ i ^ 2) / (2 * ζ i)

/-- The actual Lemniscate history array in the paper's sign convention. -/
def coefficients (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  phiCoefficients N L ω (phi ζ)

theorem coefficients_entry (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ)
    (i j : Fin (N + 1)) (hji : j.val < i.val) :
    coefficients N L ω ζ i j =
      -(1 / L) * (1 + ω *
        ((1 + ζ (j.val + 1) ^ 2) / (2 * ζ (j.val + 1)) -
          (1 + ζ j.val ^ 2) / (2 * ζ j.val)) *
        ((1 + ζ (N - j.val) ^ 2) / (2 * ζ (N - j.val)) -
          (1 + ζ (N - i.val) ^ 2) / (2 * ζ (N - i.val)))) := by
  simp [coefficients, phiCoefficients, phi, hji]

theorem coefficients_strict (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ)
    (i j : Fin (N + 1)) (hij : i.val ≤ j.val) :
    coefficients N L ω ζ i j = 0 :=
  phiCoefficients_strict N L ω (phi ζ) i j hij

/-- The actual coefficient array as a well-formed strict history. -/
def history (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) : RealizationCore.StrictHistory N :=
  ⟨coefficients N L ω ζ, coefficients_strict N L ω ζ⟩

theorem increment_entry (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ)
    (i j : Fin N) (hji : j.val < i.val) :
    RealizationCore.T_of N (coefficients N L ω ζ) i j =
      -(ω / L) * (phi ζ (j.val + 1) - phi ζ j.val) *
        (phi ζ (N - i.val) - phi ζ (N - i.val - 1)) :=
  phi_increment_entry N L ω (phi ζ) i j hji

theorem cut_rank_le_one (N k : ℕ) (hk : k ≤ N) (L ω : ℝ) (ζ : ℕ → ℝ) :
    (MemoryRank.Incremental.S_k N k
      (RealizationCore.T_of N (coefficients N L ω ζ))).rank ≤ 1 :=
  phi_cut_rank_le_one N k hk L ω (phi ζ)

/-- The Lemniscate method uses at most one auxiliary vector, for every horizon.
In particular this applies to the positive calibrated parameters of Appendix E. -/
theorem has_two_register_realization (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) :
    RegisterMachine.HasRealization N (coefficients N L ω ζ) 2 :=
  phi_has_two_register_realization N L ω (phi ζ)

theorem memory_rank_le_two (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) :
    MemoryRank.CutRank.memRank N (coefficients N L ω ζ) ≤ 2 :=
  (RegisterMachine.realization_iff_maxCutRank N (coefficients N L ω ζ) 2).mp
    (has_two_register_realization N L ω ζ)

/-- Explicit two-register machine after substituting the Lemniscate parameters. -/
def machine (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) : Machine N 2 :=
  phiMachine N L ω (phi ζ)

theorem machine_realizes (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) :
    Realizes N 2 (coefficients N L ω ζ) (machine N L ω ζ) :=
  phiMachine_realizes N L ω (phi ζ)

/-- The same predetermined machine works in every finite dimension. -/
theorem machine_vectorRealizes (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) :
    VectorRealizes N 2 (coefficients N L ω ζ) (machine N L ω ζ) :=
  (vectorRealizes_iff_scalar N 2 _ _).mpr (machine_realizes N L ω ζ)

/-- The explicit two-register machine executes the actual oracle trajectory,
with all query points and the terminal output agreeing. -/
theorem machine_executes_oracle (N : ℕ) (L ω : ℝ) (ζ : ℕ → ℝ) {d : ℕ}
    (G : (Fin d → ℝ) → (Fin d → ℝ)) (x0 : Fin d → ℝ) :
    let W := coefficients N L ω ζ
    let M := machine N L ω ζ
    let g := fun j : Fin N => G (OracleTrajectory.run W G x0 j.castSucc)
    (∀ k : Fin N, vectorReadout (M.c k) (vectorStateNat M x0 g k.val) =
      OracleTrajectory.run W G x0 k.castSucc) ∧
    vectorReadout M.o (vectorStateNat M x0 g N) =
      OracleTrajectory.run W G x0 (Fin.last N) :=
  OracleTrajectory.realization_executes_oracle _ _ (machine_vectorRealizes N L ω ζ) G x0

#print axioms phi_increment_entry
#print axioms phi_cut_eq_outer
#print axioms has_two_register_realization
#print axioms memory_rank_le_two
#print axioms machine_realizes
#print axioms machine_vectorRealizes
#print axioms machine_executes_oracle

end LemniscateMemory
