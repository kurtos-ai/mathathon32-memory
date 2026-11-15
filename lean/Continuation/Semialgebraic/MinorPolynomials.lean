module
public import Continuation.Semialgebraic.MinorRank
public import RealizationCore.Coordinates
@[expose] public section
noncomputable section
namespace MemorySemialgebraic
open Matrix MvPolynomial

abbrev CoeffIndex (N : ℕ) := Fin N × Fin N
abbrev MinorIndex (N m : ℕ) :=
  Σ k : {k : Fin N // 0 < k.val},
    (Fin (m+1) → Fin (N-k.val.val)) × (Fin (m+1) → Fin k.val.val)

def polyBlock (N k : ℕ) : Matrix (Fin (N-k)) (Fin k) (MvPolynomial (CoeffIndex N) ℚ) :=
  fun i j => if hk : k ≤ N then
    X (⟨k+i.val,by omega⟩,⟨j.val,by omega⟩) else 0

def phi (N m : ℕ) (α : MinorIndex N m) : MvPolynomial (CoeffIndex N) ℚ :=
  ((polyBlock N α.1.val.val).submatrix α.2.1 α.2.2).det

def coeffEval {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) :
    MvPolynomial (CoeffIndex N) ℚ →+* ℝ :=
  eval₂Hom (Rat.castHom ℝ) (fun ij => T ij.1 ij.2)

theorem eval_polyBlock (N k : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    (polyBlock N k).map (coeffEval T) = MemoryRank.Incremental.S_k N k T := by
  ext i j
  simp only [polyBlock, Matrix.map_apply, MemoryRank.Incremental.S_k, Matrix.of_apply]
  split_ifs with hk
  · simp [coeffEval]
  · simp

theorem eval_phi (N m : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (α : MinorIndex N m) :
    coeffEval T (phi N m α) =
      ((MemoryRank.Incremental.S_k N α.1.val.val T).submatrix α.2.1 α.2.2).det := by
  rw [phi, RingHom.map_det]
  congr 1
  ext i j
  exact congrFun (congrFun (eval_polyBlock N α.1.val.val T) (α.2.1 i)) (α.2.2 j)

theorem Q_iff_phi_zero (N m : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) :
    MemoryRank.Incremental.Q N m T ↔ ∀ α : MinorIndex N m, coeffEval T (phi N m α) = 0 := by
  constructor
  · intro h α
    rw [eval_phi]
    exact (MinorSelection.rank_le_iff_minors_vanish _ m).mp
      (h α.1.val.val α.1.property α.1.val.isLt) α.2.1 α.2.2
  · intro h k hk hkN
    apply (MinorSelection.rank_le_iff_minors_vanish _ m).mpr
    intro rows cols
    exact (eval_phi N m T ⟨⟨⟨k,hkN⟩,hk⟩,rows,cols⟩).symm.trans
      (h ⟨⟨⟨k,hkN⟩,hk⟩,rows,cols⟩)

theorem realization_iff_phi_zero (N m : ℕ) (d : Fin N → ℝ)
    (T : RealizationCore.StrictIncrement N) :
    RegisterMachine.HasRealization N (RealizationCore.W_of N d T.val) (m+1) ↔
      ∀ α : MinorIndex N m, coeffEval T.val (phi N m α) = 0 := by
  exact (RealizationCore.realization_iff_coordinates N m d T).trans
    (Q_iff_phi_zero N m T.val)

end MemorySemialgebraic
