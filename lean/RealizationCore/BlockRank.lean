module
public import Mathlib
@[expose] public section
noncomputable section
namespace MemoryBlock

def splitFin (n : ℕ) : (Fin (n+1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin n → ℝ) where
  toFun v := (v 0, fun i => v i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv v := by ext i; cases i using Fin.cases <;> simp
  right_inv p := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blockOne {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => B i' j') j) i

theorem blockOne_mulVec {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (c : ℝ) (v : Fin n → ℝ) :
    (blockOne B).mulVec (Fin.cons c v) = Fin.cons c (B.mulVec v) := by
  ext i
  cases i using Fin.cases <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, blockOne]

def submoduleProdEquiv {U V : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] (A : Submodule ℝ U) (B : Submodule ℝ V) :
    (A.prod B) ≃ₗ[ℝ] A × B where
  toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  invFun x := ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem blockOne_rank {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    (blockOne B).rank = 1 + B.rank := by
  let f := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap B.mulVecLin
  have hf : (splitFin m).toLinearMap.comp
      ((blockOne B).mulVecLin.comp (splitFin n).symm.toLinearMap) = f := by
    apply LinearMap.ext
    intro p
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    change splitFin m ((blockOne B).mulVec (Fin.cons p.1 p.2)) = _
    rw [blockOne_mulVec]
    rfl
  have hdim : Module.finrank ℝ f.range = (blockOne B).rank := by
    rw [← hf, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]
    rfl
  rw [← hdim]
  change Module.finrank ℝ (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap B.mulVecLin).range) = _
  rw [LinearMap.range_prodMap, LinearMap.range_id]
  rw [(submoduleProdEquiv (⊤ : Submodule ℝ ℝ) B.mulVecLin.range).finrank_eq]
  simp [Module.finrank_prod, Matrix.rank]

def upperBlock {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin (m+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.cases (Fin.cases 1 a j)
    (fun i' => Fin.cases 0 (fun j' => B i' j') j) i

theorem upperBlock_mulVec {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n → ℝ) (c : ℝ) (v : Fin n → ℝ) :
    (upperBlock B a).mulVec (Fin.cons c v) =
      Fin.cons (c + dotProduct a v) (B.mulVec v) := by
  ext i
  cases i using Fin.cases <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, upperBlock]

theorem upperBlock_mulVec_any {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n → ℝ) (v : Fin (n+1) → ℝ) :
    (upperBlock B a).mulVec v =
      Fin.cons (v 0 + dotProduct a (Fin.tail v)) (B.mulVec (Fin.tail v)) := by
  simpa only [Fin.cons_self_tail] using upperBlock_mulVec B a (v 0) (Fin.tail v)

theorem blockOne_mulVec_any {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin (n+1) → ℝ) :
    (blockOne B).mulVec v = Fin.cons (v 0) (B.mulVec (Fin.tail v)) := by
  simpa only [Fin.cons_self_tail] using blockOne_mulVec B (v 0) (Fin.tail v)

theorem upperBlock_range {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    (upperBlock B a).mulVecLin.range = (blockOne B).mulVecLin.range := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨Fin.cons (x 0 + dotProduct a (Fin.tail x)) (Fin.tail x), ?_⟩
    simp only [Matrix.mulVecLin_apply, blockOne_mulVec, upperBlock_mulVec_any]
  · rintro y ⟨x, rfl⟩
    refine ⟨Fin.cons (x 0 - dotProduct a (Fin.tail x)) (Fin.tail x), ?_⟩
    simp only [Matrix.mulVecLin_apply, upperBlock_mulVec, blockOne_mulVec_any,
      sub_add_cancel]

/-- A unit pivot adds exactly one to the rank, even with arbitrary first row. -/
theorem upperBlock_rank {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n → ℝ) : (upperBlock B a).rank = 1 + B.rank := by
  calc (upperBlock B a).rank = (blockOne B).rank := by
         exact congrArg (fun V : Submodule ℝ (Fin (m+1) → ℝ) => Module.finrank ℝ V)
           (upperBlock_range B a)
       _ = 1 + B.rank := blockOne_rank B

#print axioms blockOne_rank
#print axioms upperBlock_rank
end MemoryBlock
