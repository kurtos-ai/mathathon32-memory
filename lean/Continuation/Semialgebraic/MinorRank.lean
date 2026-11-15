module
public import Mathlib
@[expose] public section
noncomputable section
namespace MinorSelection
open Matrix

theorem select_independent {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] (v : ι → V) (k : ℕ)
    (hk : k ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range v))) :
    ∃ pick : Fin k → ι, Function.Injective pick ∧
      LinearIndependent ℝ (v ∘ pick) := by
  obtain ⟨f,hf,hspan,hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range v)
  choose idx hidx using hf
  let emb : Fin k → Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range v))) :=
    fun i => ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
  have hinj : Function.Injective emb := by
    intro i j hij
    exact Fin.ext (congrArg
      (fun z : Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range v))) => z.val) hij)
  have hfun : v ∘ (idx ∘ emb) = f ∘ emb := by
    funext i
    exact hidx (emb i)
  have hli' : LinearIndependent ℝ (v ∘ (idx ∘ emb)) := by
    rw [hfun]
    exact hli.comp emb hinj
  refine ⟨idx ∘ emb, ?_, hli'⟩
  intro i j hij
  apply hli'.injective
  exact congrArg v hij

theorem exists_nonsingular_minor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) (hk : k ≤ A.rank) :
    ∃ (rows : Fin k → Fin m) (cols : Fin k → Fin n),
      Function.Injective rows ∧ Function.Injective cols ∧
      (A.submatrix rows cols).det ≠ 0 := by
  obtain ⟨rows,hrows,hli⟩ := select_independent A.row k
    (by rw [← A.rank_eq_finrank_span_row]; exact hk)
  let B := A.submatrix rows id
  have hliB : LinearIndependent ℝ B.row := hli
  have hB : B.rank = k := by simpa using hliB.rank_matrix
  obtain ⟨cols,hcols,hlic⟩ := select_independent B.transpose.row k
    (by rw [← B.transpose.rank_eq_finrank_span_row, Matrix.rank_transpose, hB])
  let C := B.transpose.submatrix cols id
  have hliC : LinearIndependent ℝ C.row := hlic
  have hC : C.rank = k := by simpa using hliC.rank_matrix
  have hCT : C = (A.submatrix rows cols).transpose := by ext i j; rfl
  have hrank : (A.submatrix rows cols).rank = k := by
    rw [hCT, Matrix.rank_transpose] at hC
    exact hC
  have hsurj : Function.Surjective (A.submatrix rows cols).mulVec := by
    rw [Matrix.mulVec_surjective_iff_rank_eq_card]
    simpa using hrank
  have hunit := (Matrix.mulVec_surjective_iff_isUnit).mp hsurj
  exact ⟨rows,cols,hrows,hcols,((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero⟩

theorem rank_le_iff_minors_vanish {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (r : ℕ) : A.rank ≤ r ↔
      ∀ (rows : Fin (r+1) → Fin m) (cols : Fin (r+1) → Fin n),
        (A.submatrix rows cols).det = 0 := by
  constructor
  · intro hr rows cols
    by_contra hd
    have hfull := Matrix.rank_of_det_ne_zero hd
    have hle := Matrix.rank_submatrix_le A rows cols
    simp only [Fintype.card_fin] at hfull
    omega
  · intro h
    by_contra hr
    obtain ⟨rows,cols,_,_,hne⟩ := exists_nonsingular_minor A (r+1) (by omega)
    exact hne (h rows cols)

end MinorSelection
