module
public import Continuation.GJP.DualCoordinates
@[expose] public section
noncomputable section
open Matrix
namespace GJPDual

lemma matrix_pair_symm {n : Type*} [Fintype n] (G M : Matrix n n ℝ) (hG : G.IsSymm) :
    (∑ i,∑ j,GJP.matrixSymm M i j * G i j) = ∑ i,∑ j,M i j * G i j := by
  have hg (i j : n) : G j i=G i j := congrFun (congrFun hG i) j
  have ht : (∑ i,∑ j,M j i * G i j) = ∑ i,∑ j,M i j * G i j := by
    rw [Finset.sum_comm]
    simp only [hg]
  simp only [GJP.matrixSymm,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,
    smul_eq_mul,add_mul,mul_add,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  rw [ht]
  ring

lemma matrixFunctional_bordered {N : ℕ} (F : E N →L[ℝ] ℝ) (r : ℝ)
    (v : Q N → ℝ) (D : Matrix (Q N) (Q N) ℝ) :
    matrixFunctional F (GJP.borderedMatrix r v D) =
      r/2 * gram F (Sum.inl ()) (Sum.inl ()) -
      (∑ j,v j * gram F (Sum.inl ()) (Sum.inr j)) +
      ∑ i,∑ j,D i j * gram F (Sum.inr i) (Sum.inr j) := by
  have hg (j : Q N) : gram F (Sum.inr j) (Sum.inl ()) = gram F (Sum.inl ()) (Sum.inr j) :=
    congrFun (congrFun (gram_symm F) (Sum.inl ())) (Sum.inr j)
  have hs : (∑ j, -v j / 2 * gram F (Sum.inl ()) (Sum.inr j)) =
      -(∑ j,v j * gram F (Sum.inl ()) (Sum.inr j)) / 2 := by
    calc _ = ∑ j, -(v j * gram F (Sum.inl ()) (Sum.inr j)) / 2 := by
           apply Finset.sum_congr rfl
           intro j _
           ring
      _ = _ := by rw [← Finset.sum_div,Finset.sum_neg_distrib]
  rw [matrixFunctional_eq]
  simp only [Fintype.sum_sum_type,Fintype.sum_unique,GJP.borderedMatrix,Matrix.fromBlocks,Matrix.of_apply,
    Matrix.diagonal,Sum.elim_inl,Sum.elim_inr,ite_true,hg,Finset.sum_add_distrib]
  rw [hs]
  ring

lemma matrixFunctional_linearMatrix_single {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) (i j : Q N) :
    matrixFunctional F (linearMatrix W (0,Matrix.single i j 1)) =
      -gram F (Sum.inl ()) (Sum.inr j) +
      ∑ k,W i k * gram F (Sum.inr k) (Sum.inr j) := by
  rw [linearMatrix,matrixFunctional_bordered]
  have hG : (show Matrix (Q N) (Q N) ℝ from fun k l => gram F (Sum.inr k) (Sum.inr l)).IsSymm := by
    ext k l
    exact congrFun (congrFun (gram_symm F) (Sum.inr k)) (Sum.inr l)
  rw [matrix_pair_symm _ _ hG]
  simp [Matrix.single,ite_and,Matrix.mul_apply,Matrix.transpose_apply]

lemma matrixFunctional_radius {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) :
    matrixFunctional F (linearMatrix W (1,0)) =
      gram F (Sum.inl ()) (Sum.inl ()) / 2 := by
  rw [linearMatrix,matrixFunctional_bordered]
  simp [GJP.matrixSymm]
  ring

lemma matrixFunctional_constant {N : ℕ} (F : E N →L[ℝ] ℝ) :
    matrixFunctional F (constantMatrix N) =
      gram F (Sum.inr (Fin.last N)) (Sum.inr (Fin.last N)) / 2 := by
  rw [constantMatrix,matrixFunctional_bordered]
  simp [Matrix.vecMulVec,Pi.single_apply]
  ring

lemma functional_parts {N : ℕ} (F : E N →L[ℝ] ℝ) (e : E N) :
    F e = matrixFunctional F e.1.val + F (offInjection N e.2.1) +
      F (rowInjection N e.2.2.1) + F (colInjection N e.2.2.2) := by
  have he : e = matrixInjection N e.1 + offInjection N e.2.1 +
      rowInjection N e.2.2.1 + colInjection N e.2.2.2 := by
    ext <;> simp [matrixInjection,offInjection,rowInjection,colInjection]
  have hm : F (matrixInjection N e.1) = matrixFunctional F e.1.val := by
    change F (matrixInjection N e.1) = F (matrixInjection N (symmetrize N e.1.val))
    congr 2
    apply Subtype.ext
    exact (matrixSymm_of_symm _ e.1.property).symm
  calc F e = F (matrixInjection N e.1) + F (offInjection N e.2.1) +
      F (rowInjection N e.2.2.1) + F (colInjection N e.2.2.2) := by
        simpa only [map_add] using congrArg F he
    _ = _ := by rw [hm]

lemma functional_radius {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) :
    F (conicMap W (1,0)) = gram F (Sum.inl ()) (Sum.inl ()) / 2 := by
  rw [functional_parts]
  change matrixFunctional F (linearMatrix W (1,0)) + F (offInjection N (fun _ => -(0:ℝ))) +
    F (rowInjection N (fun _ => ∑ _ : Q N, (0:ℝ))) +
    F (colInjection N (fun _ => ∑ _ : Q N, (0:ℝ))) = _
  simp only [neg_zero,Finset.sum_const_zero]
  change matrixFunctional F (linearMatrix W (1,0)) + F (offInjection N 0) +
    F (rowInjection N 0) + F (colInjection N 0) = _
  simp only [map_zero,add_zero]
  exact matrixFunctional_radius F W

lemma functional_constant {N : ℕ} (F : E N →L[ℝ] ℝ) :
    F (constant N) = rowWeight F (Fin.last N) +
      gram F (Sum.inr (Fin.last N)) (Sum.inr (Fin.last N)) / 2 := by
  rw [functional_parts]
  change matrixFunctional F (constantMatrix N) + F (offInjection N 0) +
    rowWeight F (Fin.last N) + F (colInjection N 0) = _
  rw [map_zero,map_zero,map_zero,map_zero,add_zero,add_zero,matrixFunctional_constant,add_comm]

lemma offVector_single {N : ℕ} (i j : Q N) (hij : i ≠ j) :
    (fun kl : Off N => -(Matrix.single i j (1:ℝ)) kl.val.1 kl.val.2) =
      -Pi.single (⟨(i,j),hij⟩ : Off N) 1 := by
  ext kl
  rcases kl with ⟨⟨k,l⟩,hkl⟩
  by_cases hk : k=i <;> by_cases hl : l=j <;>
    simp [Matrix.single,Pi.single_apply,Subtype.ext_iff,Prod.mk.injEq,hk,hl,eq_comm]

lemma offVector_diagonal {N : ℕ} (i : Q N) :
    (fun kl : Off N => -(Matrix.single i i (1:ℝ)) kl.val.1 kl.val.2) = 0 := by
  ext kl
  rcases kl with ⟨⟨k,l⟩,hkl⟩
  by_cases hk : k=i
  · subst k
    change i ≠ l at hkl
    simp [Matrix.single,hkl]
  · simp [Matrix.single,Ne.symm hk]

lemma functional_single_offdiag {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) (i j : Q N) (hij : i ≠ j) :
    F (conicMap W (0,Matrix.single i j 1)) =
      -gram F (Sum.inl ()) (Sum.inr j) +
      (∑ k,W i k * gram F (Sum.inr k) (Sum.inr j)) - offWeight F ⟨(i,j),hij⟩ +
      rowWeight F i + colWeight F j := by
  rw [functional_parts]
  change matrixFunctional F (linearMatrix W (0,Matrix.single i j 1)) +
    F (offInjection N (fun kl => -(Matrix.single i j 1) kl.val.1 kl.val.2)) +
    F (rowInjection N (fun k => ∑ l,Matrix.single i j 1 k l)) +
    F (colInjection N (fun l => ∑ k,Matrix.single i j 1 k l)) = _
  have hr : (fun k => ∑ l,Matrix.single i j (1:ℝ) k l) = Pi.single i 1 := by
    ext k
    simp [Matrix.single,ite_and,Pi.single_apply,eq_comm]
  have hc : (fun l => ∑ k,Matrix.single i j (1:ℝ) k l) = Pi.single j 1 := by
    ext l
    simp [Matrix.single,ite_and,Pi.single_apply,eq_comm]
  rw [matrixFunctional_linearMatrix_single,offVector_single i j hij,hr,hc,map_neg,map_neg]
  rfl

lemma functional_single_diag {N : ℕ} (F : E N →L[ℝ] ℝ)
    (W : Matrix (Q N) (Q N) ℝ) (i : Q N) :
    F (conicMap W (0,Matrix.single i i 1)) =
      -gram F (Sum.inl ()) (Sum.inr i) +
      (∑ k,W i k * gram F (Sum.inr k) (Sum.inr i)) + rowWeight F i + colWeight F i := by
  rw [functional_parts]
  change matrixFunctional F (linearMatrix W (0,Matrix.single i i 1)) +
    F (offInjection N (fun kl => -(Matrix.single i i 1) kl.val.1 kl.val.2)) +
    F (rowInjection N (fun k => ∑ l,Matrix.single i i 1 k l)) +
    F (colInjection N (fun l => ∑ k,Matrix.single i i 1 k l)) = _
  have hr : (fun k => ∑ l,Matrix.single i i (1:ℝ) k l) = Pi.single i 1 := by
    ext k
    simp [Matrix.single,ite_and,Pi.single_apply,eq_comm]
  have hc : (fun l => ∑ k,Matrix.single i i (1:ℝ) k l) = Pi.single i 1 := by
    ext l
    simp [Matrix.single,ite_and,Pi.single_apply,eq_comm]
  rw [matrixFunctional_linearMatrix_single,offVector_diagonal,hr,hc,map_zero,map_zero,add_zero]
  rfl

end GJPDual
