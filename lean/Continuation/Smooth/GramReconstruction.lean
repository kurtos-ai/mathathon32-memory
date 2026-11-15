module
public import Continuation.Smooth.GramModel
@[expose] public section

open Matrix
open scoped InnerProductSpace
namespace SmoothGramModel

theorem exists_euclidean_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    ∃ B : ι → EuclideanSpace ℝ (Fin (Fintype.card ι)), gram B = M := by
  obtain ⟨A,hA⟩ := Continuation.SmoothSupport.psd_factorization M hM
  let e := Fintype.equivFin ι
  let B : ι → EuclideanSpace ℝ (Fin (Fintype.card ι)) := fun i =>
    WithLp.toLp 2 (fun r => A (e.symm r) i)
  refine ⟨B, ?_⟩
  ext i j
  rw [hA]
  simp only [gram,B,PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.mul_apply,Matrix.transpose_apply]
  simpa only [mul_comm] using e.symm.sum_comp (fun r => A r i * A r j)

theorem exists_gram_in_dimension (N : ℕ)
    (M : Matrix (Index N) (Index N) ℝ) (hM : M.PosSemidef) :
    ∃ B : Index N → EuclideanSpace ℝ (Fin (N+2)), gram B = M := by
  have h := exists_euclidean_gram M hM
  convert h using 1 <;> rw [index_card]

theorem model_data_inequalities {N n : ℕ} {L R : ℝ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Matrix (Index N) (Index N) ℝ) (φ : Fin (N+1) → ℝ)
    (hF : Feasible W L R M φ)
    (B : Index N → EuclideanSpace ℝ (Fin n)) (hB : gram B = M) :
    ∀ i j : Index N, 0 ≤ value φ i-value φ j -
      ⟪Fintype.linearCombination ℝ B (w j),
        Fintype.linearCombination ℝ B (v W i)-Fintype.linearCombination ℝ B (v W j)⟫_ℝ -
      1/(2*L) * ‖Fintype.linearCombination ℝ B (w i)-Fintype.linearCombination ℝ B (w j)‖^2 := by
  intro i j
  rw [← map_sub, ← map_sub, combination_inner, combination_norm, hB]
  exact hF.2.2 i j

/-- A smooth interpolating function for feasible Gram data executes the prescribed history. -/
theorem realize_of_interpolant {N n : ℕ} {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Matrix (Index N) (Index N) ℝ) (φ : Fin (N+1) → ℝ)
    (hF : Feasible W L R M φ)
    (B : Index N → EuclideanSpace ℝ (Fin n)) (hB : gram B = M)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hGrad : ∀ z, HasGradientAt F (G z) z) (hConv : ConvexOn ℝ Set.univ F)
    (hLip : LipschitzWith ⟨L,hL.le⟩ G)
    (hVal : ∀ i, F (Fintype.linearCombination ℝ B (v W i)) = value φ i)
    (hG : ∀ i, G (Fintype.linearCombination ℝ B (v W i)) = Fintype.linearCombination ℝ B (w i)) :
    ∃ I : SmoothAttain.Instance n L R, terminalLoss I W = φ (Fin.last N) := by
  have hG0 : G 0 = 0 := by simpa only [v,w,map_zero] using hG none
  have hF0 : F 0 = 0 := by simpa only [v,map_zero,value] using hVal none
  have hMin : IsMinOn F Set.univ 0 := by
    intro y _
    change F 0 ≤ F y
    have h := SmoothNecessary.tangent_lower hGrad hConv 0 y
    simpa only [hG0,inner_zero_left,add_zero] using h
  have hNear : ‖B none-0‖ ≤ R := by
    have hrad := hF.2.1
    rw [← hB] at hrad
    change ⟪B none,B none⟫_ℝ ≤ R^2 at hrad
    rw [real_inner_self_eq_norm_sq] at hrad
    simp only [sub_zero]
    nlinarith [norm_nonneg (B none)]
  let I : SmoothAttain.Instance n L R :=
    ⟨F,G,hGrad,hConv,⟨L,hL.le⟩,rfl,hLip,B none,0,hMin,hNear⟩
  let y : Fin (N+1) → EuclideanSpace ℝ (Fin n) := fun i =>
    Fintype.linearCombination ℝ B (v W (some i))
  have hgi (i : Fin (N+1)) : G (y i) = B (some i) := by
    simpa only [y,w,Fintype.linearCombination_apply_single,one_smul] using hG (some i)
  have hsum (i : Fin (N+1)) : y i = B none + ∑ j : Fin i.val,
      W i ⟨j.val, by omega⟩ • B (some ⟨j.val, by omega⟩) := by
    simp only [y,v,map_add,map_sum,map_smul,Fintype.linearCombination_apply_single,one_smul]
  have hy : y = OracleTrajectory.run W G (B none) := by
    apply OracleTrajectory.unique
    intro i
    rw [hsum i]
    simp_rw [hgi]
  refine ⟨I, ?_⟩
  change F (OracleTrajectory.run W G (B none) (Fin.last N)) - F 0 = _
  rw [← hy,hF0,sub_zero]
  exact hVal (some (Fin.last N))

end SmoothGramModel
