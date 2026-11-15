module
public import Continuation.OracleTrajectory

/-! # Registers for a separable triangular completion

The constructive part of the completion-memory theorem: a unit lower triangular
matrix with strict lower entries `a_i · ξ_j` gives an actual `1+r` register
realization of `W = I - C⁻¹ D⁻¹`. The Gram-completion argument producing this
factorization is a separate premise, not a register or rank assumption.
-/
@[expose] public section
noncomputable section
namespace Submission2026.CompletionMemory
open Matrix RegisterMachine
open scoped BigOperators Matrix

variable {N r : ℕ}

/-- A prefix sum on a fixed index set, including the empty prefix. -/
def prefixSum (f : Fin (N+1) → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin (N+1), if j.val < k then f j else 0

@[simp] theorem prefixSum_zero (f : Fin (N+1) → ℝ) : prefixSum f 0 = 0 := by simp [prefixSum]

theorem prefixSum_succ (f : Fin (N+1) → ℝ) (k : Fin (N+1)) :
    prefixSum f (k.val+1) = prefixSum f k.val + f k := by
  have h (j : Fin (N+1)) :
      (if j.val < k.val+1 then f j else 0) =
        (if j.val < k.val then f j else 0) + (if j = k then f j else 0) := by
    by_cases hj : j = k
    · subst j; simp
    · have hv : j.val ≠ k.val := fun h => hj (Fin.ext h)
      by_cases hlt : j.val < k.val <;> simp [hj,hlt,show (j.val < k.val+1) ↔ j.val < k.val by omega]
  simp only [prefixSum,h,Finset.sum_add_distrib]
  simp

theorem prefixSum_fin (f : Fin (N+1) → ℝ) (k : ℕ) (hk : k ≤ N+1) :
    prefixSum f k = ∑ j : Fin k, f ⟨j.val,by omega⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prefixSum_succ f ⟨k,by omega⟩]
    rw [Fin.sum_univ_castSucc,ih (by omega)]
    rfl

/-- Unit lower triangular displacement matrix with the displayed separable entries. -/
def D (a ξ : Fin (N+1) → Fin r → ℝ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  fun i j => if i=j then 1 else if j < i then dot (a i) (ξ j) else 0

@[simp] theorem D_diag (a ξ : Fin (N+1) → Fin r → ℝ) (i : Fin (N+1)) :
    D a ξ i i = 1 := by simp [D]

theorem D_lower (a ξ : Fin (N+1) → Fin r → ℝ) : (D a ξ).IsLowerTriangular := by
  intro i j hij
  have h : i < j := hij
  simp [D,ne_of_lt h,not_lt_of_gt h]

theorem D_det (a ξ : Fin (N+1) → Fin r → ℝ) : (D a ξ).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (D_lower a ξ)]
  simp

theorem D_isUnit (a ξ : Fin (N+1) → Fin r → ℝ) : IsUnit (D a ξ).det := by
  rw [D_det]; exact isUnit_one

theorem D_inv_lower (a ξ : Fin (N+1) → Fin r → ℝ) : (D a ξ)⁻¹.IsLowerTriangular := by
  let := Matrix.invertibleOfIsUnitDet (D a ξ) (D_isUnit a ξ)
  exact Matrix.blockTriangular_inv_of_blockTriangular (D_lower a ξ)

/-- The cumulative-sum matrix, inverse to the first-difference matrix. -/
def B (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i j => if j ≤ i then 1 else 0

/-- The report's first-difference matrix. -/
def C (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i j =>
  (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) i j -
    Fin.cases 0 (fun k => if k.castSucc = j then 1 else 0) i

theorem C_mul_zero (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (j : Fin (N+1)) :
    (C N * A) 0 j = A 0 j := by
  simp [C,Matrix.mul_apply,Matrix.one_apply]

theorem C_mul_succ (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (i : Fin N) (j : Fin (N+1)) :
    (C N * A) i.succ j = A i.succ j - A i.castSucc j := by
  simp [C,Matrix.mul_apply,Matrix.one_apply,sub_mul,Finset.sum_sub_distrib]

theorem C_mul_B : C N * B N = 1 := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [C_mul_zero]
    simp [B,Matrix.one_apply,eq_comm]
  · rw [C_mul_succ]
    simp only [B,Matrix.one_apply]
    by_cases hj : j = k.succ
    · subst j; simp [Fin.le_iff_val_le_val]
    · have hne : j.val ≠ k.val+1 := fun h => hj (Fin.ext h)
      have he : (j ≤ k.succ) ↔ j ≤ k.castSucc := by simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]; omega
      simp [he,Ne.symm hj]

theorem C_inv : (C N)⁻¹ = B N := Matrix.inv_eq_right_inv C_mul_B

theorem B_lower : (B N).IsLowerTriangular := by
  intro i j hij
  exact ite_eq_right_iff.mpr (fun h => (not_le_of_gt hij h).elim)

theorem lower_mul_diag (A E : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hA : A.IsLowerTriangular) (hE : E.IsLowerTriangular) (i : Fin (N+1)) :
    (A*E) i i = A i i * E i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hE h,mul_zero]
    · rw [hA h,zero_mul]
  · simp

theorem D_inv_diag (a ξ : Fin (N+1) → Fin r → ℝ) (i : Fin (N+1)) :
    (D a ξ)⁻¹ i i = 1 := by
  have h := congrArg (fun M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ => M i i)
    (Matrix.mul_nonsing_inv (D a ξ) (D_isUnit a ξ))
  simpa [lower_mul_diag _ _ (D_lower a ξ) (D_inv_lower a ξ)] using h

def Omega (a ξ : Fin (N+1) → Fin r → ℝ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  (C N)⁻¹ * (D a ξ)⁻¹

def W (a ξ : Fin (N+1) → Fin r → ℝ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  1 - Omega a ξ

theorem Omega_lower (a ξ : Fin (N+1) → Fin r → ℝ) : (Omega a ξ).IsLowerTriangular := by
  rw [Omega,C_inv]
  exact B_lower.mul (D_inv_lower a ξ)

@[simp] theorem Omega_diag (a ξ : Fin (N+1) → Fin r → ℝ) (i : Fin (N+1)) :
    Omega a ξ i i = 1 := by
  rw [Omega,C_inv,lower_mul_diag _ _ B_lower (D_inv_lower a ξ)]
  simp [B,D_inv_diag]

theorem W_causal (a ξ : Fin (N+1) → Fin r → ℝ) (i j : Fin (N+1)) (h : i ≤ j) :
    W a ξ i j = 0 := by
  rcases lt_or_eq_of_le h with h | rfl
  · simp [W,ne_of_lt h,Omega_lower a ξ h]
  · simp [W]

/-- Store the iterate followed by the `r` displacement registers. -/
def machine (a ξ : Fin (N+1) → Fin r → ℝ) : Machine N (r+1) where
  F k := fun i => Fin.cases
    (Fin.cons 1 (fun j => a k.succ j - dot (a k.succ) (ξ k.castSucc) * a k.castSucc j))
    (fun l => Fin.cons 0 (fun j => (if l=j then 1 else 0) - ξ k.castSucc l*a k.castSucc j)) i
  b k := Fin.cons (-1+dot (a k.succ) (ξ k.castSucc)) (ξ k.castSucc)
  c _ := e1 (r+1)
  o := e1 (r+1)

/-- The actual displacement update displayed in the paper. -/
def nextS (a ξ : Fin (N+1) → Fin r → ℝ) (k : Fin N) (S : Fin r → ℝ) (g : ℝ) : Fin r → ℝ :=
  fun l => S l + ξ k.castSucc l*(g-dot (a k.castSucc) S)

theorem machine_step (a ξ : Fin (N+1) → Fin r → ℝ) (k : Fin N)
    (x g : ℝ) (S : Fin r → ℝ) :
    (machine a ξ).F k *ᵥ Fin.cons x S + g • (machine a ξ).b k =
      Fin.cons (x-g+dot (a k.succ) (nextS a ξ k S g)) (nextS a ξ k S g) := by
  have hs : (∑ j : Fin r, (a k.succ j - dot (a k.succ) (ξ k.castSucc) *
      a k.castSucc j)*S j) = dot (a k.succ) S -
        dot (a k.succ) (ξ k.castSucc)*dot (a k.castSucc) S := by
    simp only [sub_mul,Finset.sum_sub_distrib,dot,mul_assoc,← Finset.mul_sum]
  have hn : dot (a k.succ) (nextS a ξ k S g) = dot (a k.succ) S +
      dot (a k.succ) (ξ k.castSucc)*(g-dot (a k.castSucc) S) := by
    simp only [dot,nextS,mul_add,Finset.sum_add_distrib,← mul_assoc,← Finset.sum_mul]
  ext i
  refine Fin.cases ?_ (fun l => ?_) i
  · change (∑ j : Fin (r+1),
        Fin.cons 1 (fun j => a k.succ j-dot (a k.succ) (ξ k.castSucc)*a k.castSucc j) j *
          Fin.cons x S j) + g*(-1+dot (a k.succ) (ξ k.castSucc)) =
        x-g+dot (a k.succ) (nextS a ξ k S g)
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,one_mul]
    rw [hs,hn]
    ring
  · change (∑ j : Fin (r+1),
        Fin.cons 0 (fun j => (if l=j then 1 else 0)-ξ k.castSucc l*a k.castSucc j) j *
          Fin.cons x S j) + g*ξ k.castSucc l =
        S l+ξ k.castSucc l*(g-dot (a k.castSucc) S)
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,zero_mul,zero_add]
    have hrow : (∑ j : Fin r, ((if l=j then 1 else 0)-ξ k.castSucc l*a k.castSucc j)*S j) =
        S l-ξ k.castSucc l*dot (a k.castSucc) S := by
      simp [sub_mul,Finset.sum_sub_distrib,dot,mul_assoc,← Finset.mul_sum]
    rw [hrow]
    ring

theorem stateNat_update (a ξ : Fin (N+1) → Fin r → ℝ) (x0 : ℝ)
    (g : Fin N → ℝ) (k : Fin N) :
    stateNat N (r+1) (machine a ξ) x0 g (k.val+1) =
      (machine a ξ).F k *ᵥ stateNat N (r+1) (machine a ξ) x0 g k.val +
        g k • (machine a ξ).b k := by
  rw [stateNat_succ N (r+1) _ _ _ k.val k.isLt]
  ext i
  simp only [Matrix.mulVec,dotProduct,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem dot_prefixSum (q : Fin r → ℝ) (ξ : Fin (N+1) → Fin r → ℝ)
    (z : Fin (N+1) → ℝ) (k : ℕ) :
    dot q (fun l => prefixSum (fun j => ξ j l*z j) k) =
      prefixSum (fun j => dot q (ξ j)*z j) k := by
  simp only [dot,prefixSum,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j.val < k <;> simp [h,mul_assoc]

theorem D_entry (a ξ : Fin (N+1) → Fin r → ℝ) (i j : Fin (N+1)) :
    D a ξ i j = (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) i j +
      if j < i then dot (a i) (ξ j) else 0 := by
  by_cases h : i=j
  · subst j; simp [D]
  · simp [D,h]

theorem D_mulVec (a ξ : Fin (N+1) → Fin r → ℝ) (z : Fin (N+1) → ℝ)
    (i : Fin (N+1)) :
    (D a ξ *ᵥ z) i = z i +
      dot (a i) (fun l => prefixSum (fun j => ξ j l*z j) i.val) := by
  simp only [Matrix.mulVec,dotProduct,D_entry,add_mul,Finset.sum_add_distrib]
  rw [dot_prefixSum]
  simp only [Matrix.one_apply,ite_mul,one_mul,zero_mul]
  congr 1
  simp

theorem B_mulVec (z : Fin (N+1) → ℝ) (i : Fin (N+1)) :
    (B N *ᵥ z) i = prefixSum z (i.val+1) := by
  simp only [B,Matrix.mulVec,dotProduct,prefixSum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j ≤ i
  · have hv : j.val < i.val+1 := by have := h; change j.val ≤ i.val at this; omega
    simp only [h,hv,ite_true,one_mul]
  · have hv : ¬ j.val < i.val+1 := by
      have hn : ¬ j.val ≤ i.val := h
      omega
    simp only [h,hv,ite_false,zero_mul]

theorem Omega_mulVec (a ξ : Fin (N+1) → Fin r → ℝ) (g : Fin (N+1) → ℝ)
    (i : Fin (N+1)) :
    (Omega a ξ *ᵥ g) i = prefixSum ((D a ξ)⁻¹ *ᵥ g) (i.val+1) := by
  rw [Omega,C_inv,← Matrix.mulVec_mulVec]
  exact B_mulVec _ i

/-- Pad the query inputs by a terminal zero, which is never queried. -/
def extend (g : Fin N → ℝ) (j : Fin (N+1)) : ℝ :=
  if h : j.val < N then g ⟨j.val,h⟩ else 0

@[simp] theorem extend_castSucc (g : Fin N → ℝ) (j : Fin N) :
    extend g j.castSucc = g j := by simp [extend,j.isLt]

/-- The transformed gradients solve the triangular system exactly. -/
def transformed (a ξ : Fin (N+1) → Fin r → ℝ) (g : Fin N → ℝ) : Fin (N+1) → ℝ :=
  (D a ξ)⁻¹ *ᵥ extend g

def displacement (a ξ : Fin (N+1) → Fin r → ℝ) (g : Fin N → ℝ)
    (k : ℕ) : Fin r → ℝ := fun l => prefixSum (fun j => ξ j l*transformed a ξ g j) k

theorem transformed_equation (a ξ : Fin (N+1) → Fin r → ℝ) (g : Fin N → ℝ)
    (i : Fin (N+1)) :
    transformed a ξ g i + dot (a i) (displacement a ξ g i.val) = extend g i := by
  unfold displacement
  rw [← D_mulVec]
  change (D a ξ *ᵥ ((D a ξ)⁻¹ *ᵥ extend g)) i = _
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (D_isUnit a ξ),Matrix.one_mulVec]

theorem displacement_succ (a ξ : Fin (N+1) → Fin r → ℝ) (g : Fin N → ℝ)
    (i : Fin (N+1)) (l : Fin r) :
    displacement a ξ g (i.val+1) l =
      displacement a ξ g i.val l + ξ i l*transformed a ξ g i :=
  prefixSum_succ _ i

theorem nextS_displacement (a ξ : Fin (N+1) → Fin r → ℝ) (g : Fin N → ℝ)
    (i : Fin N) :
    nextS a ξ i (displacement a ξ g i.val) (g i) = displacement a ξ g (i.val+1) := by
  have he := transformed_equation a ξ g i.castSucc
  simp only [extend_castSucc,Fin.val_castSucc] at he
  ext l
  rw [show displacement a ξ g (i.val+1) l =
      displacement a ξ g i.val l + ξ i.castSucc l*transformed a ξ g i.castSucc from
    displacement_succ a ξ g i.castSucc l]
  simp only [nextS]
  congr 1
  congr 1
  linarith

/-- The register state is the iterate followed by the accumulated displacements. -/
theorem state_solution (a ξ : Fin (N+1) → Fin r → ℝ) (x0 : ℝ) (g : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) :
    stateNat N (r+1) (machine a ξ) x0 g k =
      Fin.cons (x0-prefixSum (transformed a ξ g) k + dot (a ⟨k,by omega⟩) (displacement a ξ g k))
        (displacement a ξ g k) := by
  induction k with
  | zero =>
    ext i
    refine Fin.cases ?_ (fun l => ?_) i <;>
      simp [stateNat,e1,displacement,dot]
  | succ k ih =>
    have hkN : k < N := by omega
    rw [stateNat_update a ξ x0 g ⟨k,hkN⟩,ih (by omega),machine_step,
      nextS_displacement]
    have he := transformed_equation a ξ g (⟨k,by omega⟩ : Fin (N+1))
    simp only [extend,hkN,dite_true] at he
    ext i
    refine Fin.cases ?_ (fun l => rfl) i
    simp only [Fin.cons_zero]
    rw [prefixSum_succ (transformed a ξ g) ⟨k,by omega⟩]
    have hi : (⟨k,hkN⟩ : Fin N).succ = (⟨k+1,by omega⟩ : Fin (N+1)) := rfl
    rw [hi]
    dsimp only at he ⊢
    linarith

theorem target_full (a ξ : Fin (N+1) → Fin r → ℝ) (x0 : ℝ) (g : Fin N → ℝ)
    (i : Fin (N+1)) :
    target N (W a ξ) x0 g i = x0 + (W a ξ *ᵥ extend g) i := by
  have hp : (∑ j : Fin i.val, W a ξ i ⟨j.val,by omega⟩ * g ⟨j.val,by omega⟩) =
      prefixSum (fun j => W a ξ i j*extend g j) i.val := by
    rw [prefixSum_fin _ _ (by omega)]
    apply Finset.sum_congr rfl
    intro j _
    simp [extend,show j.val < N by omega]
  unfold target
  rw [hp]
  congr 1
  simp only [prefixSum,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j.val < i.val
  · simp [h]
  · have hW := W_causal a ξ i j (show i ≤ j by change i.val ≤ j.val; omega)
    simp [h,hW]

theorem target_solution (a ξ : Fin (N+1) → Fin r → ℝ) (x0 : ℝ) (g : Fin N → ℝ)
    (i : Fin (N+1)) :
    target N (W a ξ) x0 g i =
      x0-prefixSum (transformed a ξ g) i.val + dot (a i) (displacement a ξ g i.val) := by
  rw [target_full,W,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply,Omega_mulVec]
  change x0 + (extend g i-prefixSum (transformed a ξ g) (i.val+1)) = _
  rw [prefixSum_succ]
  have he := transformed_equation a ξ g i
  linarith

/-- Actual register realization of the precise inverse-defined coefficient map. -/
theorem realizes (a ξ : Fin (N+1) → Fin r → ℝ) :
    Realizes N (r+1) (W a ξ) (machine a ξ) := by
  refine ⟨by omega,?_,?_,?_⟩
  · intro x0 g k
    rw [target_solution]
    rw [stateFin,state_solution a ξ x0 g k.val (by omega)]
    simp [machine,dot,e1]
  · intro x0 g
    rw [target_solution]
    rw [stateFin,state_solution a ξ x0 g N (by omega)]
    simp [machine,dot,e1]
  · intro x0 g
    rfl

theorem vectorRealizes (a ξ : Fin (N+1) → Fin r → ℝ) :
    VectorRealizes N (r+1) (W a ξ) (machine a ξ) :=
  (vectorRealizes_iff_scalar N (r+1) _ _).mpr (realizes a ξ)

theorem cut_rank_le (a ξ : Fin (N+1) → Fin r → ℝ) (k : ℕ) (hk : k ≤ N) :
    (RegisterMachine.H_k N k hk (W a ξ)).rank ≤ r+1 :=
  necessity_rank_le_unconditional N (r+1) _ k hk ⟨machine a ξ,realizes a ξ⟩

theorem memory_le (a ξ : Fin (N+1) → Fin r → ℝ) :
    MemoryRank.CutRank.memRank N (W a ξ) ≤ r+1 :=
  maxCutRank_le_registers N (r+1) _ ⟨machine a ξ,realizes a ξ⟩

/-- Recognition of the report's natural separable-factorization premise. -/
theorem eq_D_of_separable (E : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (a ξ : Fin (N+1) → Fin r → ℝ) (hlower : E.IsLowerTriangular)
    (hdiag : ∀ i, E i i = 1) (hsep : ∀ i j, j < i → E i j = dot (a i) (ξ j)) : E = D a ξ := by
  ext i j
  rcases lt_trichotomy j i with h | rfl | h
  · simp [D,ne_of_gt h,hsep i j h,h]
  · simp [hdiag]
  · simp [D,ne_of_lt h,not_lt_of_gt h,hlower h]

/-- The inverse construction needs no assumed register realization or rank bound. -/
theorem realizes_of_separable (E : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (a ξ : Fin (N+1) → Fin r → ℝ) (hlower : E.IsLowerTriangular)
    (hdiag : ∀ i, E i i = 1) (hsep : ∀ i j, j < i → E i j = dot (a i) (ξ j)) :
    VectorRealizes N (r+1) (1-(C N)⁻¹*E⁻¹) (machine a ξ) := by
  rw [eq_D_of_separable E a ξ hlower hdiag hsep]
  exact vectorRealizes a ξ

theorem memory_le_of_separable (E : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (a ξ : Fin (N+1) → Fin r → ℝ) (hlower : E.IsLowerTriangular)
    (hdiag : ∀ i, E i i = 1) (hsep : ∀ i j, j < i → E i j = dot (a i) (ξ j)) :
    MemoryRank.CutRank.memRank N (1-(C N)⁻¹*E⁻¹) ≤ 1+r := by
  rw [eq_D_of_separable E a ξ hlower hdiag hsep]
  simpa [Nat.add_comm,W,Omega] using memory_le a ξ

/-- The same predetermined machine realizes the queries and output of an actual oracle. -/
theorem executes_oracle (a ξ : Fin (N+1) → Fin r → ℝ) {d : ℕ}
    (G : (Fin d → ℝ) → (Fin d → ℝ)) (x0 : Fin d → ℝ) :
    let g := fun j : Fin N => G (OracleTrajectory.run (W a ξ) G x0 j.castSucc)
    (∀ k : Fin N, vectorReadout ((machine a ξ).c k)
      (vectorStateNat (machine a ξ) x0 g k.val) =
      OracleTrajectory.run (W a ξ) G x0 k.castSucc) ∧
    vectorReadout (machine a ξ).o (vectorStateNat (machine a ξ) x0 g N) =
      OracleTrajectory.run (W a ξ) G x0 (Fin.last N) :=
  OracleTrajectory.realization_executes_oracle _ _ (vectorRealizes a ξ) G x0

#print axioms state_solution
#print axioms executes_oracle
#print axioms realizes
#print axioms vectorRealizes
#print axioms memory_le_of_separable
end Submission2026.CompletionMemory
