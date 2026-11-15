module
public import Continuation.GJP.HistoryNormalization
public import Continuation.Smooth.GramExact

@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {N : ℕ}

/-- Convert the source paper's unit lower coefficients to additive history coefficients. -/
def additiveHistory (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := 1-W

lemma additiveHistory_strict {W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hW : UnitLower W) :
    ∀ i j, i.val ≤ j.val → additiveHistory W i j = 0 := by
  intro i j hij
  rcases eq_or_lt_of_le hij with heq | hlt
  · have he : i=j := Fin.ext heq
    subst j
    simp [additiveHistory,hW.2]
  · have hzero := hW.1 (show i<j from hlt)
    simp [additiveHistory,hzero,Matrix.one_apply,ne_of_lt (show i<j from hlt)]

lemma sourceMatrix_additiveHistory (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    sourceMatrix 1 (additiveHistory W) = W := by
  simp [sourceMatrix,additiveHistory]

lemma additiveHistory_sourceMatrix (L : ℝ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    additiveHistory (sourceMatrix L W) = L • W := by
  simp [additiveHistory,sourceMatrix]

lemma gram_v_none (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Fin (N+1)) :
    SmoothGramModel.v U (some i) none = 1 := by
  simp [SmoothGramModel.v, Pi.single_apply]

lemma gram_v_some (U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i j : Fin (N+1)) :
    SmoothGramModel.v U (some i) (some j) = if j < i then U i j else 0 := by
  classical
  simp only [SmoothGramModel.v, Pi.add_apply, Pi.single_eq_of_ne (Option.some_ne_none _),
    zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hji : j < i
  · rw [if_pos hji]
    let k : Fin i.val := ⟨j.val,hji⟩
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro b hb hbk
      have hbj : (⟨b.val, by omega⟩ : Fin (N+1)) ≠ j := by
        intro he
        apply hbk
        apply Fin.ext
        change b.val = j.val
        exact congrArg (fun a : Fin (N+1) => a.val) he
      simp [Pi.single_apply,hbj,Ne.symm hbj]
    · simp
  · rw [if_neg hji]
    apply Finset.sum_eq_zero
    intro b hb
    have hbj : (⟨b.val, by omega⟩ : Fin (N+1)) ≠ j := by
      intro he
      have he' : b.val = j.val := congrArg (fun a : Fin (N+1) => a.val) he
      apply hji
      change j.val < i.val
      omega
    simp [Pi.single_apply,hbj,Ne.symm hbj]

/-- The source coordinates `xᵢ−gᵢ` as coefficient vectors in the actual Gram model. -/
def shiftedSite (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Fin (N+1)) :
    SmoothGramModel.Index N → ℝ :=
  Pi.single none 1 - ∑ j, W i j • Pi.single (some j) 1

lemma shiftedSite_none (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Fin (N+1)) :
    shiftedSite W i none = 1 := by
  simp [shiftedSite,Pi.single_apply]

lemma shiftedSite_some (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i j : Fin (N+1)) :
    shiftedSite W i (some j) = -W i j := by
  simp [shiftedSite,Pi.single_apply]

lemma gram_shiftedSite {W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hW : UnitLower W)
    (i : Fin (N+1)) :
    SmoothGramModel.v (additiveHistory W) (some i) - SmoothGramModel.w (some i) =
      shiftedSite W i := by
  funext k
  cases k with
  | none => simp [gram_v_none,SmoothGramModel.w,shiftedSite_none]
  | some j =>
    change SmoothGramModel.v (additiveHistory W) (some i) (some j) -
      (Pi.single (some i) (1:ℝ) : SmoothGramModel.Index N → ℝ) (some j) = _
    rw [gram_v_some,shiftedSite_some]
    rcases lt_trichotomy j i with hji | rfl | hij
    · simp [hji,additiveHistory,Matrix.one_apply,ne_of_gt hji,ne_of_lt hji]
    · simp [hW.2]
    · have hw := hW.1 hij
      simp [not_lt_of_gt hij,Pi.single_apply,ne_of_lt hij,ne_of_gt hij,hw]

/-- The index conversion from the conic block layout to the actual Gram model. -/
def gramIndex : SmoothGramModel.Index N → Unit ⊕ Fin (N+1)
  | none => Sum.inl ()
  | some i => Sum.inr i

def gramOfBlock (G : Matrix (Unit ⊕ Fin (N+1)) (Unit ⊕ Fin (N+1)) ℝ) :
    Matrix (SmoothGramModel.Index N) (SmoothGramModel.Index N) ℝ :=
  G.submatrix gramIndex gramIndex

lemma gramOfBlock_psd {G : Matrix (Unit ⊕ Fin (N+1)) (Unit ⊕ Fin (N+1)) ℝ}
    (hG : G.PosSemidef) : (gramOfBlock G).PosSemidef := hG.submatrix gramIndex

/-- The shifted inner products supplied by the conic dual coordinates. -/
def shiftedPairing (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : Matrix (Unit ⊕ Fin (N+1)) (Unit ⊕ Fin (N+1)) ℝ) (i j : Fin (N+1)) : ℝ :=
  G (Sum.inl ()) (Sum.inr j) - ∑ k, W i k * G (Sum.inr k) (Sum.inr j)

lemma shiftedSite_pairing (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (G : Matrix (Unit ⊕ Fin (N+1)) (Unit ⊕ Fin (N+1)) ℝ) (i j : Fin (N+1)) :
    shiftedSite W i ⬝ᵥ (gramOfBlock G *ᵥ SmoothGramModel.w (some j)) =
      shiftedPairing W G i j := by
  simp [shiftedSite,SmoothGramModel.w,sub_dotProduct,sum_dotProduct,smul_dotProduct,
    single_dotProduct,Matrix.mulVec_single,gramOfBlock,gramIndex,shiftedPairing]

lemma shifted_interpolation_identity {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (xi xj gi gj : ι → ℝ) (fi fj : ℝ) :
    (fi + (gi ⬝ᵥ (M *ᵥ gi))/2) - (fj + (gj ⬝ᵥ (M *ᵥ gj))/2) -
      gj ⬝ᵥ (M *ᵥ (xi-xj)) -
      (1/2:ℝ) * ((gi-gj) ⬝ᵥ (M *ᵥ (gi-gj))) =
      fi-fj - ((xi-gi) ⬝ᵥ (M *ᵥ gj)) + ((xj-gj) ⬝ᵥ (M *ᵥ gj)) := by
  simp only [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub]
  rw [show gj ⬝ᵥ (M *ᵥ xi) = xi ⬝ᵥ (M *ᵥ gj) from hM.dotProduct_mulVec_comm,
    show gj ⬝ᵥ (M *ᵥ xj) = xj ⬝ᵥ (M *ᵥ gj) from hM.dotProduct_mulVec_comm,
    show gj ⬝ᵥ (M *ᵥ gi) = gi ⬝ᵥ (M *ᵥ gj) from hM.dotProduct_mulVec_comm]
  ring

/-- Coordinate inequalities imply the full THG interpolation system, including the minimizer. -/
theorem feasible_of_shifted_coordinates
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hW : UnitLower W)
    (G : Matrix (Unit ⊕ Fin (N+1)) (Unit ⊕ Fin (N+1)) ℝ)
    (f h : Fin (N+1) → ℝ) (hG : G.PosSemidef)
    (hradius : G (Sum.inl ()) (Sum.inl ()) ≤ 2)
    (hf : ∀ i, 0 ≤ f i) (hh : ∀ i, 0 ≤ h i)
    (hdiag : ∀ i, shiftedPairing W G i i = f i+h i)
    (hpair : ∀ i j, shiftedPairing W G i j ≤ f i+h j) :
    SmoothGramModel.Feasible (additiveHistory W) 1 (Real.sqrt 2) (gramOfBlock G)
      (fun i => f i+G (Sum.inr i) (Sum.inr i)/2) := by
  let M := gramOfBlock G
  let U := additiveHistory W
  let φ := fun i => f i+G (Sum.inr i) (Sum.inr i)/2
  have hMsym : M.IsSymm := (gramOfBlock_psd hG).isHermitian.isSymm
  have hvalue (i : SmoothGramModel.Index N) : SmoothGramModel.value φ i =
      SmoothGramModel.value f i +
        (SmoothGramModel.w i ⬝ᵥ (M *ᵥ SmoothGramModel.w i))/2 := by
    cases i <;> simp [SmoothGramModel.value,SmoothGramModel.w,φ,M,
      single_dotProduct,Matrix.mulVec_single,gramOfBlock,gramIndex]
  have hdiagext (i : SmoothGramModel.Index N) :
      (SmoothGramModel.v U i-SmoothGramModel.w i) ⬝ᵥ (M *ᵥ SmoothGramModel.w i) =
      SmoothGramModel.value f i+SmoothGramModel.value h i := by
    cases i with
    | none => simp [SmoothGramModel.v,SmoothGramModel.w,SmoothGramModel.value]
    | some i =>
      change (SmoothGramModel.v (additiveHistory W) (some i)-SmoothGramModel.w (some i)) ⬝ᵥ
        (gramOfBlock G *ᵥ SmoothGramModel.w (some i)) = f i+h i
      rw [gram_shiftedSite hW,shiftedSite_pairing,hdiag]
  have hpairext (i j : SmoothGramModel.Index N) :
      (SmoothGramModel.v U i-SmoothGramModel.w i) ⬝ᵥ (M *ᵥ SmoothGramModel.w j) ≤
      SmoothGramModel.value f i+SmoothGramModel.value h j := by
    cases i with
    | none =>
      cases j with
      | none => simp [SmoothGramModel.v,SmoothGramModel.w,SmoothGramModel.value]
      | some j => simpa [SmoothGramModel.v,SmoothGramModel.w,SmoothGramModel.value] using hh j
    | some i =>
      cases j with
      | none => simpa [SmoothGramModel.w,SmoothGramModel.value] using hf i
      | some j =>
        change (SmoothGramModel.v (additiveHistory W) (some i)-SmoothGramModel.w (some i)) ⬝ᵥ
          (gramOfBlock G *ᵥ SmoothGramModel.w (some j)) ≤ f i+h j
        rw [gram_shiftedSite hW,shiftedSite_pairing]
        exact hpair i j
  refine ⟨gramOfBlock_psd hG,?_,?_⟩
  · simpa [gramOfBlock,gramIndex,Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)] using hradius
  · intro i j
    change 0 ≤ SmoothGramModel.value φ i-SmoothGramModel.value φ j -
      SmoothGramModel.w j ⬝ᵥ (M *ᵥ (SmoothGramModel.v U i-SmoothGramModel.v U j)) -
      1/(2*1) * ((SmoothGramModel.w i-SmoothGramModel.w j) ⬝ᵥ
        (M *ᵥ (SmoothGramModel.w i-SmoothGramModel.w j)))
    rw [hvalue i,hvalue j]
    norm_num only [mul_one]
    rw [shifted_interpolation_identity M hMsym,hdiagext]
    linarith [hpairext i j]

/-- The conic coordinates are realized by an actual smooth-convex instance. -/
theorem shifted_coordinates_actual_loss
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hW : UnitLower W)
    (G : Matrix (Unit ⊕ Fin (N+1)) (Unit ⊕ Fin (N+1)) ℝ)
    (f h : Fin (N+1) → ℝ) (hG : G.PosSemidef)
    (hradius : G (Sum.inl ()) (Sum.inl ()) ≤ 2)
    (hf : ∀ i, 0 ≤ f i) (hh : ∀ i, 0 ≤ h i)
    (hdiag : ∀ i, shiftedPairing W G i i = f i+h i)
    (hpair : ∀ i j, shiftedPairing W G i j ≤ f i+h j) :
    f (Fin.last N)+G (Sum.inr (Fin.last N)) (Sum.inr (Fin.last N))/2 ∈
      SmoothGramModel.actualLossSet N (additiveHistory W) 1 (Real.sqrt 2) := by
  apply SmoothGramModel.modelLossSet_subset_actualLossSet N _ _ _ (by norm_num)
    (Real.sqrt_nonneg 2)
  exact ⟨gramOfBlock G,fun i => f i+G (Sum.inr i) (Sum.inr i)/2,
    feasible_of_shifted_coordinates W hW G f h hG hradius hf hh hdiag hpair,rfl⟩

end GJP
