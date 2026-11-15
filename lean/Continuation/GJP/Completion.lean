module
public import Continuation.GJP.Elimination

@[expose] public section
noncomputable section
open Matrix
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- The lower triangular completion used in the sufficiency proof of Lemma 3.3. -/
def triangularCompletion (d p q : n → ℝ) (r : ℝ) : Matrix n n ℝ :=
  fun i j => if i < j then 0 else if i = j then d i else q i * q j + p i * p j / r

lemma triangularCompletion_lower (d p q : n → ℝ) (r : ℝ) :
    (triangularCompletion d p q r).IsLowerTriangular := by
  intro i j hij
  simp [triangularCompletion, show i < j from hij]

lemma triangularCompletion_diag (d p q : n → ℝ) (r : ℝ) (i : n) :
    triangularCompletion d p q r i i = d i := by simp [triangularCompletion]

lemma triangularCompletion_zero_row (d p q : n → ℝ) (r : ℝ) (i : n)
    (hd : d i = 0) (hp : p i = 0) (hq : q i = 0) :
    ∀ j, triangularCompletion d p q r i j = 0 := by
  intro j
  simp [triangularCompletion, hd, hp, hq]

lemma triangularCompletion_slack (d p q : n → ℝ) (r : ℝ) :
    matrixSymm (triangularCompletion d p q r) - (1/2 : ℝ) • Matrix.vecMulVec q q -
      (1/(2*r)) • Matrix.vecMulVec p p =
      Matrix.diagonal (fun i => d i - (q i)^2/2 - (p i)^2/(2*r)) := by
  funext i j
  simp only [matrixSymm, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rcases lt_trichotomy i j with h | h | h
  · simp [triangularCompletion, h, ne_of_lt h, ne_of_gt h, not_lt_of_gt h,
      Matrix.diagonal_apply]; ring
  · subst j; simp [triangularCompletion]; ring
  · simp [triangularCompletion, h, ne_of_lt h, ne_of_gt h, not_lt_of_gt h,
      Matrix.diagonal_apply]; ring

/-- Singular triangular systems can be solved without a pseudoinverse when each zero
pivot has an identically zero row, and the target has the same zero rows. -/
theorem exists_unitLower_solution (A L : Matrix n n ℝ)
    (hA : A.IsLowerTriangular) (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i = A i i)
    (hAzero : ∀ i, A i i = 0 → ∀ j, A i j = 0)
    (hLzero : ∀ i, A i i = 0 → ∀ j, L i j = 0) :
    ∃ X : Matrix n n ℝ, UnitLower X ∧ A * X = L := by
  let z : n → ℝ := fun i => if A i i = 0 then 1 else 0
  let B := A + Matrix.diagonal z
  let K := L + Matrix.diagonal z
  have hB : B.IsLowerTriangular := hA.add (Matrix.blockTriangular_diagonal z)
  have hK : K.IsLowerTriangular := hL.add (Matrix.blockTriangular_diagonal z)
  have hBdiag : ∀ i, B i i ≠ 0 := by
    intro i
    simp only [B, Matrix.add_apply, Matrix.diagonal_apply_eq]
    by_cases h : A i i = 0 <;> simp [z, h]
  have hBunit : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (hB.det_ne_zero_iff.mpr hBdiag)
  letI : Invertible B := hBunit.invertible
  let X := B⁻¹ * K
  have hXlower : X.IsLowerTriangular :=
    (Matrix.blockTriangular_inv_of_blockTriangular hB).mul hK
  have hBX : B * X = K := by simp [X, ← Matrix.mul_assoc]
  have hXdiag : ∀ i, X i i = 1 := by
    intro i
    have hi := congrArg (fun M : Matrix n n ℝ => M i i) hBX
    rw [lower_mul_diag B X hB hXlower] at hi
    have hk : K i i = B i i := by simp [K, B, hd]
    rw [hk] at hi
    exact (mul_left_cancel₀ (hBdiag i) (hi.trans (mul_one _).symm))
  refine ⟨X, ⟨hXlower, hXdiag⟩, ?_⟩
  funext i j
  by_cases hz : A i i = 0
  · simp [Matrix.mul_apply, hAzero i hz, hLzero i hz]
  · have hBi : ∀ k, B i k = A i k := by
      intro k
      by_cases hik : i = k
      · subst k; simp [B, z, hz]
      · simp [B, Matrix.diagonal_apply, hik]
    have hKi : K i j = L i j := by
      by_cases hij : i = j
      · subst j; simp [K, z, hz]
      · simp [K, Matrix.diagonal_apply, hij]
    have hi := congrArg (fun M : Matrix n n ℝ => M i j) hBX
    simpa only [Matrix.mul_apply, hBi, hKi] using hi

/-- At a zero pivot, the diagonal inequality forces both border vectors to vanish. -/
lemma diagonal_inequality_zero (r d p q : ℝ) (hr : 0 < r) (hd : d = 0)
    (h : p^2/(2*r) ≤ d - q^2/2) : p = 0 ∧ q = 0 := by
  rw [hd] at h
  have hp : 0 ≤ p^2/(2*r) := by positivity
  have hq : 0 ≤ q^2 := sq_nonneg q
  have hp0 : p^2/(2*r) = 0 := by linarith
  have hp2 : p^2 = 0 := (div_eq_zero_iff.mp hp0).resolve_right (by positivity : (2*r : ℝ) ≠ 0)
  constructor <;> nlinarith [sq_nonneg p]

/-- Sign constraints turn a zero triangular pivot and zero column sum into a zero column. -/
lemma upper_zero_column {T : Matrix n n ℝ} (hT : T.IsUpperTriangular)
    (hsign : ∀ i j, i < j → T i j ≤ 0) (i : n)
    (hd : T i i = 0) (hp : ∑ j, T j i = 0) : ∀ j, T j i = 0 := by
  have hnonpos : ∀ j, T j i ≤ 0 := by
    intro j
    rcases lt_trichotomy j i with h | h | h
    · exact hsign j i h
    · simpa [h] using hd.le
    · rw [hT h]
  intro j
  have heach := (Finset.sum_eq_zero_iff_of_nonpos (s := Finset.univ)
    (fun k _ => hnonpos k)).mp hp
  exact heach j (Finset.mem_univ j)

/-- Sufficiency in Lemma 3.3, including singular `T`, proved by explicit triangular completion. -/
theorem equation15_exists_of_diagonal (last : n) (T C : Matrix n n ℝ) (r : ℝ)
    (hr : 0 < r) (hT : T.IsUpperTriangular) (hC : UnitLower C)
    (hsign : ∀ i j, i < j → T i j ≤ 0)
    (hdiag : ∀ i, (∑ j, T j i)^2/(2*r) ≤ T i i - (C⁻¹ last i)^2/2) :
    ∃ W : Matrix n n ℝ, UnitLower W ∧ (equation15Matrix last W T C r).PosSemidef := by
  let p : n → ℝ := fun i => ∑ j, T j i
  let q : n → ℝ := fun i => C⁻¹ last i
  let L := triangularCompletion (fun i => T i i) p q r
  have hzero : ∀ i, T i i = 0 → p i = 0 ∧ q i = 0 := by
    intro i hi
    exact diagonal_inequality_zero r (T i i) (p i) (q i) hr hi (hdiag i)
  obtain ⟨X, hX, hTX⟩ := exists_unitLower_solution Tᵀ L hT.transpose
    (triangularCompletion_lower _ _ _ _) (fun i => triangularCompletion_diag _ _ _ _ i)
    (fun i hi j => upper_zero_column hT hsign i hi (hzero i hi).1 j)
    (fun i hi => triangularCompletion_zero_row _ _ _ _ i hi (hzero i hi).1 (hzero i hi).2)
  refine ⟨X * C, hX.mul hC, ?_⟩
  apply (equation15_reduced_iff last (X*C) T C r hr hC.isUnit).mpr
  letI : Invertible C := hC.isUnit.invertible
  have htrans : Tᵀ * (X*C) * C⁻¹ = L := by
    simpa [Matrix.mul_assoc] using hTX
  have hp : Tᵀ *ᵥ (fun _ => (1 : ℝ)) = p := (colSum_eq T).symm
  have hq : C⁻¹ᵀ *ᵥ Pi.single last (1 : ℝ) = q := by
    funext i
    simp [q, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [reducedSlack, htrans, hp, hq]
  change (matrixSymm (triangularCompletion _ p q r) - _ - _).PosSemidef
  rw [triangularCompletion_slack]
  apply Matrix.PosSemidef.diagonal
  intro i
  have h := hdiag i
  change 0 ≤ T i i - q i^2/2 - p i^2/(2*r)
  dsimp [p, q]
  linarith

/-- Full Lemma 3.3 elimination equivalence for all admissible triangular factors. -/
theorem equation15_exists_iff_diagonal (last : n) (T C : Matrix n n ℝ) (r : ℝ)
    (hr : 0 < r) (hT : T.IsUpperTriangular) (hC : UnitLower C)
    (hsign : ∀ i j, i < j → T i j ≤ 0) :
    (∃ W : Matrix n n ℝ, UnitLower W ∧ (equation15Matrix last W T C r).PosSemidef) ↔
      ∀ i, (∑ j, T j i)^2/(2*r) ≤ T i i - (C⁻¹ last i)^2/2 := by
  constructor
  · rintro ⟨W, hW, hPSD⟩
    exact equation15_diagonal_necessary last r hr hW hT hC hPSD
  · exact equation15_exists_of_diagonal last T C r hr hT hC hsign

end GJP
