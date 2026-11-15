module
public import RealizationCore.CompatibleChain
@[expose] public section

/-!
# Canonical future-output states for realization sufficiency

The future-output vector is represented in the uniform ambient space ℝ^(N+1).
Rows below the current cut are zero. The transition discards the current first
future-output coordinate in the dimensional presentation, represented here by
gating rows below the next cut while preserving all absolute future row labels.
-/

namespace RegisterMachine

noncomputable section
open Matrix Finset BigOperators

def cv {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : ℝ) (g : Fin N → ℝ)
    (k : Fin (N+1)) : Fin (N+1) → ℝ :=
  fun i => if h : k.val ≤ i.val then
    x0 + ∑ j : Fin k.val, W i ⟨j.val, by omega⟩ * g ⟨j.val, by omega⟩ else 0

def ch {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : Fin N) : Fin (N+1) → ℝ :=
  fun i => if h : k.val < i.val then W i ⟨k.val, by omega⟩ else 0

def cdrop {N : ℕ} (k : Fin N) : (Fin (N+1) → ℝ) →ₗ[ℝ] (Fin (N+1) → ℝ) where
  toFun v i := if h : k.val+1 ≤ i.val then v i else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    by_cases h : k.val+1 ≤ i.val
    · simp [h]
    · simp [h]
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : k.val+1 ≤ i.val
    · simp [h]
    · simp [h]

lemma cv_succ {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : ℝ) (g : Fin N → ℝ)
    (k : Fin N) :
    cv W x0 g ⟨k.val+1, by omega⟩ = cdrop k (cv W x0 g ⟨k.val, by omega⟩) + g k • ch W k := by
  funext i
  by_cases hi : k.val+1 ≤ i.val
  · have hk : k.val < i.val := by omega
    have hrow : k.val ≤ i.val := by omega
    simp only [cv, cdrop, ch, hi, hk, hrow, dite_true, dite_false, ite_true,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc]
    simp [Fin.val_castSucc, Fin.val_last]
    ring
  · have hiN := i.isLt
    have hkN := k.isLt
    have hk : ¬ k.val < i.val := by omega
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hz : cdrop k (cv W x0 g ⟨k.val, by omega⟩) i = 0 := by
      change (if h : k.val+1 ≤ i.val then cv W x0 g ⟨k.val, by omega⟩ i else 0) = 0
      simp [hi]
    rw [hz]
    simp [cv, ch, hi, hk]

/-- Padded cut matrix: output rows are uniformly labeled, while its columns are
exactly `(x₀, g₀, …, g_{k-1})`. This eliminates filtering inside the input sum. -/
def cH {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : ℕ) (hk : k ≤ N) :
    Matrix (Fin (N+1)) (Fin (k+1)) ℝ :=
  fun i j => if h : k ≤ i.val then if j.val = 0 then 1 else W i ⟨j.val-1, by omega⟩ else 0

lemma cH_mulVec_eq_cv {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) :
    cH W k.val (by omega) *ᵥ inputVec N x0 g k.val (by omega) = cv W x0 g k := by
  funext i
  simp only [cH, Matrix.mulVec, dotProduct, cv]
  by_cases hi : k.val ≤ i.val
  · simp only [hi, dite_true, Fin.sum_univ_succ, inputVec_zero, inputVec_succ]
    simp [Fin.val_succ, Fin.succ_ne_zero]
  · simp [hi]

lemma cdrop_range {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (k : Fin N) (v : Fin (N+1) → ℝ)
    (hv : v ∈ (cH W k.val (by omega)).mulVecLin.range) :
    cdrop k v ∈ (cH W (k.val+1) (by omega)).mulVecLin.range := by
  obtain ⟨u, rfl⟩ := hv
  rw [Matrix.mulVecLin_apply]
  obtain ⟨x0, g, hg⟩ := inputVec_surjective N k.val (by omega) u
  rw [← hg, cH_mulVec_eq_cv W x0 g ⟨k.val, by omega⟩]
  have hp : cv W x0 (gTrunc N g k.val) ⟨k.val, by omega⟩ = cv W x0 g ⟨k.val, by omega⟩ := by
    funext i
    simp only [cv]
    split_ifs with hi
    · congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp [gTrunc, j.isLt]
    · rfl
  rw [← hp]
  have hz : gTrunc N g k.val k = 0 := by simp [gTrunc]
  have hrec := cv_succ W x0 (gTrunc N g k.val) k
  rw [hz, zero_smul, add_zero] at hrec
  rw [← hrec]
  refine ⟨inputVec N x0 (gTrunc N g k.val) (k.val+1) (by omega), ?_⟩
  rw [Matrix.mulVecLin_apply, cH_mulVec_eq_cv W x0 (gTrunc N g k.val) ⟨k.val+1, by omega⟩]


lemma ch_range {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : Fin N) :
    ch W k ∈ (cH W (k.val+1) (by omega)).mulVecLin.range := by
  refine ⟨Pi.single (Fin.last (k.val+1)) 1, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.mulVec_single, cH, Pi.single_apply, ch]
  by_cases hi : k.val < i.val
  · have hki : k.val+1 ≤ i.val := by omega
    simp [cH, ch, hi, hki, Fin.val_last]
  · have hki : ¬ k.val+1 ≤ i.val := by omega
    simp [cH, ch, hi, hki, Fin.val_last]

def cobs {N : ℕ} (k : Fin (N+1)) : (Fin (N+1) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj ⟨k.val, by omega⟩

lemma cv_obs {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : ℝ) (g : Fin N → ℝ)
    (k : Fin (N+1)) : cobs k (cv W x0 g k) = target N W x0 g k := by
  simp [cobs, cv, target]

#print axioms cH_mulVec_eq_cv
#print axioms cv_succ
#print axioms cdrop_range
#print axioms ch_range
#print axioms cv_obs

end
end RegisterMachine
