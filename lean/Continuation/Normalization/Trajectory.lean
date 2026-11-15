module
public import Continuation.Normalization.Core
public import RealizationCore.VectorRealization
@[expose] public section
noncomputable section
namespace RegisterMachine
open Matrix Finset
-- Helper lemmas for matrix inverses
lemma A_mat_inv_mul_A_mat {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    A_mat_inv hs h *ᵥ (A_mat hs h *ᵥ v) = v := by
  rw [A_mat_mulVec, A_mat_inv_mulVec, B_lin_A_lin]

lemma A_mat_mul_A_mat_inv {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    A_mat hs h *ᵥ (A_mat_inv hs h *ᵥ v) = v := by
  rw [A_mat_inv_mulVec, A_mat_mulVec, A_lin_B_lin]

lemma A_of_inv_mul_A_of {N s : ℕ} (M : Machine N s) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hR : Realizes N s W M) (k : Fin (N+1)) (v : Fin s → ℝ) :
    A_of_inv_mat M W hR k *ᵥ (A_of M W hR k *ᵥ v) = v := by
  unfold A_of A_of_inv_mat
  by_cases hk : k.val < N
  · simp only [hk, dite_true]
    exact A_mat_inv_mul_A_mat hR.1 (dot_c_qFin N s W M hR ⟨k.val, hk⟩) v
  · simp only [hk, dite_false]
    exact A_mat_inv_mul_A_mat hR.1 (dot_o_qFin N s W M hR) v

lemma A_of_mul_A_of_inv {N s : ℕ} (M : Machine N s) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hR : Realizes N s W M) (k : Fin (N+1)) (v : Fin s → ℝ) :
    A_of M W hR k *ᵥ (A_of_inv_mat M W hR k *ᵥ v) = v := by
  unfold A_of A_of_inv_mat
  by_cases hk : k.val < N
  · simp only [hk, dite_true]
    exact A_mat_mul_A_mat_inv hR.1 (dot_c_qFin N s W M hR ⟨k.val, hk⟩) v
  · simp only [hk, dite_false]
    exact A_mat_mul_A_mat_inv hR.1 (dot_o_qFin N s W M hR) v

-- dot e1 e1 =1 lemma for fixed A construction
lemma dot_e1_self {s : ℕ} (hs : 0 < s) : dot (e1 s) (e1 s) = 1 := by
  simp only [dot, e1]
  have h : ∀ i : Fin s, (if i.val = 0 then (1:ℝ) else 0) * (if i.val = 0 then (1:ℝ) else 0) = if i = ⟨0, hs⟩ then 1 else 0 := by
    intro i
    by_cases hi : i.val = 0
    · have he : i = ⟨0, hs⟩ := Fin.ext hi
      simp [he]
    · have hne : i ≠ ⟨0, hs⟩ := by intro he; apply hi; rw [he]
      simp [hi, hne]
  simp only [h]
  simp

def A_fixed {s : ℕ} (hs : 0 < s) : Matrix (Fin s) (Fin s) ℝ :=
  A_mat_inv hs (dot_e1_self hs)

def A_fixed_inv {s : ℕ} (hs : 0 < s) : Matrix (Fin s) (Fin s) ℝ :=
  A_mat hs (dot_e1_self hs)

lemma A_fixed_ones_eq_e1 {s : ℕ} (hs : 0 < s) : A_fixed hs *ᵥ onesVec s = e1 s := by
  unfold A_fixed
  exact A_mat_inv_ones_eq_q hs (dot_e1_self hs)

lemma A_fixed_inv_e1_eq_ones {s : ℕ} (hs : 0 < s) : A_fixed_inv hs *ᵥ e1 s = onesVec s := by
  unfold A_fixed_inv
  exact A_mat_q_eq_ones hs (dot_e1_self hs)

lemma A_fixed_inv_mul_A_fixed {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) :
    A_fixed_inv hs *ᵥ (A_fixed hs *ᵥ v) = v := by
  unfold A_fixed A_fixed_inv
  exact A_mat_mul_A_mat_inv hs (dot_e1_self hs) v

lemma A_fixed_mul_A_fixed_inv {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) :
    A_fixed hs *ᵥ (A_fixed_inv hs *ᵥ v) = v := by
  unfold A_fixed A_fixed_inv
  exact A_mat_inv_mul_A_mat hs (dot_e1_self hs) v

lemma dot_e1_A_fixed {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) :
    dot (e1 s) (A_fixed hs *ᵥ v) = dot (e1 s) v := by
  unfold A_fixed
  have h : dot (e1 s) (A_mat_inv hs (dot_e1_self hs) *ᵥ v) = dot (e1 s) v := by
    rw [A_mat_inv_mulVec]
    have h1 : dotLinear s (e1 s) (B_lin hs (dot_e1_self hs) v) = e1Linear s v := by
      have h0 : dotLinear s (e1 s) (↑((kerEquiv hs (dot_e1_self hs)).symm (projToKerE hs v)) : Fin s → ℝ) = 0 := by
        have : (↑((kerEquiv hs (dot_e1_self hs)).symm (projToKerE hs v)) : Fin s → ℝ) ∈ LinearMap.ker (dotLinear s (e1 s)) :=
          ((kerEquiv hs (dot_e1_self hs)).symm (projToKerE hs v)).property
        rwa [LinearMap.mem_ker] at this
      calc dotLinear s (e1 s) (B_lin hs (dot_e1_self hs) v)
          = dotLinear s (e1 s) ((e1Linear s v) • e1 s + ↑((kerEquiv hs (dot_e1_self hs)).symm (projToKerE hs v))) := by rw [B_lin_apply]
        _ = (e1Linear s v) • dotLinear s (e1 s) (e1 s) + dotLinear s (e1 s) (↑((kerEquiv hs (dot_e1_self hs)).symm (projToKerE hs v))) := by rw [map_add, LinearMap.map_smul]
        _ = (e1Linear s v) * 1 + 0 := by rw [dotLinear_apply_eq_dot, dot_e1_self hs, h0, smul_eq_mul]
        _ = e1Linear s v := by ring
    simp only [e1Linear, dotLinear_apply_eq_dot] at h1
    exact h1
  exact h

lemma dot_e1_A_fixed_inv {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) :
    dot (e1 s) (A_fixed_inv hs *ᵥ v) = dot (e1 s) v := by
  unfold A_fixed_inv
  exact e1_dot_A_mat hs (dot_e1_self hs) v

end RegisterMachine
noncomputable section
namespace RegisterMachine

open Matrix Finset

-- Normalized machine as separate structure with its own state starting with ones
structure NormalizedMachine (N s : ℕ) where
  F : Fin N → Matrix (Fin s) (Fin s) ℝ
  b : Fin N → Fin s → ℝ

def normalizedMachineOf {N s : ℕ} (M : Machine N s) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hR : Realizes N s W M) : NormalizedMachine N s where
  F := normF M W hR
  b := normB M W hR

noncomputable def stateNormNat {N s : ℕ} (MN : NormalizedMachine N s) (x0 : ℝ) (g : Fin N → ℝ) : ℕ → Fin s → ℝ
  | 0 => x0 • onesVec s
  | n+1 => if h : n < N then MN.F ⟨n, h⟩ *ᵥ stateNormNat MN x0 g n + g ⟨n, h⟩ • MN.b ⟨n, h⟩ else stateNormNat MN x0 g n

noncomputable def stateNormFin {N s : ℕ} (MN : NormalizedMachine N s) (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) : Fin s → ℝ :=
  stateNormNat MN x0 g k.val

lemma stateNormNat_zero {N s : ℕ} (MN : NormalizedMachine N s) (x0 : ℝ) (g : Fin N → ℝ) :
    stateNormNat MN x0 g 0 = x0 • onesVec s := by simp [stateNormNat]

lemma stateNormNat_succ {N s : ℕ} (MN : NormalizedMachine N s) (x0 : ℝ) (g : Fin N → ℝ) (n : ℕ) (hn : n < N) :
    stateNormNat MN x0 g (n+1) = MN.F ⟨n, hn⟩ *ᵥ stateNormNat MN x0 g n + g ⟨n, hn⟩ • MN.b ⟨n, hn⟩ := by
  simp [stateNormNat, hn]

def RealizesNorm {N s : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (MN : NormalizedMachine N s) : Prop :=
  0 < s ∧
  (∀ (x0 : ℝ) (g : Fin N → ℝ) (k : Fin N),
    dot (e1 s) (stateNormFin MN x0 g ⟨k.val, by omega⟩) = target N W x0 g ⟨k.val, by omega⟩) ∧
  (∀ (x0 : ℝ) (g : Fin N → ℝ),
    dot (e1 s) (stateNormFin MN x0 g ⟨N, by omega⟩) = target N W x0 g ⟨N, by omega⟩) ∧
  (∀ (x0 : ℝ) (g : Fin N → ℝ),
    stateNormFin MN x0 g ⟨0, by omega⟩ = x0 • onesVec s) ∧
  (∀ (k : Fin N), MN.F k *ᵥ onesVec s = onesVec s)

-- State induction: normalized state equals A_of * original state
-- State induction: normalized state equals A_of * original state
theorem normStateNat_eq_A_of_stateNat {N s : ℕ} (M : Machine N s) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hR : Realizes N s W M) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    stateNormNat (normalizedMachineOf M W hR) x0 g k = A_of M W hR ⟨k, by omega⟩ *ᵥ stateNat N s M x0 g k := by
  induction k with
  | zero =>
    simp only [stateNormNat]
    have hq0 : qFin N s M ⟨0, by omega⟩ = e1 s := qFin_zero_eq_e1 N s M
    have hA0 : A_of M W hR ⟨0, by omega⟩ *ᵥ e1 s = onesVec s := by
      have : qFin N s M ⟨0, by omega⟩ = e1 s := hq0
      rw [← this]
      exact A_of_q_eq_ones M W hR ⟨0, by omega⟩
    have hst0 : stateNat N s M x0 g 0 = x0 • e1 s := by
      funext i
      simp only [stateNat, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hst0]
    have h1 : A_of M W hR ⟨0, by omega⟩ *ᵥ (x0 • e1 s) = x0 • (A_of M W hR ⟨0, by omega⟩ *ᵥ e1 s) := by
      rw [Matrix.mulVec_smul]
    rw [h1, hA0]
  | succ n ih =>
    have hn : n < N := by omega
    have hn' : n ≤ N := by omega
    have ih' := ih hn'
    have hsucc : stateNat N s M x0 g (n+1) = M.F ⟨n, hn⟩ *ᵥ stateNat N s M x0 g n + (g ⟨n, hn⟩ • M.b ⟨n, hn⟩) := by
      have h1 := stateNat_succ N s M x0 g n hn
      simp only [h1]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      ring
    have hNormSucc : stateNormNat (normalizedMachineOf M W hR) x0 g (n+1) = normF M W hR ⟨n, hn⟩ *ᵥ stateNormNat (normalizedMachineOf M W hR) x0 g n + (g ⟨n, hn⟩ • normB M W hR ⟨n, hn⟩) := by
      simp only [stateNormNat, hn, normalizedMachineOf]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [hNormSucc, ih']
    have hAinv : A_of_inv_mat M W hR ⟨n, by omega⟩ *ᵥ (A_of M W hR ⟨n, by omega⟩ *ᵥ stateNat N s M x0 g n) = stateNat N s M x0 g n := by
      exact A_of_inv_mul_A_of M W hR ⟨n, by omega⟩ (stateNat N s M x0 g n)
    have hF : (A_of M W hR ⟨n+1, by omega⟩ * M.F ⟨n, hn⟩ * A_of_inv_mat M W hR ⟨n, by omega⟩) *ᵥ (A_of M W hR ⟨n, by omega⟩ *ᵥ stateNat N s M x0 g n) = A_of M W hR ⟨n+1, by omega⟩ *ᵥ (M.F ⟨n, hn⟩ *ᵥ stateNat N s M x0 g n) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAinv]
    have h1 : normF M W hR ⟨n, hn⟩ *ᵥ (A_of M W hR ⟨n, by omega⟩ *ᵥ stateNat N s M x0 g n) = A_of M W hR ⟨n+1, by omega⟩ *ᵥ (M.F ⟨n, hn⟩ *ᵥ stateNat N s M x0 g n) := by
      simp only [normF, hF]
    have h2 : (normF M W hR ⟨n, hn⟩ *ᵥ (A_of M W hR ⟨n, by omega⟩ *ᵥ stateNat N s M x0 g n) + g ⟨n, hn⟩ • normB M W hR ⟨n, hn⟩) = A_of M W hR ⟨n+1, by omega⟩ *ᵥ (M.F ⟨n, hn⟩ *ᵥ stateNat N s M x0 g n + g ⟨n, hn⟩ • M.b ⟨n, hn⟩) := by
      simp only [normB, h1, Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [h2, ← hsucc]

-- Forward direction: ordinary to normalized
theorem ordinary_to_normalized {N s : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s) (hR : Realizes N s W M) :
    RealizesNorm W (normalizedMachineOf M W hR) := by
  refine ⟨hR.1, ?_, ?_, ?_, ?_⟩
  · intro x0 g k
    have h1 : stateNormFin (normalizedMachineOf M W hR) x0 g ⟨k.val, by omega⟩ = stateNormNat (normalizedMachineOf M W hR) x0 g k.val := rfl
    have h2 : stateNormNat (normalizedMachineOf M W hR) x0 g k.val = A_of M W hR ⟨k.val, by omega⟩ *ᵥ stateNat N s M x0 g k.val := by
      exact normStateNat_eq_A_of_stateNat M W hR x0 g k.val (by omega)
    have h3 : dot (e1 s) (A_of M W hR ⟨k.val, by omega⟩ *ᵥ stateNat N s M x0 g k.val) = dot (M.c k) (stateNat N s M x0 g k.val) := by
      have h := e1_dot_A_of M W hR ⟨k.val, by omega⟩ (stateNat N s M x0 g k.val)
      simp only [dite_eq_left k.isLt] at h
      exact h
    have h4 : dot (M.c k) (stateNat N s M x0 g k.val) = target N W x0 g ⟨k.val, by omega⟩ := hR.2.1 x0 g k
    calc dot (e1 s) (stateNormFin (normalizedMachineOf M W hR) x0 g ⟨k.val, by omega⟩)
        = dot (e1 s) (stateNormNat (normalizedMachineOf M W hR) x0 g k.val) := by rw [h1]
      _ = dot (e1 s) (A_of M W hR ⟨k.val, by omega⟩ *ᵥ stateNat N s M x0 g k.val) := by rw [h2]
      _ = dot (M.c k) (stateNat N s M x0 g k.val) := h3
      _ = target N W x0 g ⟨k.val, by omega⟩ := h4
  · intro x0 g
    have h1 : stateNormFin (normalizedMachineOf M W hR) x0 g ⟨N, by omega⟩ = stateNormNat (normalizedMachineOf M W hR) x0 g N := rfl
    have h2 : stateNormNat (normalizedMachineOf M W hR) x0 g N = A_of M W hR ⟨N, by omega⟩ *ᵥ stateNat N s M x0 g N := by
      exact normStateNat_eq_A_of_stateNat M W hR x0 g N (by omega)
    have h3 : dot (e1 s) (A_of M W hR ⟨N, by omega⟩ *ᵥ stateNat N s M x0 g N) = dot M.o (stateNat N s M x0 g N) := by
      have h := e1_dot_A_of M W hR ⟨N, by omega⟩ (stateNat N s M x0 g N)
      simp only [dite_eq_right (by omega : ¬ N < N)] at h
      exact h
    have h4 : dot M.o (stateNat N s M x0 g N) = target N W x0 g ⟨N, by omega⟩ := hR.2.2.1 x0 g
    calc dot (e1 s) (stateNormFin (normalizedMachineOf M W hR) x0 g ⟨N, by omega⟩)
        = dot (e1 s) (stateNormNat (normalizedMachineOf M W hR) x0 g N) := by rw [h1]
      _ = dot (e1 s) (A_of M W hR ⟨N, by omega⟩ *ᵥ stateNat N s M x0 g N) := by rw [h2]
      _ = dot M.o (stateNat N s M x0 g N) := h3
      _ = target N W x0 g ⟨N, by omega⟩ := h4
  · intro x0 g
    simp [stateNormFin, stateNormNat]
  · intro k
    exact normF_ones M W hR k
-- Conjugation back to the ordinary e1 initialization.
theorem normalized_to_ordinary {N s : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (MN : NormalizedMachine N s) (hN : RealizesNorm W MN) :
    HasRealization N W s := by
  let A := A_fixed hN.1
  let Ainv := A_fixed_inv hN.1
  let M : Machine N s := {
    F := fun k => A * MN.F k * Ainv
    b := fun k => A *ᵥ MN.b k
    c := fun _ => e1 s
    o := e1 s }
  have hState (x0 : ℝ) (g : Fin N → ℝ) : ∀ t, t ≤ N →
      stateNat N s M x0 g t = A *ᵥ stateNormNat MN x0 g t := by
    intro t
    induction t with
    | zero =>
      intro _
      have hz : stateNat N s M x0 g 0 = x0 • e1 s := by
        ext i
        simp [stateNat, smul_eq_mul, mul_comm]
      rw [hz,stateNormNat,Matrix.mulVec_smul,A_fixed_ones_eq_e1]
    | succ n ih =>
      intro hnN
      have hn : n < N := by omega
      have hs : stateNat N s M x0 g (n+1) = M.F ⟨n,hn⟩ *ᵥ stateNat N s M x0 g n +
          g ⟨n,hn⟩ • M.b ⟨n,hn⟩ := by
        rw [stateNat_succ N s M x0 g n hn]
        ext i
        simp [Matrix.mulVec,dotProduct,mul_comm]
      rw [hs,ih (by omega),stateNormNat_succ MN x0 g n hn]
      change (A * MN.F ⟨n,hn⟩ * Ainv) *ᵥ (A *ᵥ stateNormNat MN x0 g n) +
        g ⟨n,hn⟩ • (A *ᵥ MN.b ⟨n,hn⟩) = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        A_fixed_inv_mul_A_fixed, Matrix.mulVec_add, Matrix.mulVec_smul]
  refine ⟨M,hN.1,?_,?_,?_⟩
  · intro x0 g k
    change dot (e1 s) (stateNat N s M x0 g k.val) = _
    rw [hState x0 g k.val (by omega),dot_e1_A_fixed]
    exact hN.2.1 x0 g k
  · intro x0 g
    change dot (e1 s) (stateNat N s M x0 g N) = _
    rw [hState x0 g N le_rfl,dot_e1_A_fixed]
    exact hN.2.2.1 x0 g
  · intro x0 g
    rfl

theorem realization_iff_normalized {N s : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    HasRealization N W s ↔ ∃ MN : NormalizedMachine N s, RealizesNorm W MN := by
  constructor
  · rintro ⟨M,hM⟩
    exact ⟨normalizedMachineOf M W hM,ordinary_to_normalized W M hM⟩
  · rintro ⟨MN,hMN⟩
    exact normalized_to_ordinary W MN hMN

/-- Actual vector recursion with every register initialized at x0. -/
def vectorNormStateNat {N s d : ℕ} (MN : NormalizedMachine N s)
    (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ) : ℕ → Fin s → Fin d → ℝ
  | 0 => fun _ a => x0 a
  | k+1 => if h : k < N then
      fun r a => (∑ j : Fin s, MN.F ⟨k,h⟩ r j * vectorNormStateNat MN x0 g k j a)
        + MN.b ⟨k,h⟩ r * g ⟨k,h⟩ a
    else vectorNormStateNat MN x0 g k

theorem vectorNormState_coordinate {N s d : ℕ} (MN : NormalizedMachine N s)
    (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ) (a : Fin d) (k : ℕ) :
    (fun r => vectorNormStateNat MN x0 g k r a) =
      stateNormNat MN (x0 a) (fun j => g j a) k := by
  induction k with
  | zero => ext r; simp [vectorNormStateNat,stateNormNat,onesVec]
  | succ k ih =>
    ext r
    by_cases h : k < N
    · simp only [vectorNormStateNat,stateNormNat,h,dite_true,Matrix.mulVec,dotProduct,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      have hs : (∑ j : Fin s, MN.F ⟨k,h⟩ r j * vectorNormStateNat MN x0 g k j a) =
          ∑ j : Fin s, MN.F ⟨k,h⟩ r j * stateNormNat MN (x0 a) (fun j => g j a) k j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [congrFun ih j]
      rw [hs,mul_comm (MN.b ⟨k,h⟩ r)]
    · simpa only [vectorNormStateNat,stateNormNat,h,dite_false] using congrFun ih r

theorem vectorNormReadout_coordinate {N s d : ℕ} (MN : NormalizedMachine N s)
    (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ) (a : Fin d) (k : ℕ) :
    vectorReadout (e1 s) (vectorNormStateNat MN x0 g k) a =
      dot (e1 s) (stateNormNat MN (x0 a) (fun j => g j a) k) := by
  unfold vectorReadout dot
  apply Finset.sum_congr rfl
  intro r _
  rw [congrFun (vectorNormState_coordinate MN x0 g a k) r]

/-- One normalized machine must work in all finite dimensions at every query and output. -/
def VectorRealizesNorm {N s : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (MN : NormalizedMachine N s) : Prop :=
  0 < s ∧ (∀ k, MN.F k *ᵥ onesVec s = onesVec s) ∧
    ∀ (d : ℕ) (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ) (k : Fin (N+1)),
      vectorReadout (e1 s) (vectorNormStateNat MN x0 g k.val) = vectorTarget W x0 g k

theorem normalized_readout_all {N s : ℕ} {W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ}
    {MN : NormalizedMachine N s} (hN : RealizesNorm W MN)
    (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) :
    dot (e1 s) (stateNormFin MN x0 g k) = target N W x0 g k := by
  by_cases hk : k.val < N
  · exact hN.2.1 x0 g ⟨k.val,hk⟩
  · have he : k = (⟨N,Nat.lt_succ_self N⟩ : Fin (N+1)) := by
      apply Fin.ext
      change k.val = N
      omega
    rw [he]
    exact hN.2.2.1 x0 g

theorem vectorRealizesNorm_iff_scalar {N s : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (MN : NormalizedMachine N s) :
    VectorRealizesNorm W MN ↔ RealizesNorm W MN := by
  constructor
  · intro h
    refine ⟨h.1,?_,?_,?_,h.2.1⟩
    · intro x0 g k
      have hv := congrFun (h.2.2 1 (fun _ => x0) (fun j _ => g j) ⟨k.val,by omega⟩) (0 : Fin 1)
      simpa only [vectorNormReadout_coordinate,vectorTarget,target,stateNormFin] using hv
    · intro x0 g
      have hv := congrFun (h.2.2 1 (fun _ => x0) (fun j _ => g j) ⟨N,by omega⟩) (0 : Fin 1)
      simpa only [vectorNormReadout_coordinate,vectorTarget,target,stateNormFin] using hv
    · intro x0 g
      rfl
  · intro h
    refine ⟨h.1,h.2.2.2.2,?_⟩
    intro d x0 g k
    ext a
    rw [vectorNormReadout_coordinate]
    exact normalized_readout_all h (x0 a) (fun j => g j a) k

theorem vectorRealization_iff_normalized {N s : ℕ}
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    HasVectorRealization N W s ↔ ∃ MN : NormalizedMachine N s, VectorRealizesNorm W MN := by
  rw [hasVectorRealization_iff_scalar,realization_iff_normalized]
  exact exists_congr (fun MN => (vectorRealizesNorm_iff_scalar W MN).symm)

end RegisterMachine
