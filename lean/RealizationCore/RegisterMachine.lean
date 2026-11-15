module
public import Mathlib
public import RealizationCore.RankIdentity
public import MemoryRank.CutRank
@[expose] public section
noncomputable section

/-! Scalar register-machine semantics and the unconditional cut-rank lower bound.
The same real scalar coefficients act coordinatewise in every dimension.
The dimension-independent tensor extension is proved in the report.
-/

namespace RegisterMachine

open Matrix Finset BigOperators

structure Machine (N s : ℕ) where
  F : Fin N → Matrix (Fin s) (Fin s) ℝ
  b : Fin N → Fin s → ℝ
  c : Fin N → Fin s → ℝ
  o : Fin s → ℝ

def e1 (s : ℕ) : Fin s → ℝ := fun i => if i.val = 0 then 1 else 0

def dot {s : ℕ} (u v : Fin s → ℝ) : ℝ := ∑ i : Fin s, u i * v i

def target (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) : ℝ :=
  x0 + ∑ j : Fin k.val, W k ⟨j.val, by omega⟩ * g ⟨j.val, by omega⟩

def inputVec (N : ℕ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) (j : Fin (k+1)) : ℝ :=
  if h : j = 0 then x0 else g ⟨j.val - 1, by
    have hjv : j.val ≠ 0 := by intro heq; apply h; ext; simpa using heq
    omega
  ⟩

@[simp] lemma inputVec_zero (N : ℕ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    inputVec N x0 g k hk (0 : Fin (k+1)) = x0 := by simp [inputVec]

@[simp] lemma inputVec_succ (N : ℕ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) (j : Fin k) :
    inputVec N x0 g k hk (Fin.succ j) = g ⟨j.val, by omega⟩ := by simp [inputVec, Fin.succ_ne_zero j, Fin.val_succ]

@[simp] lemma inputVec_castSucc (N : ℕ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k + 1 ≤ N) (j : Fin (k+1)) :
    inputVec N x0 g (k+1) hk (Fin.castSucc j) = inputVec N x0 g k (by omega) j := by
  simp [inputVec, Fin.castSucc_eq_zero_iff, Fin.val_castSucc]

@[simp] lemma inputVec_last (N : ℕ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k + 1 ≤ N) :
    inputVec N x0 g (k+1) hk (Fin.last (k+1)) = g ⟨k, by omega⟩ := by
  simp [inputVec, show Fin.last (k+1) ≠ (0 : Fin (k+2)) by simp [Fin.ext_iff, Fin.val_last], Fin.val_last]

def H_k (N : ℕ) (k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Matrix (Fin (N - k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun (i : Fin (N - k + 1)) (j : Fin (k + 1)) =>
    if hj : j.val = 0 then (1 : ℝ) else W ⟨k + i.val, by omega⟩ ⟨j.val - 1, by omega⟩

def truncTargetVec (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) : Fin (N - k + 1) → ℝ :=
  fun i => x0 + ∑ j : Fin k, W ⟨k + i.val, by omega⟩ ⟨j.val, by omega⟩ * g ⟨j.val, by omega⟩

@[simp] lemma H_k_zero (N k hk W i) : H_k (N:=N) (k:=k) hk W i (0 : Fin (k+1)) = 1 := by simp [H_k]

@[simp] lemma H_k_succ (N k hk W i j) : H_k (N:=N) (k:=k) hk W i (Fin.succ j) = W ⟨k + i.val, by omega⟩ ⟨j.val, by omega⟩ := by
  simp [H_k, Fin.val_succ, Fin.succ_ne_zero j]

lemma Hk_mulVec_truncTarget (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    H_k N k hk W *ᵥ inputVec N x0 g k hk = truncTargetVec N W x0 g k hk := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  simp [H_k_zero, inputVec_zero, H_k_succ, inputVec_succ, truncTargetVec]

noncomputable def stateNat (N s : ℕ) (M : Machine N s) (x0 : ℝ) (g : Fin N → ℝ) : ℕ → (Fin s → ℝ)
  | 0 => fun i => e1 s i * x0
  | n+1 =>
    if h : n < N then
      fun i => (∑ j : Fin s, M.F ⟨n, h⟩ i j * stateNat N s M x0 g n j) + M.b ⟨n, h⟩ i * g ⟨n, h⟩
    else stateNat N s M x0 g n

noncomputable def stateFin (N s : ℕ) (M : Machine N s) (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)) : Fin s → ℝ :=
  stateNat N s M x0 g k.val

theorem stateNat_zero (N s : ℕ) (M : Machine N s) (x0 : ℝ) (g : Fin N → ℝ) : stateNat (N:=N) (s:=s) M x0 g 0 = fun i => e1 s i * x0 := by simp [stateNat]

theorem stateNat_succ (N s : ℕ) (M : Machine N s) (x0 : ℝ) (g : Fin N → ℝ) (n : ℕ) (hn : n < N) :
    stateNat (N:=N) (s:=s) M x0 g (n+1) =
      fun i => (∑ j : Fin s, M.F ⟨n, hn⟩ i j * stateNat N s M x0 g n j) + M.b ⟨n, hn⟩ i * g ⟨n, hn⟩ := by
  simp [stateNat, hn]

def Realizes (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s) : Prop :=
  0 < s ∧
  (∀ (x0 : ℝ) (g : Fin N → ℝ) (k : Fin N),
    dot (M.c k) (stateFin N s M x0 g ⟨k.val, by omega⟩) = target N W x0 g ⟨k.val, by omega⟩) ∧
  (∀ (x0 : ℝ) (g : Fin N → ℝ),
    dot M.o (stateFin N s M x0 g ⟨N, by omega⟩) = target N W x0 g ⟨N, by omega⟩) ∧
  (∀ (x0 : ℝ) (g : Fin N → ℝ),
    stateFin N s M x0 g ⟨0, by omega⟩ = fun i => e1 s i * x0)

noncomputable def psi (N s : ℕ) (M : Machine N s) : (k : ℕ) → (hk : k ≤ N) → Matrix (Fin s) (Fin (k+1)) ℝ
  | 0, _ => Matrix.of fun i _ => e1 s i
  | k+1, hk =>
    let hk' : k ≤ N := by omega
    let prev := psi N s M k hk'
    Matrix.of fun (i : Fin s) (j : Fin (k+2)) =>
      Fin.lastCases (M.b ⟨k, by omega⟩ i) (fun j' : Fin (k+1) => ∑ t : Fin s, M.F ⟨k, by omega⟩ i t * prev t j') j

@[simp] lemma psi_castSucc (N s : ℕ) (M : Machine N s) (k : ℕ) (hk : k + 1 ≤ N) (i : Fin s) (j : Fin (k+1)) :
    psi N s M (k+1) hk i (Fin.castSucc j) = ∑ t : Fin s, M.F ⟨k, by omega⟩ i t * psi N s M k (by omega) t j := by
  simp [psi, Fin.lastCases_castSucc]

@[simp] lemma psi_last (N s : ℕ) (M : Machine N s) (k : ℕ) (hk : k + 1 ≤ N) (i : Fin s) :
    psi N s M (k+1) hk i (Fin.last (k+1)) = M.b ⟨k, by omega⟩ i := by
  simp [psi, Fin.lastCases_last]

theorem psi_mulVec_state (N s : ℕ) (M : Machine N s) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    psi N s M k hk *ᵥ inputVec N x0 g k hk = stateNat N s M x0 g k := by
  induction k with
  | zero =>
    ext i
    simp [psi, inputVec, stateNat, e1, Matrix.mulVec, dotProduct]
  | succ k ih =>
    have hk' : k ≤ N := by omega
    have ih' := ih hk'
    ext i
    simp only [Matrix.mulVec, dotProduct]
    have hsplit : (∑ j : Fin (k+2), psi N s M (k+1) hk i j * inputVec N x0 g (k+1) hk j) =
      (∑ j : Fin (k+1), (∑ t : Fin s, M.F ⟨k, by omega⟩ i t * psi N s M k hk' t j) * inputVec N x0 g k hk' j)
      + M.b ⟨k, by omega⟩ i * g ⟨k, by omega⟩ := by
      calc _ = (∑ j : Fin (k+1), psi N s M (k+1) hk i (Fin.castSucc j) * inputVec N x0 g (k+1) hk (Fin.castSucc j))
              + psi N s M (k+1) hk i (Fin.last (k+1)) * inputVec N x0 g (k+1) hk (Fin.last (k+1)) := by
              rw [Fin.sum_univ_castSucc]
        _ = (∑ j : Fin (k+1), (∑ t : Fin s, M.F ⟨k, by omega⟩ i t * psi N s M k hk' t j) * inputVec N x0 g k hk' j)
              + M.b ⟨k, by omega⟩ i * g ⟨k, by omega⟩ := by
              simp only [psi_castSucc, inputVec_castSucc, psi_last, inputVec_last]
    rw [hsplit]
    have hswap : (∑ j : Fin (k+1), (∑ t : Fin s, M.F ⟨k, by omega⟩ i t * psi N s M k hk' t j) * inputVec N x0 g k hk' j)
        = ∑ t : Fin s, M.F ⟨k, by omega⟩ i t * (∑ j : Fin (k+1), psi N s M k hk' t j * inputVec N x0 g k hk' j) := by
      calc _ = ∑ j : Fin (k+1), ∑ t : Fin s, M.F ⟨k, by omega⟩ i t * psi N s M k hk' t j * inputVec N x0 g k hk' j := by
              apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
        _ = ∑ t : Fin s, ∑ j : Fin (k+1), M.F ⟨k, by omega⟩ i t * psi N s M k hk' t j * inputVec N x0 g k hk' j := by
              rw [Finset.sum_comm]
        _ = ∑ t : Fin s, M.F ⟨k, by omega⟩ i t * (∑ j : Fin (k+1), psi N s M k hk' t j * inputVec N x0 g k hk' j) := by
              apply Finset.sum_congr rfl; intro t _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hswap]
    have hfun : (fun t => ∑ j : Fin (k+1), psi N s M k hk' t j * inputVec N x0 g k hk' j) = stateNat N s M x0 g k := by
      funext t
      have : (psi N s M k hk' *ᵥ inputVec N x0 g k hk') t = stateNat N s M x0 g k t := congrFun ih' t
      simpa [Matrix.mulVec, dotProduct] using this
    have h1 : (∑ t : Fin s, M.F ⟨k, by omega⟩ i t * (∑ j : Fin (k+1), psi N s M k hk' t j * inputVec N x0 g k hk' j))
        = ∑ t : Fin s, M.F ⟨k, by omega⟩ i t * stateNat N s M x0 g k t := by
      apply Finset.sum_congr rfl; intro t _; have : (∑ j : Fin (k+1), psi N s M k hk' t j * inputVec N x0 g k hk' j) = stateNat N s M x0 g k t := by
        have h' := congrFun hfun t; simpa using h'
      rw [this]
    rw [h1]
    have hsucc := stateNat_succ N s M x0 g k (by omega)
    simp [hsucc]

noncomputable def phiAux (N s : ℕ) (M : Machine N s) : (m : ℕ) → (hm : m ≤ N) → Matrix (Fin (m+1)) (Fin s) ℝ
  | 0, _ => Matrix.of fun _ j => M.o j
  | m+1, hm =>
    have hm' : m ≤ N := by omega
    let prev := phiAux N s M m hm'
    let k : Fin N := ⟨N - (m+1), by omega⟩
    Matrix.of fun (i : Fin (m+2)) (j : Fin s) =>
      if hi : i.val = 0 then M.c k j
      else (prev * M.F k) ⟨i.val - 1, by omega⟩ j

noncomputable def phi (N s : ℕ) (M : Machine N s) (k : ℕ) (hk : k ≤ N) : Matrix (Fin (N - k + 1)) (Fin s) ℝ :=
  phiAux N s M (N - k) (by omega)

def gTrunc (N : ℕ) (g : Fin N → ℝ) (k : ℕ) : Fin N → ℝ := fun j => if j.val < k then g j else 0

-- (1) State invariance: state depends only on consumed inputs (proved via psi)
lemma state_invariant (N s : ℕ) (M : Machine N s) (x0 : ℝ) (g g' : Fin N → ℝ) (k : ℕ) (hk : k ≤ N)
    (h : ∀ j : Fin k, g ⟨j.val, by omega⟩ = g' ⟨j.val, by omega⟩) :
    stateNat N s M x0 g k = stateNat N s M x0 g' k := by
  have hInput : inputVec N x0 g k hk = inputVec N x0 g' k hk := by
    ext j
    simp only [inputVec]
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp [hj0]
      have hjv : j.val ≠ 0 := by intro heq; apply hj0; ext; simpa using heq
      have hjk : j.val - 1 < k := by omega
      have h1 := h ⟨j.val - 1, hjk⟩
      have heq : (⟨j.val - 1, by omega⟩ : Fin N) = ⟨j.val - 1, by omega⟩ := rfl
      simpa using h1
  have h1 : psi N s M k hk *ᵥ inputVec N x0 g k hk = stateNat N s M x0 g k := psi_mulVec_state N s M x0 g k hk
  have h2 : psi N s M k hk *ᵥ inputVec N x0 g' k hk = stateNat N s M x0 g' k := psi_mulVec_state N s M x0 g' k hk
  rw [hInput] at h1
  rw [h1, h2] at *

/-- With gradients zero from cut `k` onwards, the target at row `k+t`
reduces to the truncated target. -/
lemma target_gTrunc_succ (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x0 : ℝ) (g : Fin N → ℝ) (k t : ℕ) (ht : k+t < N) :
    target N W x0 (gTrunc N g k) ⟨k+t+1, by omega⟩ =
      x0 + (∑ j : Fin (k+t), W ⟨k+t+1, by omega⟩ ⟨j.val, by omega⟩ *
        gTrunc N g k ⟨j.val, by omega⟩)
      + W ⟨k+t+1, by omega⟩ ⟨k+t, by omega⟩ * gTrunc N g k ⟨k+t, by omega⟩ := by
  unfold target
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  abel

lemma target_gTrunc (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) : ∀ (t : ℕ) (ht : t ≤ N-k),
      target N W x0 (gTrunc N g k) ⟨k+t, by omega⟩ =
        x0 + ∑ j : Fin k, W ⟨k+t, by omega⟩ ⟨j.val, by omega⟩ * g ⟨j.val, by omega⟩ := by
  intro t
  induction t with
  | zero =>
    intro ht
    unfold target
    simp only [Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [gTrunc, j.isLt]
  | succ t ih =>
    intro ht
    have hlt : t ≤ N-k := by omega
    have hlk : k+t < N := by omega
    change target N W x0 (gTrunc N g k) ⟨k+t+1, by omega⟩ = _
    rw [target_gTrunc_succ N W x0 g k t hlk]
    have hzero : gTrunc N g k ⟨k+t, by omega⟩ = 0 := by simp [gTrunc]
    rw [hzero, mul_zero, add_zero]
    simp only [Fin.sum_univ_add]
    simp only [gTrunc, Fin.val_castAdd, Fin.val_natAdd]
    simp [show ∀ j : Fin k, j.val < k from fun j => j.isLt,
      Nat.not_lt.mpr (Nat.le_add_right k t), Nat.add_assoc]

lemma target_gTrunc_Fin (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) (i : Fin (N-k+1)) :
    target N W x0 (gTrunc N g k) ⟨k+i.val, by have := i.isLt; omega⟩ =
      truncTargetVec N W x0 g k hk i := by
  rw [target_gTrunc N W x0 g k hk i.val (by have := i.isLt; omega)]
  rfl

/-- Recursion step for the truncated-g state. -/
lemma stateNat_succ_gTrunc (N s : ℕ) (M : Machine N s) (x0 : ℝ) (g : Fin N → ℝ)
    (k : ℕ) (hk : k < N) :
    stateNat N s M x0 (gTrunc N g k) (k+1) =
      M.F ⟨k, hk⟩ *ᵥ stateNat N s M x0 (gTrunc N g k) k := by
  rw [stateNat_succ N s M x0 (gTrunc N g k) k hk]
  funext i
  simp [Matrix.mulVec, dotProduct, gTrunc]

/-- The observation row recursion, before applying it to the cut-state.
The vanishing-tail hypothesis is the causality condition that makes the future
state updates reduce to `F k * Z k`. -/
lemma phiAux_apply_state (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Machine N s) (hR : Realizes N s W M) (x0 : ℝ) (g : Fin N → ℝ) :
    ∀ (m : ℕ) (hm : m ≤ N), (∀ j : Fin N, N-m ≤ j.val → g j = 0) →
      (phiAux N s M m hm) *ᵥ stateNat N s M x0 g (N-m) =
      (fun i : Fin (m+1) => target N W x0 g ⟨N-m+i.val, by omega⟩) := by
  intro m
  induction m with
  | zero =>
    intro hm hzero
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    change dot M.o (stateNat N s M x0 g N) = target N W x0 g ⟨N, by omega⟩
    exact hR.2.2.1 x0 g
  | succ m ih =>
    intro hm hzero
    have hm1 : m ≤ N := by omega
    have hzeroTail : ∀ j : Fin N, N-m ≤ j.val → g j = 0 := by
      intro j hj
      exact hzero j (by omega)
    have ih' := ih hm1 hzeroTail
    have hk : N-(m+1) < N := by omega
    have hk1 : N-(m+1)+1 = N-m := by omega
    have hgk : g ⟨N-(m+1), hk⟩ = 0 := hzero ⟨N-(m+1), hk⟩ (by simp)
    have hstate : stateNat N s M x0 g (N-m) =
        M.F ⟨N-(m+1), hk⟩ *ᵥ stateNat N s M x0 g (N-(m+1)) := by
      rw [← hk1, stateNat_succ N s M x0 g (N-(m+1)) hk]
      funext q
      simp [Matrix.mulVec, dotProduct, hgk]
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · have hobs := hR.2.1 x0 g ⟨N-(m+1), hk⟩
      change dot (M.c ⟨N-(m+1), hk⟩) (stateNat N s M x0 g (N-(m+1))) =
          target N W x0 g ⟨N-(m+1), by omega⟩
      exact hobs
    · change ((phiAux N s M m hm1 * M.F ⟨N-(m+1), hk⟩) *ᵥ
        stateNat N s M x0 g (N-(m+1))) i' = _
      rw [← Matrix.mulVec_mulVec, ← hstate]
      convert congrFun ih' i' using 1 <;>
        congr 1 <;> apply Fin.ext <;> simp <;> omega

/-- The nonempty observation identity, stated at the cut rather than the auxiliary row count. -/
lemma phi_apply_truncState (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Machine N s) (hR : Realizes N s W M) (x0 : ℝ) (g : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) :
    phi N s M k hk *ᵥ stateNat N s M x0 (gTrunc N g k) k = truncTargetVec N W x0 g k hk := by
  have hzero : ∀ j : Fin N, N-(N-k) ≤ j.val → gTrunc N g k j = 0 := by
    intro j hj
    simp only [Nat.sub_sub_self hk] at hj
    simp [gTrunc, show ¬ j.val < k by omega]
  have h := phiAux_apply_state N s W M hR x0 (gTrunc N g k) (N-k) (Nat.sub_le N k) hzero
  simp only [Nat.sub_sub_self hk] at h
  change phiAux N s M (N-k) (Nat.sub_le N k) *ᵥ stateNat N s M x0 (gTrunc N g k) k = _
  rw [h]
  funext i
  exact target_gTrunc_Fin N W x0 g k hk i

lemma inputVec_gTrunc (N : ℕ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N)
    (j : Fin (k+1)) :
    inputVec N x0 g k hk j = inputVec N x0 (gTrunc N g k) k hk j := by
  unfold inputVec
  by_cases hj : j = 0
  · simp [hj]
  · simp only [hj, dite_false]
    have hjk : j.val - 1 < k := by have := j.isLt; omega
    simp [gTrunc, hjk]

lemma inputVec_surjective (N : ℕ) (k : ℕ) (hk : k ≤ N) (v : Fin (k+1) → ℝ) :
    ∃ (x0 : ℝ) (g : Fin N → ℝ), inputVec N x0 g k hk = v := by
  refine ⟨v 0, (fun j => if h : j.val < k then v ⟨j.val+1, by omega⟩ else 0), ?_⟩
  funext j
  by_cases hj : j = 0
  · simp [hj]
  · simp only [inputVec, hj, dite_false]
    have hjk : j.val - 1 < k := by have := j.isLt; omega
    simp only [hjk, dite_true]
    congr 1
    apply Fin.ext
    simp
    have hpos : 0 < j.val := by
      by_contra hn
      have hz : j.val = 0 := Nat.eq_zero_of_not_pos hn
      exact hj (Fin.ext hz)
    omega

-- (2) φ·ψ identity: H_k = Φ_k·Ψ_k from Realizes via state-invariance and gTrunc
-- Full proof by induction on m = N-k matching phiAux recursion; base m=0 uses
-- Realizes terminal readout (o), step uses Realizes observation c_k and (1).
theorem Hk_eq_phi_mul_psi (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s) (k : ℕ) (hk : k ≤ N) (hR : Realizes N s W M) :
    H_k N k hk W = phi N s M k hk * psi N s M k hk := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x0, g, rfl⟩ := inputVec_surjective N k hk v
  rw [Hk_mulVec_truncTarget N W x0 g k hk]
  rw [← Matrix.mulVec_mulVec]
  have hinput : inputVec N x0 g k hk = inputVec N x0 (gTrunc N g k) k hk :=
    funext (inputVec_gTrunc N x0 g k hk)
  rw [hinput]
  rw [psi_mulVec_state]
  exact (phi_apply_truncState N s W M hR x0 g k hk).symm

def HasRealization (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) : Prop :=
  ∃ M : Machine N s, Realizes N s W M

-- (4) Unconditional necessity: HasRealization → rank H_k ≤ s (no CutFactorization hypothesis)
theorem necessity_rank_le_unconditional (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : ℕ) (hk : k ≤ N)
    (hHas : HasRealization N W s) : (H_k N k hk W).rank ≤ s := by
  obtain ⟨M, hR⟩ := hHas
  have hEq : H_k N k hk W = phi N s M k hk * psi N s M k hk := Hk_eq_phi_mul_psi N s W M k hk hR
  calc (H_k N k hk W).rank = (phi N s M k hk * psi N s M k hk).rank := by rw [hEq]
    _ ≤ s := by
      have h1 : (phi N s M k hk * psi N s M k hk).rank ≤ (phi N s M k hk).rank := Matrix.rank_mul_le_left _ _
      have h2 : (phi N s M k hk).rank ≤ s := le_trans (Matrix.rank_le_width (phi N s M k hk)) (by simp)
      exact le_trans h1 h2

-- Derived CutFactorization as theorem, not hypothesis of main result
theorem cutFactorization_of_realizes (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s) (k : ℕ) (hk : k ≤ N) (hR : Realizes N s W M) :
    H_k N k hk W = phi N s M k hk * psi N s M k hk :=
  Hk_eq_phi_mul_psi N s W M k hk hR

#print axioms psi_mulVec_state
#print axioms Hk_mulVec_truncTarget
#print axioms necessity_rank_le_unconditional


/-- This semantic cut matrix is the same matrix used in the increment-rank identity. -/
theorem cutMatrix_eq (N k : ℕ) (hk : k ≤ N)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    H_k N k hk W = RealizationCore.H_k N k hk W := by rfl

theorem increment_rank_lower_bound (N s : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : ℕ) (hk : k ≤ N)
    (h : HasRealization N W s) :
    1 + (RealizationCore.S_k_of N k W).rank ≤ s := by
  have hr := necessity_rank_le_unconditional N s W k hk h
  rw [cutMatrix_eq, RealizationCore.rank_H_eq_one_add_rank_S] at hr
  exact hr

theorem maxCutRank_le_registers (N s : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (h : HasRealization N W s) : MemoryRank.CutRank.memRank N W ≤ s := by
  apply Finset.sup_le
  intro k _
  have hr := necessity_rank_le_unconditional N s W k.val (by omega) h
  simpa [MemoryRank.CutRank.H_k, H_k] using hr

#print axioms Hk_eq_phi_mul_psi
#print axioms increment_rank_lower_bound
#print axioms maxCutRank_le_registers
end RegisterMachine
