module
public import Benchmarks.Smooth
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace GJP

def rOGM (N : ℕ) : ℝ := 1 / (SmoothBenchmark.theta N N ^ 2)

def S (N : ℕ) (δ : Fin (N+1) → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (N+1), if i.val ≤ k then δ i else 0

def partialSum (N : ℕ) (δ : Fin (N+1) → ℝ) (i : Fin (N+1)) : ℝ :=
  S N δ i.val

def phiTerm (N : ℕ) (δ : Fin (N+1) → ℝ) (i : Fin (N+1)) : ℝ :=
  if i.val < N then (δ i) ^ 2 / (2 * partialSum N δ i) else (δ i) ^ 2

def Phi (N : ℕ) (δ : Fin (N+1) → ℝ) : ℝ :=
  Finset.sup' Finset.univ ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun i => phiTerm N δ i)

def DeltaProp (N : ℕ) (δ : Fin (N+1) → ℝ) : Prop :=
  (∀ i, 0 ≤ δ i) ∧ ∑ i : Fin (N+1), δ i = 1

def deltaStar (N : ℕ) : Fin (N+1) → ℝ :=
  fun i => if i.val < N then 2 * rOGM N * SmoothBenchmark.theta N i.val else Real.sqrt (rOGM N)

lemma rOGM_pos (N : ℕ) : 0 < rOGM N := by
  unfold rOGM
  have hθ : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
  positivity

lemma rOGM_nonneg (N : ℕ) : 0 ≤ rOGM N := le_of_lt (rOGM_pos N)

lemma theta_sq_standard (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    SmoothBenchmark.theta N k ^ 2 = SmoothBenchmark.theta N k + SmoothBenchmark.theta N (k-1) ^ 2 := by
  have hrec := SmoothBenchmark.theta_recurrence_standard N k hk hkN
  have hsq : Real.sqrt (1 + 4 * SmoothBenchmark.theta N (k-1) ^ 2) ^ 2 = 1 + 4 * SmoothBenchmark.theta N (k-1) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have h1 : (2 * SmoothBenchmark.theta N k - 1) ^ 2 = 1 + 4 * SmoothBenchmark.theta N (k-1) ^ 2 := by
    have : 2 * SmoothBenchmark.theta N k - 1 = Real.sqrt (1 + 4 * SmoothBenchmark.theta N (k-1) ^ 2) := by
      rw [hrec]; ring
    rw [this, hsq]
  nlinarith

lemma theta_sq_final (N : ℕ) (hN : 1 ≤ N) :
    SmoothBenchmark.theta N N ^ 2 = SmoothBenchmark.theta N N + 2 * SmoothBenchmark.theta N (N-1) ^ 2 := by
  have hrec := SmoothBenchmark.theta_recurrence_final N hN
  have hsq : Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) ^ 2 = 1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have h1 : (2 * SmoothBenchmark.theta N N - 1) ^ 2 = 1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2 := by
    have : 2 * SmoothBenchmark.theta N N - 1 = Real.sqrt (1 + 8 * SmoothBenchmark.theta N (N-1) ^ 2) := by
      rw [hrec]; ring
    rw [this, hsq]
  nlinarith

lemma S_zero_eq (N : ℕ) (δ : Fin (N+1) → ℝ) : S N δ 0 = δ ⟨0, Nat.zero_lt_succ _⟩ := by
  unfold S
  let a : Fin (N+1) := ⟨0, Nat.zero_lt_succ _⟩
  have hsum : (∑ i : Fin (N+1), if i.val ≤ (0:ℕ) then δ i else (0:ℝ)) = (if a.val ≤ 0 then δ a else 0) := by
    apply Fintype.sum_eq_single (a := a)
    intro x hx
    have hval : x.val ≠ 0 := fun hv => hx (Fin.ext (by simp [a, hv]))
    have : ¬ (x.val ≤ 0) := by omega
    simp [this]
  have h0 : a.val ≤ 0 := by simp [a]
  have hfa : (if a.val ≤ 0 then δ a else (0:ℝ)) = δ a := by simp [h0]
  rw [hfa] at hsum
  exact hsum

lemma S_succ_eq (N : ℕ) (δ : Fin (N+1) → ℝ) (k : ℕ) (hk : k+1 ≤ N) :
    S N δ (k+1) = S N δ k + δ ⟨k+1, by omega⟩ := by
  unfold S
  have h_eq : ∀ i : Fin (N+1), (if i.val ≤ k+1 then δ i else (0:ℝ)) = (if i.val ≤ k then δ i else 0) + (if i.val = k+1 then δ i else 0) := by
    intro i
    by_cases h1 : i.val ≤ k
    · have h2 : i.val ≤ k+1 := by omega
      have h3 : i.val ≠ k+1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i.val = k+1
      · simp [h1, h2]
      · have h3 : ¬ (i.val ≤ k+1) := by omega
        simp [h1, h3, h2]
  simp_rw [h_eq]
  rw [Finset.sum_add_distrib]
  congr 1
  let a : Fin (N+1) := ⟨k+1, by omega⟩
  have h_eq2 : ∀ i : Fin (N+1), (if i.val = k+1 then δ i else (0:ℝ)) = (if i = a then δ i else 0) := by
    intro i
    by_cases hi : i = a
    · subst hi
      simp [a]
    · have hval : i.val ≠ k+1 := fun hv => hi (Fin.ext (by simp [a, hv]))
      simp [hi, hval]
  simp_rw [h_eq2]
  have hsum : (∑ i : Fin (N+1), if i = a then δ i else (0:ℝ)) = δ a := by
    have h := Fintype.sum_eq_single (a := a) (f := fun i => if i = a then δ i else (0:ℝ)) (by intro x hx; simp [hx])
    have hfa : (fun i => if i = a then δ i else (0:ℝ)) a = δ a := by simp
    calc (∑ i : Fin (N+1), if i = a then δ i else (0:ℝ)) = (if a = a then δ a else (0:ℝ)) := h
      _ = δ a := hfa
  exact hsum

lemma S_eq_total (N : ℕ) (δ : Fin (N+1) → ℝ) (k : ℕ) (hk : N ≤ k) : S N δ k = ∑ i : Fin (N+1), δ i := by
  unfold S
  have : ∀ i : Fin (N+1), (if i.val ≤ k then δ i else (0 : ℝ)) = δ i := by
    intro i
    have : i.val ≤ k := by omega
    simp [this]
  simp_rw [this]

lemma deltaStar_S_eq (N : ℕ) (k : ℕ) (hk : k < N) : S N (deltaStar N) k = 2 * rOGM N * (SmoothBenchmark.theta N k ^ 2) := by
  induction k with
  | zero =>
    have h0 : S N (deltaStar N) 0 = deltaStar N ⟨0, Nat.zero_lt_succ _⟩ := S_zero_eq N (deltaStar N)
    have hds : deltaStar N ⟨0, Nat.zero_lt_succ _⟩ = 2 * rOGM N * SmoothBenchmark.theta N 0 := by
      unfold deltaStar
      have hlt : (⟨0, Nat.zero_lt_succ _⟩ : Fin (N+1)).val < N := by omega
      simp [hlt]
    rw [h0, hds]
    have hθ0 : SmoothBenchmark.theta N 0 = 1 := SmoothBenchmark.theta_zero N
    rw [hθ0]
    ring
  | succ k ih =>
    have hkN : k < N := by omega
    have hkn : k+1 ≤ N := by omega
    have hS_eq := S_succ_eq N (deltaStar N) k hkn
    rw [hS_eq]
    have ih' := ih hkN
    have hds : deltaStar N ⟨k+1, by omega⟩ = 2 * rOGM N * SmoothBenchmark.theta N (k+1) := by
      unfold deltaStar
      have hlt : (⟨k+1, by omega⟩ : Fin (N+1)).val < N := by omega
      simp [hlt]
    rw [hds, ih']
    have hsq := theta_sq_standard N (k+1) (by omega) hk
    have : SmoothBenchmark.theta N ((k+1)-1) = SmoothBenchmark.theta N k := by
      have : (k+1)-1 = k := by omega
      rw [this]
    rw [this] at hsq
    calc 2 * rOGM N * SmoothBenchmark.theta N k ^ 2 + 2 * rOGM N * SmoothBenchmark.theta N (k+1)
        = 2 * rOGM N * (SmoothBenchmark.theta N k ^ 2 + SmoothBenchmark.theta N (k+1)) := by ring
      _ = 2 * rOGM N * (SmoothBenchmark.theta N (k+1) + SmoothBenchmark.theta N k ^ 2) := by ring
      _ = 2 * rOGM N * (SmoothBenchmark.theta N (k+1) ^ 2) := by rw [hsq]
      _ = 2 * rOGM N * SmoothBenchmark.theta N (k+1) ^ 2 := by ring

lemma deltaStar_total (N : ℕ) (hN : 1 ≤ N) : S N (deltaStar N) N = 1 := by
  have hS_N1 : S N (deltaStar N) (N-1) = 2 * rOGM N * (SmoothBenchmark.theta N (N-1) ^ 2) := deltaStar_S_eq N (N-1) (by omega)
  have hsucc : S N (deltaStar N) N = S N (deltaStar N) (N-1) + deltaStar N ⟨N, Nat.lt_succ_self N⟩ := by
    have hk : (N-1) + 1 ≤ N := by omega
    have h1 : S N (deltaStar N) ((N-1)+1) = S N (deltaStar N) (N-1) + deltaStar N ⟨(N-1)+1, by omega⟩ := S_succ_eq N (deltaStar N) (N-1) hk
    have hN_eq : (N-1)+1 = N := Nat.sub_add_cancel hN
    have hS_eq : S N (deltaStar N) ((N-1)+1) = S N (deltaStar N) N := by rw [hN_eq]
    have hFin : deltaStar N ⟨(N-1)+1, by omega⟩ = deltaStar N ⟨N, Nat.lt_succ_self N⟩ := by
      have hval : (⟨(N-1)+1, by omega⟩ : Fin (N+1)).val = (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)).val := by omega
      unfold deltaStar
      rw [hval]
    rw [hS_eq] at h1
    rw [hFin] at h1
    exact h1
  rw [hsucc, hS_N1]
  have hdsN : deltaStar N ⟨N, Nat.lt_succ_self N⟩ = Real.sqrt (rOGM N) := by
    unfold deltaStar
    have h1 : (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)).val = N := rfl
    have h2 : ¬ (N < N) := by simp
    simp [h1, h2]
  rw [hdsN]
  have hsqrt : Real.sqrt (rOGM N) = 1 / SmoothBenchmark.theta N N := by
    unfold rOGM
    have hθ_pos : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
    have hθ_nn : 0 ≤ SmoothBenchmark.theta N N := le_of_lt hθ_pos
    have h1 : Real.sqrt (1 / (SmoothBenchmark.theta N N ^ 2)) = Real.sqrt 1 / Real.sqrt (SmoothBenchmark.theta N N ^ 2) := by
      rw [Real.sqrt_div (by positivity)]
    have h2 : Real.sqrt (1 : ℝ) = 1 := by simp
    have h3 : Real.sqrt (SmoothBenchmark.theta N N ^ 2) = SmoothBenchmark.theta N N := Real.sqrt_sq hθ_nn
    rw [h1, h2, h3]
  rw [hsqrt]
  unfold rOGM
  have hθ_pos : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
  have hθ_ne : SmoothBenchmark.theta N N ≠ 0 := ne_of_gt hθ_pos
  have hsq_final := theta_sq_final N hN
  field_simp
  nlinarith [hsq_final]

lemma quadratic_le (w a : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (h : w^2 - w - a ≤ 0) : w ≤ (1 + Real.sqrt (1 + 4*a))/2 := by
  have h1 : (2*w -1)^2 ≤ 1 + 4*a := by nlinarith
  have h2 : 0 ≤ 1 + 4*a := by positivity
  have h3 : Real.sqrt (1 + 4*a) ^2 = 1 + 4*a := Real.sq_sqrt h2
  have h4 : (2*w -1)^2 ≤ (Real.sqrt (1 + 4*a))^2 := by rw [h3]; exact h1
  have h5 : 0 ≤ Real.sqrt (1 + 4*a) := Real.sqrt_nonneg _
  by_cases hle : 2*w -1 ≤ 0
  · have : 2*w -1 ≤ Real.sqrt (1 + 4*a) := by linarith
    linarith
  · have h6 : 0 ≤ 2*w -1 := by linarith
    have h7 : (2*w -1) ≤ Real.sqrt (1 + 4*a) := by
      have h8 : Real.sqrt ((2*w -1)^2) ≤ Real.sqrt (1 + 4*a) := Real.sqrt_le_sqrt h1
      have h9 : Real.sqrt ((2*w -1)^2) = 2*w -1 := Real.sqrt_sq h6
      rw [h9] at h8
      exact h8
    linarith

lemma sqrt_two_mul_eq (m S : ℝ) (hm : 0 < m) (hS : 0 ≤ S) : Real.sqrt (2*m*S) = 2*m * Real.sqrt (S / (2*m)) := by
  have hm2 : 0 < 2*m := by positivity
  have hm2_nn : 0 ≤ 2*m := le_of_lt hm2
  have h1 : 2*m*S = (2*m)^2 * (S / (2*m)) := by field_simp
  rw [h1, Real.sqrt_mul (by positivity : 0 ≤ (2*m)^2), Real.sqrt_sq hm2_nn]

theorem deltaStar_mem_Delta (N : ℕ) : DeltaProp N (deltaStar N) := by
  constructor
  · intro i
    unfold deltaStar
    split
    · have hθ : 0 ≤ SmoothBenchmark.theta N i.val := le_of_lt (SmoothBenchmark.theta_pos N i.val (by omega))
      have hr : 0 ≤ rOGM N := rOGM_nonneg N
      positivity
    · exact Real.sqrt_nonneg _
  · by_cases hN : N = 0
    · subst hN
      have hsum : ∑ i : Fin 1, deltaStar 0 i = deltaStar 0 (⟨0, Nat.zero_lt_succ _⟩ : Fin 1) := by
        apply Fintype.sum_eq_single (a := ⟨0, Nat.zero_lt_succ _⟩)
        intro x hx; exfalso; apply hx; ext; omega
      rw [hsum]
      unfold deltaStar rOGM
      have hθ0 : SmoothBenchmark.theta 0 0 = 1 := SmoothBenchmark.theta_zero 0
      simp only [hθ0, show ¬ ((⟨0, Nat.zero_lt_succ _⟩ : Fin 1).val < (0:ℕ)) from by omega, ↓reduceIte]
      have : Real.sqrt (1 / (1 : ℝ) ^ 2) = 1 := by simp
      simp [this]
    · have hN1 : 1 ≤ N := by omega
      have hS : S N (deltaStar N) N = 1 := deltaStar_total N hN1
      have hEq : S N (deltaStar N) N = ∑ i : Fin (N+1), deltaStar N i := S_eq_total N (deltaStar N) N (by omega)
      rw [hEq] at hS
      exact hS

theorem phiTerm_tied (N : ℕ) (i : Fin (N+1)) : phiTerm N (deltaStar N) i = rOGM N := by
  unfold phiTerm partialSum
  by_cases h : i.val < N
  · simp only [h, ↓reduceIte]
    have hS : S N (deltaStar N) i.val = 2 * rOGM N * (SmoothBenchmark.theta N i.val ^ 2) := deltaStar_S_eq N i.val h
    have hθ_pos : 0 < SmoothBenchmark.theta N i.val := SmoothBenchmark.theta_pos N i.val (by omega)
    have hr_pos : 0 < rOGM N := rOGM_pos N
    have h1 : (2 * rOGM N * SmoothBenchmark.theta N i.val) ^ 2 / (2 * (2 * rOGM N * (SmoothBenchmark.theta N i.val ^ 2))) = rOGM N := by
      have hθ_ne : SmoothBenchmark.theta N i.val ≠ 0 := ne_of_gt hθ_pos
      have hr_ne : rOGM N ≠ 0 := ne_of_gt hr_pos
      field_simp
    have hds : deltaStar N i = 2 * rOGM N * SmoothBenchmark.theta N i.val := by
      unfold deltaStar; simp [h]
    calc (deltaStar N i) ^ 2 / (2 * S N (deltaStar N) i.val) = (2 * rOGM N * SmoothBenchmark.theta N i.val) ^ 2 / (2 * (2 * rOGM N * (SmoothBenchmark.theta N i.val ^ 2))) := by
          rw [hds, hS]
      _ = rOGM N := h1
  · simp only [h, ↓reduceIte]
    have hN : i.val = N := by omega
    have hds : deltaStar N i = Real.sqrt (rOGM N) := by
      unfold deltaStar; simp [h, hN]
    rw [hds, Real.sq_sqrt (rOGM_nonneg N)]

theorem deltaStar_Phi_eq (N : ℕ) : Phi N (deltaStar N) = rOGM N := by
  unfold Phi
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin (N+1))), phiTerm N (deltaStar N) i ≤ rOGM N := by
    intro i _; rw [phiTerm_tied N i]
  have hge : rOGM N ≤ Finset.sup' Finset.univ ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun i => phiTerm N (deltaStar N) i) := by
    have hmem : (⟨0, by omega⟩ : Fin (N+1)) ∈ Finset.univ := Finset.mem_univ _
    have hle2 := Finset.le_sup' (s := Finset.univ) (f := fun i => phiTerm N (deltaStar N) i) hmem
    rw [phiTerm_tied N ⟨0, by omega⟩] at hle2
    exact hle2
  apply le_antisymm
  · apply Finset.sup'_le _ _; intro i hi; rw [phiTerm_tied N i]
  · exact hge

-- Helper: S is nonnegative
lemma S_nonneg (N : ℕ) (δ : Fin (N+1) → ℝ) (hδ : ∀ i, 0 ≤ δ i) (k : ℕ) : 0 ≤ S N δ k := by
  unfold S
  apply Finset.sum_nonneg
  intro i _
  split
  · exact hδ i
  · linarith

lemma S_mono (N : ℕ) (δ : Fin (N+1) → ℝ) (hδ : ∀ i, 0 ≤ δ i) {a b : ℕ} (hab : a ≤ b) : S N δ a ≤ S N δ b := by
  unfold S
  apply Finset.sum_le_sum
  intro i _
  by_cases h1 : i.val ≤ a
  · have h2 : i.val ≤ b := by omega
    simp [h1, h2]
  · by_cases h2 : i.val ≤ b
    · simp [h1, h2]
      exact hδ i
    · simp [h1, h2]

lemma S_le_S_succ (N : ℕ) (δ : Fin (N+1) → ℝ) (hδ : ∀ i, 0 ≤ δ i) (k : ℕ) (hk : k+1 ≤ N) : S N δ k ≤ S N δ (k+1) := by
  have h := S_succ_eq N δ k hk
  have hδk : 0 ≤ δ ⟨k+1, by omega⟩ := hδ _
  linarith

-- δ_i ≤ S_i when i ≤ k
lemma delta_le_S (N : ℕ) (δ : Fin (N+1) → ℝ) (hδ : ∀ i, 0 ≤ δ i) (i : Fin (N+1)) (k : ℕ) (hik : i.val ≤ k) : δ i ≤ S N δ k := by
  unfold S
  have h : 0 ≤ S N δ k := S_nonneg N δ hδ k
  have h1 : δ i = (if i.val ≤ k then δ i else (0:ℝ)) := by simp [hik]
  have h2 : (if i.val ≤ k then δ i else (0:ℝ)) ≤ ∑ j : Fin (N+1), if j.val ≤ k then δ j else 0 := by
    apply Finset.single_le_sum (a := i)
    · intro j _
      split
      · exact hδ j
      · linarith
    · exact Finset.mem_univ i
  linarith

-- If S_k = 0 then δ_i = 0 for i ≤ k
lemma delta_eq_zero_of_S_eq_zero (N : ℕ) (δ : Fin (N+1) → ℝ) (hδ : ∀ i, 0 ≤ δ i) (k : ℕ) (hk : S N δ k = 0) (i : Fin (N+1)) (hik : i.val ≤ k) : δ i = 0 := by
  unfold S at hk
  have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin (N+1))), 0 ≤ (if j.val ≤ k then δ j else (0:ℝ)) := by
    intro j _
    split
    · exact hδ j
    · linarith
  have h_sum_zero : ∑ j : Fin (N+1), (if j.val ≤ k then δ j else (0:ℝ)) = 0 := hk
  have h_eq_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_zero
  have hm : i ∈ Finset.univ := Finset.mem_univ _
  have hj := h_eq_zero i hm
  simp [hik] at hj
  exact hj

-- Core inequality: δ_i^2 ≤ 2 Φ S_i
lemma delta_sq_le (N : ℕ) (δ : Fin (N+1) → ℝ) (hΔ : DeltaProp N δ) (m : ℝ) (hm : m = Phi N δ) (i : Fin (N+1)) (hi : i.val < N) : (δ i) ^ 2 ≤ 2 * m * S N δ i.val := by
  have hδ : ∀ j, 0 ≤ δ j := hΔ.1
  have h_phi_le : phiTerm N δ i ≤ m := by
    rw [hm]
    apply Finset.le_sup' _ (Finset.mem_univ i)
  unfold phiTerm partialSum at h_phi_le
  simp only [hi, ↓reduceIte] at h_phi_le
  by_cases hS : S N δ i.val = 0
  · have hδ0 : δ i = 0 := delta_eq_zero_of_S_eq_zero N δ hδ i.val hS i le_rfl
    simp [hδ0, hS]
  · have hS_pos : 0 < S N δ i.val := by
      have hS_nn : 0 ≤ S N δ i.val := S_nonneg N δ hδ i.val
      exact lt_of_le_of_ne hS_nn (Ne.symm hS)
    have h_den_pos : 0 < 2 * S N δ i.val := by positivity
    have h1 : (δ i) ^ 2 / (2 * S N δ i.val) ≤ m := h_phi_le
    have h2 : (δ i) ^ 2 ≤ m * (2 * S N δ i.val) := by
      rw [div_le_iff₀ h_den_pos] at h1
      linarith
    have : m * (2 * S N δ i.val) = 2 * m * S N δ i.val := by ring
    rw [this] at h2
    exact h2

lemma delta_le_sqrt (N : ℕ) (δ : Fin (N+1) → ℝ) (hΔ : DeltaProp N δ) (m : ℝ) (hm : m = Phi N δ) (i : Fin (N+1)) (hi : i.val < N) : δ i ≤ Real.sqrt (2 * m * S N δ i.val) := by
  have hsq := delta_sq_le N δ hΔ m hm i hi
  have hδ : 0 ≤ δ i := hΔ.1 i
  exact Real.le_sqrt_of_sq_le hsq

-- S bound induction
lemma S_le_bound (N : ℕ) (δ : Fin (N+1) → ℝ) (hΔ : DeltaProp N δ) (m : ℝ) (hm : m = Phi N δ) (hmpos : 0 < m) (k : ℕ) (hk : k < N) : S N δ k ≤ 2 * m * (SmoothBenchmark.theta N k ^ 2) := by
  induction k with
  | zero =>
    have hS0 : S N δ 0 = δ ⟨0, Nat.zero_lt_succ _⟩ := S_zero_eq N δ
    have hle : (δ ⟨0, Nat.zero_lt_succ _⟩) ^ 2 ≤ 2 * m * S N δ 0 := delta_sq_le N δ hΔ m hm ⟨0, Nat.zero_lt_succ _⟩ (by omega)
    by_cases hS0_zero : S N δ 0 = 0
    · rw [hS0_zero]; positivity
    · have hS0_pos : 0 < S N δ 0 := by
        have hS0_nn : 0 ≤ S N δ 0 := S_nonneg N δ hΔ.1 0
        exact lt_of_le_of_ne hS0_nn (Ne.symm hS0_zero)
      have h1 : (S N δ 0)^2 ≤ 2 * m * S N δ 0 := by
        calc (S N δ 0)^2 = (δ ⟨0, Nat.zero_lt_succ _⟩)^2 := by rw [hS0]
          _ ≤ 2 * m * S N δ 0 := hle
      have h2 : S N δ 0 ≤ 2 * m := by
        have hm2 : 0 < 2 * m := by positivity
        nlinarith
      have hθ0 : SmoothBenchmark.theta N 0 = 1 := SmoothBenchmark.theta_zero N
      rw [hθ0]
      simp
      linarith
  | succ k ih =>
    have hkN : k < N := by omega
    have hkn : k+1 ≤ N := by omega
    have ih' := ih hkN
    have hS_eq := S_succ_eq N δ k hkn
    have hk_lt : k+1 < N := by omega
    have h_delta_le : δ ⟨k+1, by omega⟩ ≤ Real.sqrt (2 * m * S N δ (k+1)) := delta_le_sqrt N δ hΔ m hm ⟨k+1, by omega⟩ hk_lt
    have hS_k_le : S N δ k ≤ 2 * m * (SmoothBenchmark.theta N k ^2) := ih'
    have h1 : S N δ (k+1) ≤ 2 * m * (SmoothBenchmark.theta N k ^2) + Real.sqrt (2 * m * S N δ (k+1)) := by
      calc S N δ (k+1) = S N δ k + δ ⟨k+1, by omega⟩ := hS_eq
        _ ≤ 2 * m * (SmoothBenchmark.theta N k ^2) + Real.sqrt (2 * m * S N δ (k+1)) := by linarith
    by_cases hS_zero : S N δ (k+1) = 0
    · rw [hS_zero]; positivity
    · have hS_pos : 0 < S N δ (k+1) := by
        have hS_nn : 0 ≤ S N δ (k+1) := S_nonneg N δ hΔ.1 (k+1)
        exact lt_of_le_of_ne hS_nn (Ne.symm hS_zero)
      have hm2_pos : 0 < 2 * m := by positivity
      let w := Real.sqrt (S N δ (k+1) / (2 * m))
      have hw_nn : 0 ≤ w := Real.sqrt_nonneg _
      have hw_sq : w ^2 = S N δ (k+1) / (2 * m) := Real.sq_sqrt (by positivity)
      have h_ineq : w^2 - w - SmoothBenchmark.theta N k ^2 ≤ 0 := by
        have h1' : S N δ (k+1) - 2 * m * (SmoothBenchmark.theta N k ^2) ≤ Real.sqrt (2 * m * S N δ (k+1)) := by linarith
        have h2 : Real.sqrt (2 * m * S N δ (k+1)) = 2 * m * w := by
          have h_eq : Real.sqrt (2 * m * S N δ (k+1)) = 2 * m * Real.sqrt (S N δ (k+1) / (2 * m)) := by
            have h1 : 2 * m * S N δ (k+1) = (2 * m)^2 * (S N δ (k+1) / (2 * m)) := by field_simp
            rw [h1, Real.sqrt_mul (by positivity : 0 ≤ (2 * m)^2), Real.sqrt_sq (le_of_lt hm2_pos)]
          rw [h_eq]
        rw [h2] at h1'
        have h3 : S N δ (k+1) = 2 * m * w^2 := by
          calc S N δ (k+1) = 2 * m * (S N δ (k+1) / (2 * m)) := by field_simp
            _ = 2 * m * w^2 := by rw [hw_sq]
        nlinarith
      have ha_nn : 0 ≤ SmoothBenchmark.theta N k ^2 := by positivity
      have hw_le : w ≤ (1 + Real.sqrt (1 + 4*(SmoothBenchmark.theta N k ^2)))/2 := quadratic_le w _ hw_nn ha_nn h_ineq
      have hθ_eq : SmoothBenchmark.theta N (k+1) = (1 + Real.sqrt (1 + 4 * SmoothBenchmark.theta N k ^2))/2 := by
        have hrec := SmoothBenchmark.theta_recurrence_standard N (k+1) (by omega) hk_lt
        have h1 : SmoothBenchmark.theta N ((k+1)-1) = SmoothBenchmark.theta N k := by
          have : (k+1)-1 = k := by omega
          rw [this]
        rw [h1] at hrec
        exact hrec
      have hw_le2 : w ≤ SmoothBenchmark.theta N (k+1) := by rw [←hθ_eq] at hw_le; exact hw_le
      have hw2_le : w^2 ≤ SmoothBenchmark.theta N (k+1) ^2 := by nlinarith [hw_nn, hw_le2, show 0 ≤ SmoothBenchmark.theta N (k+1) from le_of_lt (SmoothBenchmark.theta_pos N (k+1) (by omega))]
      have hS_eq2 : S N δ (k+1) = 2 * m * w^2 := by
        calc S N δ (k+1) = 2 * m * (S N δ (k+1) / (2 * m)) := by field_simp
          _ = 2 * m * w^2 := by rw [hw_sq]
      calc S N δ (k+1) = 2 * m * w^2 := hS_eq2
        _ ≤ 2 * m * (SmoothBenchmark.theta N (k+1) ^2) := by nlinarith
theorem rOGM_leq_Phi (N : ℕ) (δ : Fin (N+1) → ℝ) (hΔ : DeltaProp N δ) : rOGM N ≤ Phi N δ := by
  by_cases hN0 : N = 0
  · subst hN0
    have h_sum : ∑ i : Fin 1, δ i = 1 := hΔ.2
    have h0 : δ ⟨0, Nat.zero_lt_succ _⟩ = 1 := by
      have h1 : ∑ i : Fin 1, δ i = δ ⟨0, Nat.zero_lt_succ _⟩ := by
        apply Fintype.sum_eq_single (a := ⟨0, Nat.zero_lt_succ _⟩) (f := δ)
        intro x hx
        exfalso; apply hx; ext; omega
      linarith
    have hPhi : Phi 0 δ = (δ ⟨0, Nat.zero_lt_succ _⟩) ^ 2 := by
      unfold Phi
      have h1 : (⟨0, Nat.zero_lt_succ _⟩ : Fin 1) ∈ Finset.univ := Finset.mem_univ _
      have hle : ∀ i ∈ (Finset.univ : Finset (Fin 1)), phiTerm 0 δ i ≤ phiTerm 0 δ ⟨0, Nat.zero_lt_succ _⟩ := by
        intro i _
        have : i = ⟨0, Nat.zero_lt_succ _⟩ := by ext; omega
        simp [this]
      have hge : phiTerm 0 δ ⟨0, Nat.zero_lt_succ _⟩ ≤ Finset.sup' Finset.univ ⟨⟨0, Nat.zero_lt_succ _⟩, h1⟩ (fun i => phiTerm 0 δ i) := by
        apply Finset.le_sup' _ (Finset.mem_univ _)
      have hsup_le : Finset.sup' Finset.univ ⟨⟨0, Nat.zero_lt_succ _⟩, h1⟩ (fun i => phiTerm 0 δ i) ≤ phiTerm 0 δ ⟨0, Nat.zero_lt_succ _⟩ := by
        apply Finset.sup'_le _ _; intro i hi; exact hle i hi
      have hsup_eq : Finset.sup' Finset.univ ⟨⟨0, Nat.zero_lt_succ _⟩, h1⟩ (fun i => phiTerm 0 δ i) = phiTerm 0 δ ⟨0, Nat.zero_lt_succ _⟩ := le_antisymm hsup_le hge
      rw [hsup_eq]
      unfold phiTerm
      simp [show ¬ ((⟨0, Nat.zero_lt_succ _⟩ : Fin 1).val < (0:ℕ)) from by omega]
    rw [hPhi, h0]
    unfold rOGM
    have hθ0 : SmoothBenchmark.theta 0 0 = 1 := SmoothBenchmark.theta_zero 0
    simp [hθ0]
  · have hN1 : 1 ≤ N := by omega
    have hδ : ∀ i, 0 ≤ δ i := hΔ.1
    have h_sum : ∑ i : Fin (N+1), δ i = 1 := hΔ.2
    have hm_pos : 0 < Phi N δ := by
      have h_exists : ∃ i : Fin (N+1), 0 < δ i := by
        by_contra h
        push_neg at h
        have h_zero : ∀ i : Fin (N+1), δ i = 0 := by intro i; have hle := h i; have hge := hδ i; linarith
        have h_sum_zero : ∑ i : Fin (N+1), δ i = 0 := by
          apply Finset.sum_eq_zero; intro i _; rw [h_zero i]
        linarith
      obtain ⟨i, hi⟩ := h_exists
      have h_phi_ge : phiTerm N δ i ≤ Phi N δ := by
        unfold Phi; apply Finset.le_sup' _ (Finset.mem_univ i)
      have h_phi_pos : 0 < phiTerm N δ i := by
        unfold phiTerm
        by_cases hlt : i.val < N
        · simp only [hlt, ↓reduceIte]
          have hS_pos : 0 < S N δ i.val := by
            have h1 : 0 ≤ S N δ i.val := S_nonneg N δ hδ i.val
            have h2 : δ i ≤ S N δ i.val := delta_le_S N δ hδ i i.val le_rfl
            linarith
          have h_num_pos : 0 < (δ i) ^ 2 := by have : 0 < δ i := hi; positivity
          have h_den_pos : 0 < 2 * S N δ i.val := by positivity
          exact div_pos h_num_pos h_den_pos
        · simp only [hlt, ↓reduceIte]
          positivity
      linarith
    let m := Phi N δ
    have hm_eq : m = Phi N δ := rfl
    have hS_N1_le : S N δ (N-1) ≤ 2 * m * (SmoothBenchmark.theta N (N-1) ^ 2) := S_le_bound N δ hΔ m hm_eq hm_pos (N-1) (by omega)
    have h_deltaN_le : δ ⟨N, Nat.lt_succ_self N⟩ ≤ Real.sqrt m := by
      have h_phi_ge_N : phiTerm N δ ⟨N, Nat.lt_succ_self N⟩ ≤ m := by
        unfold Phi at *
        apply Finset.le_sup' _ (Finset.mem_univ _)
      unfold phiTerm at h_phi_ge_N
      have h1 : ¬ ((⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)).val < N) := by simp
      simp only [h1, ↓reduceIte] at h_phi_ge_N
      exact Real.le_sqrt_of_sq_le h_phi_ge_N
    have h_total : S N δ (N-1) + δ ⟨N, Nat.lt_succ_self N⟩ = 1 := by
      have h1 : S N δ ((N-1)+1) = S N δ (N-1) + δ ⟨(N-1)+1, by omega⟩ := S_succ_eq N δ (N-1) (by omega)
      have hN_eq : (N-1)+1 = N := Nat.sub_add_cancel hN1
      have hS_eq : S N δ ((N-1)+1) = S N δ N := by rw [hN_eq]
      have hFin : (⟨(N-1)+1, by omega⟩ : Fin (N+1)) = (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) := by ext; omega
      rw [hS_eq] at h1
      rw [hFin] at h1
      have hS_total : S N δ N = ∑ i : Fin (N+1), δ i := S_eq_total N δ N (by omega)
      rw [h_sum] at hS_total
      linarith
    have h_g_le : 1 ≤ 2 * m * (SmoothBenchmark.theta N (N-1) ^ 2) + Real.sqrt m := by linarith
    have h_g_r : 2 * rOGM N * (SmoothBenchmark.theta N (N-1) ^ 2) + Real.sqrt (rOGM N) = 1 := by
      have hsqrt : Real.sqrt (rOGM N) = 1 / SmoothBenchmark.theta N N := by
        unfold rOGM
        have hθ_pos : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
        have hθ_nn : 0 ≤ SmoothBenchmark.theta N N := le_of_lt hθ_pos
        have h1 : Real.sqrt (1 / (SmoothBenchmark.theta N N ^ 2)) = Real.sqrt 1 / Real.sqrt (SmoothBenchmark.theta N N ^ 2) := by
          rw [Real.sqrt_div (by positivity)]
        have h2 : Real.sqrt (1 : ℝ) = 1 := by simp
        have h3 : Real.sqrt (SmoothBenchmark.theta N N ^ 2) = SmoothBenchmark.theta N N := Real.sqrt_sq hθ_nn
        rw [h1, h2, h3]
      rw [hsqrt]
      unfold rOGM
      have hsq := theta_sq_final N hN1
      have hθ_pos : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
      have hθ_ne : SmoothBenchmark.theta N N ≠ 0 := ne_of_gt hθ_pos
      field_simp
      nlinarith [hsq]
    have h_mono : ∀ a b : ℝ, 0 ≤ a → a < b → 2 * a * (SmoothBenchmark.theta N (N-1) ^ 2) + Real.sqrt a < 2 * b * (SmoothBenchmark.theta N (N-1) ^ 2) + Real.sqrt b := by
      intro a b ha hab
      have h1 : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha hab
      have hθ2 : 0 ≤ SmoothBenchmark.theta N (N-1) ^ 2 := by positivity
      have h2 : 2 * a * (SmoothBenchmark.theta N (N-1) ^ 2) ≤ 2 * b * (SmoothBenchmark.theta N (N-1) ^ 2) := by nlinarith
      linarith
    by_contra h_lt
    push_neg at h_lt
    have h_m_lt_r : m < rOGM N := h_lt
    have h_g_m_lt : 2 * m * (SmoothBenchmark.theta N (N-1) ^ 2) + Real.sqrt m < 1 := by
      rw [←h_g_r]
      exact h_mono _ _ (le_of_lt hm_pos) h_m_lt_r
    linarith

lemma le_of_sq_le_sq' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by nlinarith

lemma sqrt_rOGM (N : ℕ) : Real.sqrt (rOGM N) = 1 / SmoothBenchmark.theta N N := by
  unfold rOGM
  have hθ : 0 < SmoothBenchmark.theta N N := SmoothBenchmark.theta_pos N N le_rfl
  rw [Real.sqrt_div (by positivity), Real.sqrt_one, Real.sqrt_sq hθ.le]

lemma terminal_rOGM_identity (N : ℕ) (hN : 1 ≤ N) :
    2 * rOGM N * SmoothBenchmark.theta N (N-1) ^ 2 + Real.sqrt (rOGM N) = 1 := by
  rw [sqrt_rOGM]
  unfold rOGM
  have hθ := SmoothBenchmark.theta_pos N N le_rfl
  have hsq := theta_sq_final N hN
  field_simp
  nlinarith


lemma total_split (N : ℕ) (δ : Fin (N+1) → ℝ) (hN : 1 ≤ N)
    (hsum : ∑ i, δ i = 1) : S N δ (N-1) + δ ⟨N, Nat.lt_succ_self N⟩ = 1 := by
  have h := S_succ_eq N δ (N-1) (by omega)
  have ht := S_eq_total N δ N le_rfl
  have h' : S N δ N = S N δ (N-1) + δ ⟨N, Nat.lt_succ_self N⟩ := by
    simpa [Nat.sub_add_cancel hN] using h
  rw [hsum] at ht
  linarith


lemma delta_le_of_sum_eq {r x d u : ℝ} (hr : 0 < r) (hu : 0 < u) (hd : 0 ≤ d)
    (h : x + d = 2 * r * u ^ 2) (hdSq : d ^ 2 ≤ 2 * r * (x+d)) :
    d ≤ 2 * r * u := by
  apply le_of_sq_le_sq' (by positivity) (by positivity)
  calc d ^ 2 ≤ 2 * r * (x+d) := hdSq
    _ = (2 * r * u) ^ 2 := by rw [h]; ring

/-- Backward uniqueness given the already-established partial-sum bound. -/
theorem uniqueness_of_partialSum_bound (N : ℕ) (δ : Fin (N+1) → ℝ) (hN : 1 ≤ N)
    (hΔ : DeltaProp N δ) (hPhi : Phi N δ = rOGM N)
    (hb : ∀ k, k < N → S N δ k ≤ 2 * rOGM N * SmoothBenchmark.theta N k ^ 2) :
    ∀ i, δ i = deltaStar N i := by
  have hr := rOGM_pos N
  have hδNsq : δ ⟨N, Nat.lt_succ_self N⟩ ^ 2 ≤ rOGM N := by
    have hf : phiTerm N δ ⟨N, Nat.lt_succ_self N⟩ ≤ Phi N δ :=
      Finset.le_sup' _ (Finset.mem_univ _)
    rw [hPhi] at hf
    simpa [phiTerm] using hf
  have hδN : δ ⟨N, Nat.lt_succ_self N⟩ ≤ Real.sqrt (rOGM N) :=
    le_of_sq_le_sq' (hΔ.1 _) (Real.sqrt_nonneg _) (by
      rw [Real.sq_sqrt hr.le]
      exact hδNsq)
  have ht := total_split N δ hN hΔ.2
  have hopt := terminal_rOGM_identity N hN
  have hSN := hb (N-1) (by omega)
  have hterm : S N δ (N-1) = 2 * rOGM N * SmoothBenchmark.theta N (N-1) ^ 2 ∧
      δ ⟨N, Nat.lt_succ_self N⟩ = Real.sqrt (rOGM N) := by
    constructor <;> linarith
  have hall : ∀ k, k < N → S N δ k = 2 * rOGM N * SmoothBenchmark.theta N k ^ 2 := by
    intro k hk
    have hdec : ∀ j, j ≤ N-1 → j < N → S N δ j = 2 * rOGM N * SmoothBenchmark.theta N j ^ 2 := by
      intro j hj
      induction hj using Nat.decreasingInduction with
      | self => exact fun _ => hterm.1
      | of_succ j hj ih =>
          intro hjN
          have hcur := ih (by omega)
          have hstep := S_succ_eq N δ j (by omega)
          have hjN' : j+1 < N := by omega
          let i : Fin (N+1) := ⟨j+1, Nat.lt_succ_of_le hjN'.le⟩
          have hdSq := delta_sq_le N δ hΔ (rOGM N) hPhi.symm i hjN'
          change δ i ^ 2 ≤ 2 * rOGM N * S N δ i.val at hdSq
          change δ i ^ 2 ≤ 2 * rOGM N * S N δ (j+1) at hdSq
          have htpos := SmoothBenchmark.theta_pos N (j+1) hjN'.le
          have hdle : δ i ≤ 2 * rOGM N * SmoothBenchmark.theta N (j+1) := by
            apply delta_le_of_sum_eq hr htpos (hΔ.1 i)
            · rw [← hstep, hcur]
            · rw [← hstep]
              exact hdSq
          have hrec : SmoothBenchmark.theta N (j+1) ^ 2 =
              SmoothBenchmark.theta N (j+1) + SmoothBenchmark.theta N j ^ 2 := by
            simpa using theta_sq_standard N (j+1) (by omega) (by omega)
          have hupper := hb j hjN
          have hstep' : S N δ (j+1) = S N δ j + δ i := by
            simpa [i] using hstep
          apply le_antisymm hupper
          nlinarith
    exact hdec k (by omega) hk
  intro i
  obtain ⟨k, hk⟩ := i
  by_cases hkN : k < N
  · unfold deltaStar
    simp only [hkN, ↓reduceIte]
    cases k with
    | zero =>
        have hs := hall 0 hkN
        rw [S_zero_eq, SmoothBenchmark.theta_zero] at hs
        have he : (⟨0, hk⟩ : Fin (N+1)) = ⟨0, Nat.zero_lt_succ N⟩ := Fin.ext rfl
        rw [he]
        calc δ ⟨0, Nat.zero_lt_succ N⟩ = 2 * rOGM N * 1 ^ 2 := hs
          _ = 2 * rOGM N * SmoothBenchmark.theta N 0 := by rw [SmoothBenchmark.theta_zero]; ring
    | succ j =>
        have hcur := hall (j+1) hkN
        have hprev := hall j (by omega)
        have hstep := S_succ_eq N δ j (by omega)
        have he : (⟨j+1, by omega⟩ : Fin (N+1)) = ⟨j+1, hk⟩ := Fin.ext rfl
        rw [he] at hstep
        calc δ ⟨j+1, hk⟩ = S N δ (j+1) - S N δ j := by linarith [hstep]
          _ = 2 * rOGM N * SmoothBenchmark.theta N (j+1) := by
            rw [hcur, hprev]
            have ht : SmoothBenchmark.theta N (j+1) ^ 2 =
                SmoothBenchmark.theta N (j+1) + SmoothBenchmark.theta N j ^ 2 := by
              simpa using theta_sq_standard N (j+1) (by omega) (by omega)
            have ht' : SmoothBenchmark.theta N (j+1) ^ 2 - SmoothBenchmark.theta N j ^ 2 =
                SmoothBenchmark.theta N (j+1) := by linarith
            calc 2 * rOGM N * SmoothBenchmark.theta N (j+1) ^ 2 -
                  2 * rOGM N * SmoothBenchmark.theta N j ^ 2 =
                2 * rOGM N * (SmoothBenchmark.theta N (j+1) ^ 2 -
                  SmoothBenchmark.theta N j ^ 2) := by ring
              _ = 2 * rOGM N * SmoothBenchmark.theta N (j+1) := by rw [ht']
  · have hkEq : k = N := by omega
    subst k
    rw [hterm.2]
    unfold deltaStar
    simp [sqrt_rOGM]

theorem uniqueness (N : ℕ) (δ : Fin (N+1) → ℝ) (hΔ : DeltaProp N δ)
    (hPhi : Phi N δ = rOGM N) : ∀ i, δ i = deltaStar N i := by
  by_cases hN : N = 0
  · subst N
    intro i
    obtain ⟨k, hk⟩ := i
    have hk0 : k = 0 := by omega
    subst k
    have hd : δ ⟨0, hk⟩ = 1 := by simpa using hΔ.2
    simp only [deltaStar, lt_self_iff_false, ↓reduceIte, rOGM,
      SmoothBenchmark.theta_zero, one_pow, div_one, Real.sqrt_one]
    exact hd
  · have hr : 0 < rOGM N := rOGM_pos N
    exact uniqueness_of_partialSum_bound N δ (by omega) hΔ hPhi
      (fun k hk => S_le_bound N δ hΔ (rOGM N) hPhi.symm hr k hk)

end GJP