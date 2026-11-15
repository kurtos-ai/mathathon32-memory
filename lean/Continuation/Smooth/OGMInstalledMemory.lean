module
public import Continuation.Smooth.OGM
public import RealizationCore.RankIdentity
public import RealizationCore.MemoryCharacterization
public import RealizationCore.RealizationTheorem
public import MemoryRank.IncrementalRank
public import MemoryRank.ZeroLocus
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace InstalledOGM

open Matrix RealizationCore MemoryRank.Incremental RegisterMachine
open SmoothOGM

def ogmT_inst (N : ℕ) (L : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  RealizationCore.T_of N (SmoothOGM.ogmW N L)

def ogmS_inst (N : ℕ) (L : ℝ) (k : ℕ) : Matrix (Fin (N - k)) (Fin k) ℝ :=
  RealizationCore.S_k_of N k (SmoothOGM.ogmW N L)

theorem Hk_bridge (N k : ℕ) (hk : k ≤ N) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    RegisterMachine.H_k N k hk W = RealizationCore.H_k N k hk W := by
  ext i j
  simp only [RegisterMachine.H_k, RealizationCore.H_k, Matrix.of_apply]
  split
  · rfl
  ·
    have hrow : (⟨k + i.val, by omega⟩ : Fin (N+1)) = ⟨k + i.val, RealizationCore.k_add_i_lt_Succ hk i.isLt⟩ := Fin.ext rfl
    have hcol : (⟨j.val - 1, by omega⟩ : Fin (N+1)) = ⟨j.val - 1, by omega⟩ := Fin.ext rfl
    rw [hrow, hcol]

theorem theta_one_one : SmoothBenchmark.theta 1 1 = 2 := by
  have h : SmoothBenchmark.theta 1 1 = (1 + Real.sqrt (1 + 8 * SmoothBenchmark.theta 1 0 ^ 2)) / 2 := by
    simp only [SmoothBenchmark.theta, show ¬(0+1 < 1) from by omega, show (0+1:ℕ)=1 from rfl, ↓reduceIte]
  rw [h]
  have h0 : SmoothBenchmark.theta 1 0 = (1:ℝ) := rfl
  rw [h0]
  have h1 : (1:ℝ) + 8 * (1:ℝ) ^ 2 = 9 := by ring
  rw [h1]
  have hsq : Real.sqrt (9:ℝ) = 3 := by
    have : (9:ℝ) = 3^2 := by norm_num
    rw [this]; exact Real.sqrt_sq (by norm_num)
  rw [hsq]; ring

theorem theta_N_one (N : ℕ) (hN : 2 ≤ N) : SmoothBenchmark.theta N 1 = (1 + Real.sqrt 5) / 2 := by
  have h1 : SmoothBenchmark.theta N 1 = (1 + Real.sqrt (1 + 4 * SmoothBenchmark.theta N 0 ^ 2)) / 2 := by
    show SmoothBenchmark.theta N ((0:ℕ)+1) = _
    simp only [SmoothBenchmark.theta, show (0+1 < N) from by omega, ↓reduceIte]
  rw [h1]
  have h0 : SmoothBenchmark.theta N 0 = (1:ℝ) := rfl
  rw [h0]
  have : (1:ℝ) + 4 * (1:ℝ) ^ 2 = 5 := by ring
  rw [this]

theorem theta_one_gt_one (N : ℕ) (hN : 2 ≤ N) : 1 < SmoothBenchmark.theta N 1 := by
  rw [theta_N_one N hN]
  have : 1 < Real.sqrt (5:ℝ) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem T10_numer_ne_zero (N : ℕ) (hN : 2 ≤ N) : 1 - 1 / SmoothBenchmark.theta N 1 ≠ 0 := by
  have hgt : 1 < SmoothBenchmark.theta N 1 := theta_one_gt_one N hN
  have hpos : 0 < SmoothBenchmark.theta N 1 := SmoothBenchmark.theta_pos N 1 (by omega)
  have : 1 / SmoothBenchmark.theta N 1 < 1 := by rw [div_lt_one hpos]; exact hgt
  linarith

theorem increment_eq (Nn : ℕ) (L : ℝ) (i j : Fin Nn) (hij : j.val < i.val) :
    ogmT_inst Nn L i j = SmoothOGM.ogmACoeff Nn L (i.val + 1) j.val - SmoothOGM.ogmACoeff Nn L i.val j.val := by
  unfold ogmT_inst RealizationCore.T_of
  simp only [Matrix.of_apply, hij, dite_true]
  have h1 : (SmoothOGM.ogmW Nn L) ⟨i.val + 1, by omega⟩ ⟨j.val, by omega⟩ = SmoothOGM.ogmACoeff Nn L (i.val+1) j.val := by
    simp [SmoothOGM.ogmW, Matrix.of_apply, show j.val < i.val + 1 by omega]
  have h2 : (SmoothOGM.ogmW Nn L) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = SmoothOGM.ogmACoeff Nn L i.val j.val := by
    simp [SmoothOGM.ogmW, Matrix.of_apply, hij]
  rw [h1, h2]

theorem increment_eq_zero (Nn : ℕ) (L : ℝ) (i j : Fin Nn) (hij : ¬ j.val < i.val) :
    ogmT_inst Nn L i j = 0 := by
  unfold ogmT_inst
  simp only [RealizationCore.T_of, Matrix.of_apply, hij, dite_false]

theorem ogmACoeff_one_zero (N : ℕ) (L : ℝ) (hN : 1 ≤ N) :
    SmoothOGM.ogmACoeff N L 1 0 = -(1 + (2 * SmoothBenchmark.theta N 0 - 1) / SmoothBenchmark.theta N 1) / L := by
  have h0 : (0 : ℕ) < N := by omega
  have := SmoothOGM.aCoeff_succ_eq N L 0 h0
  simpa using this

theorem ogmACoeff_one_zero_simplified (N : ℕ) (L : ℝ) (hN : 1 ≤ N) :
    SmoothOGM.ogmACoeff N L 1 0 = -(1 + 1 / SmoothBenchmark.theta N 1) / L := by
  have h := ogmACoeff_one_zero N L hN
  have htheta0 : SmoothBenchmark.theta N 0 = 1 := rfl
  rw [htheta0] at h
  simp only [show (2 * (1:ℝ) - 1) = 1 from by ring] at h
  exact h

theorem ogmECoeff_one_zero (N : ℕ) (L : ℝ) (hN : 1 ≤ N) :
    SmoothOGM.ogmECoeff N L 1 0 = -(2 * SmoothBenchmark.theta N 0 - 1) * (1 - 1 / SmoothBenchmark.theta N 1) / L := by
  have h0 : (0 : ℕ) < N := by omega
  have := SmoothOGM.eCoeff_succ_eq N L 0 h0
  simpa using this

theorem ogmECoeff_one_zero_simplified (N : ℕ) (L : ℝ) (hN : 1 ≤ N) :
    SmoothOGM.ogmECoeff N L 1 0 = -(1 - 1 / SmoothBenchmark.theta N 1) / L := by
  have h0 : (0 : ℕ) < N := by omega
  have h := SmoothOGM.eCoeff_succ_eq N L 0 h0
  have htheta0 : SmoothBenchmark.theta N 0 = 1 := rfl
  rw [htheta0] at h
  have h2 : (2 * (1:ℝ) - 1) = 1 := by ring
  rw [h2] at h
  have h3 : -(1 : ℝ) * (1 - 1 / SmoothBenchmark.theta N 1) / L = -(1 - 1 / SmoothBenchmark.theta N 1) / L := by ring
  rw [h3] at h
  exact h

theorem ogmACoeff_two_zero (N : ℕ) (L : ℝ) (hN : 2 ≤ N) :
    SmoothOGM.ogmACoeff N L 2 0 = SmoothOGM.ogmACoeff N L 1 0 + 1 / SmoothBenchmark.theta N 2 * SmoothOGM.ogmECoeff N L 1 0 := by
  have hk : 1 < N := by omega
  exact SmoothOGM.aCoeff_succ_lt N L 1 0 hk (by omega)

theorem T10_eq (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : L ≠ 0) :
    ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ = -(1 - 1 / SmoothBenchmark.theta N 1) / (L * SmoothBenchmark.theta N 2) := by
  have hij : (0 : ℕ) < 1 := by omega
  rw [increment_eq N L _ _ hij]
  have h1 : SmoothOGM.ogmACoeff N L 1 0 = -(1 + 1 / SmoothBenchmark.theta N 1) / L := ogmACoeff_one_zero_simplified N L (by omega)
  have h2 : SmoothOGM.ogmACoeff N L 2 0 = SmoothOGM.ogmACoeff N L 1 0 + 1 / SmoothBenchmark.theta N 2 * SmoothOGM.ogmECoeff N L 1 0 := ogmACoeff_two_zero N L hN
  have h3 : SmoothOGM.ogmECoeff N L 1 0 = -(1 - 1 / SmoothBenchmark.theta N 1) / L := ogmECoeff_one_zero_simplified N L (by omega)
  rw [h2, h3, h1]
  field_simp
  ring

theorem T10_ne_zero (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : L ≠ 0) (hth2 : SmoothBenchmark.theta N 2 ≠ 0) :
    ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ ≠ 0 := by
  rw [T10_eq N L hN hL]
  have hnum : 1 - 1 / SmoothBenchmark.theta N 1 ≠ 0 := T10_numer_ne_zero N hN
  have h : -(1 - 1 / SmoothBenchmark.theta N 1) ≠ 0 := by
    intro heq
    have : 1 - 1 / SmoothBenchmark.theta N 1 = 0 := by linarith
    exact hnum this
  exact div_ne_zero h (mul_ne_zero hL hth2)

theorem T_zero_of_N1 (L : ℝ) : ogmT_inst 1 L = 0 := by
  ext i j
  have hij : ¬ j.val < i.val := by
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega
  exact increment_eq_zero 1 L i j hij

theorem S1_entry_T10 (N : ℕ) (L : ℝ) (hN : 2 ≤ N) :
    ogmS_inst N L 1 ⟨0, by omega⟩ ⟨0, by omega⟩ = ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ := by
  have hk : 1 ≤ N := by omega
  have h1 : ogmS_inst N L 1 ⟨0, by omega⟩ ⟨0, by omega⟩ = RealizationCore.T_of N (SmoothOGM.ogmW N L) ⟨1, by omega⟩ ⟨0, by omega⟩ := by
    unfold ogmS_inst
    simp only [RealizationCore.S_k_of, hk, dite_true]
    rfl
  have h2 : RealizationCore.T_of N (SmoothOGM.ogmW N L) ⟨1, by omega⟩ ⟨0, by omega⟩ = ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ := rfl
  rw [h1, h2]

theorem S1_rank_one (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : L ≠ 0) (hth2 : SmoothBenchmark.theta N 2 ≠ 0) :
    (ogmS_inst N L 1).rank = 1 := by
  have hne : ogmS_inst N L 1 ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ 0 := by
    rw [S1_entry_T10 N L hN]
    exact T10_ne_zero N L hN hL hth2
  have hle : (ogmS_inst N L 1).rank ≤ 1 := by
    have h := Matrix.rank_le_width (R := ℝ) (A := ogmS_inst N L 1)
    simpa using h
  have hge : 1 ≤ (ogmS_inst N L 1).rank := by
    let sub : Matrix (Fin 1) (Fin 1) ℝ := (ogmS_inst N L 1).submatrix (fun _ => ⟨0, by omega⟩) (fun _ => ⟨0, by omega⟩)
    have hsub_eq : sub = Matrix.of fun _ _ => ogmS_inst N L 1 ⟨0, by omega⟩ ⟨0, by omega⟩ := by
      ext i j; fin_cases i; fin_cases j; simp [sub, Matrix.submatrix_apply]
    have hdet : sub.det = ogmS_inst N L 1 ⟨0, by omega⟩ ⟨0, by omega⟩ := by
      rw [hsub_eq]; simp
    have hdet_ne : sub.det ≠ 0 := by rw [hdet]; exact hne
    have hrank1 : sub.rank = 1 := by
      rw [Matrix.rank_of_det_ne_zero hdet_ne]
      simp
    have hle_sub : sub.rank ≤ (ogmS_inst N L 1).rank := Matrix.rank_submatrix_le _ _ _
    omega
  omega

theorem T_in_Q1_of_realization (N : ℕ) (L : ℝ) (hReal : RegisterMachine.HasRealization N (SmoothOGM.ogmW N L) 2) :
    MemoryRank.Incremental.Q N 1 (ogmT_inst N L) := by
  intro k hk1 hkN
  have hk_le : k ≤ N := by omega
  have hH : (RegisterMachine.H_k N k hk_le (SmoothOGM.ogmW N L)).rank ≤ 2 := by
    exact (RegisterMachine.realization_iff_rank_all (SmoothOGM.ogmW N L) 2).mp hReal k hk_le
  have hH_real : (RealizationCore.H_k N k hk_le (SmoothOGM.ogmW N L)).rank ≤ 2 := by
    calc (RealizationCore.H_k N k hk_le (SmoothOGM.ogmW N L)).rank
        = (RegisterMachine.H_k N k hk_le (SmoothOGM.ogmW N L)).rank := by rw [← Hk_bridge]
      _ ≤ 2 := hH
  have h_eq : (RealizationCore.H_k N k hk_le (SmoothOGM.ogmW N L)).rank = 1 + (ogmS_inst N L k).rank := by
    have h_eq2 : (RealizationCore.H_k N k hk_le (SmoothOGM.ogmW N L)).rank = 1 + (RealizationCore.S_k_of N k (SmoothOGM.ogmW N L)).rank :=
      RealizationCore.rank_H_eq_one_add_rank_S N k hk_le (SmoothOGM.ogmW N L)
    have hs : RealizationCore.S_k_of N k (SmoothOGM.ogmW N L) = ogmS_inst N L k := rfl
    rw [hs] at h_eq2
    exact h_eq2
  have hS_le : (ogmS_inst N L k).rank ≤ 1 := by omega
  have hQ : (MemoryRank.Incremental.S_k N k (ogmT_inst N L)).rank ≤ 1 := by
    have : MemoryRank.Incremental.S_k N k (ogmT_inst N L) = ogmS_inst N L k := rfl
    rw [this]
    exact hS_le
  exact hQ

theorem T_in_Q1_unconditional (N : ℕ) (L : ℝ) : MemoryRank.Incremental.Q N 1 (ogmT_inst N L) := by
  apply T_in_Q1_of_realization N L (SmoothOGM.ogmHasRealization N L)

theorem s_WO_eq_one_of_N1 (L : ℝ) (_hL : L ≠ 0) (_hReal : RegisterMachine.HasRealization 1 (SmoothOGM.ogmW 1 L) 2) :
    RegisterMachine.HasRealization 1 (SmoothOGM.ogmW 1 L) 1 := by
  rw [RegisterMachine.one_register_iff_zero_increment]
  exact T_zero_of_N1 L

theorem s_WO_not_one_of_ge2 (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : L ≠ 0) (hth2 : SmoothBenchmark.theta N 2 ≠ 0) :
    ¬ RegisterMachine.HasRealization N (SmoothOGM.ogmW N L) 1 := by
  intro h1
  have hT0 : ogmT_inst N L = 0 := by
    have h := (RegisterMachine.one_register_iff_zero_increment N (SmoothOGM.ogmW N L)).mp h1
    simpa [ogmT_inst] using h
  have hT10_ne : ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ ≠ 0 := T10_ne_zero N L hN hL hth2
  have hT10_eq : ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ = 0 := by
    have heq := congrFun (congrFun hT0 ⟨1, by omega⟩) ⟨0, by omega⟩
    simpa using heq
  exact hT10_ne hT10_eq

theorem memory_conclusion_N1 (L : ℝ) (hL : L ≠ 0) (hReal2 : RegisterMachine.HasRealization 1 (SmoothOGM.ogmW 1 L) 2) :
    IsLeast {s : ℕ | RegisterMachine.HasRealization 1 (SmoothOGM.ogmW 1 L) s} 1 := by
  have h1 : RegisterMachine.HasRealization 1 (SmoothOGM.ogmW 1 L) 1 := s_WO_eq_one_of_N1 L hL hReal2
  constructor
  · exact h1
  · intro s hs
    have h_rank := (RegisterMachine.realization_iff_rank_all (SmoothOGM.ogmW 1 L) s).mp hs
    have hcut : (RealizationCore.H_k 1 0 (by omega) (SmoothOGM.ogmW 1 L)).rank = 1 := by
      have h_eq := RealizationCore.rank_H_eq_one_add_rank_S 1 0 (by omega) (SmoothOGM.ogmW 1 L)
      have hS0 : (RealizationCore.S_k_of 1 0 (SmoothOGM.ogmW 1 L)).rank = 0 := by
        have h_empty : (RealizationCore.S_k_of 1 0 (SmoothOGM.ogmW 1 L)) = (0 : Matrix (Fin (1-0)) (Fin 0) ℝ) := by
          ext i j; fin_cases j
        rw [h_empty]; simp
      rw [h_eq, hS0]
    have h0_le2 : (RealizationCore.H_k 1 0 (by omega) (SmoothOGM.ogmW 1 L)).rank ≤ s := by
      have hmp : (RegisterMachine.H_k 1 0 (by omega) (SmoothOGM.ogmW 1 L)).rank ≤ s := h_rank 0 (by omega)
      calc (RealizationCore.H_k 1 0 (by omega) (SmoothOGM.ogmW 1 L)).rank
          = (RegisterMachine.H_k 1 0 (by omega) (SmoothOGM.ogmW 1 L)).rank := by rw [← Hk_bridge]
        _ ≤ s := hmp
    rw [hcut] at h0_le2
    exact h0_le2

theorem memory_conclusion_ge2 (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : L ≠ 0) (hth2 : SmoothBenchmark.theta N 2 ≠ 0)
    (hReal2 : RegisterMachine.HasRealization N (SmoothOGM.ogmW N L) 2) :
    IsLeast {s : ℕ | RegisterMachine.HasRealization N (SmoothOGM.ogmW N L) s} 2 := by
  have h_not1 : ¬ RegisterMachine.HasRealization N (SmoothOGM.ogmW N L) 1 := s_WO_not_one_of_ge2 N L hN hL hth2
  constructor
  · exact hReal2
  · intro s hs
    by_contra hlt
    have hs_lt2 : s < 2 := by omega
    have h_cases : s = 0 ∨ s = 1 := by omega
    cases h_cases with
    | inl h0 =>
      rw [h0] at hs
      have h_rank := (RegisterMachine.realization_iff_rank_all (SmoothOGM.ogmW N L) 0).mp hs
      have h0rank : (RegisterMachine.H_k N 0 (by omega) (SmoothOGM.ogmW N L)).rank ≤ 0 := h_rank 0 (by omega)
      have hcut1 : 1 ≤ (RegisterMachine.H_k N 0 (by omega) (SmoothOGM.ogmW N L)).rank := by
        have h_eq := RealizationCore.rank_H_eq_one_add_rank_S N 0 (by omega) (SmoothOGM.ogmW N L)
        have heq := Hk_bridge N 0 (by omega) (SmoothOGM.ogmW N L)
        rw [heq, h_eq]
        exact Nat.le_add_right 1 _
      omega
    | inr h1s =>
      rw [h1s] at hs
      exact h_not1 hs

theorem memory_conclusion_N1_unconditional (L : ℝ) (hL : L ≠ 0) :
    IsLeast {s : ℕ | RegisterMachine.HasRealization 1 (SmoothOGM.ogmW 1 L) s} 1 :=
  memory_conclusion_N1 L hL (SmoothOGM.ogmHasRealization 1 L)

theorem memory_conclusion_ge2_unconditional (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : L ≠ 0) (hth2 : SmoothBenchmark.theta N 2 ≠ 0) :
    IsLeast {s : ℕ | RegisterMachine.HasRealization N (SmoothOGM.ogmW N L) s} 2 :=
  memory_conclusion_ge2 N L hN hL hth2 (SmoothOGM.ogmHasRealization N L)

theorem theta_pos_ne_zero (N k : ℕ) (hk : k ≤ N) : SmoothBenchmark.theta N k ≠ 0 :=
  ne_of_gt (SmoothBenchmark.theta_pos N k hk)

theorem T10_ne_zero_of_pos (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : L ≠ 0) :
    ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ ≠ 0 :=
  T10_ne_zero N L hN hL (theta_pos_ne_zero N 2 (by omega))

theorem memory_conclusion_ge2_pos (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : 0 < L) :
    IsLeast {s : ℕ | RegisterMachine.HasRealization N (SmoothOGM.ogmW N L) s} 2 :=
  memory_conclusion_ge2_unconditional N L hN (ne_of_gt hL) (theta_pos_ne_zero N 2 (by omega))

theorem T10_eq_pos (N : ℕ) (L : ℝ) (hN : 2 ≤ N) (hL : 0 < L) :
    ogmT_inst N L ⟨1, by omega⟩ ⟨0, by omega⟩ = -(1 - 1 / SmoothBenchmark.theta N 1) / (L * SmoothBenchmark.theta N 2) :=
  T10_eq N L hN (ne_of_gt hL)



end InstalledOGM
