module

public import Benchmarks.Smooth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic
public import RealizationCore.VectorRealization
/-! The paper's OGM coefficient recurrence and its actual two-register realization.
All query points and the terminal output are proved correct for arbitrary formal
inputs in every finite dimension. No performance or optimality theorem is claimed. -/
@[expose] public section
noncomputable section
namespace SmoothOGM

open Matrix BigOperators
open RegisterMachine

export SmoothBenchmark (theta theta_pos theta_ge_one)

noncomputable def betaCoeff (N k : ℕ) : ℝ := 1 / theta N (k+1)

noncomputable def ogmCoeffs (N : ℕ) (L : ℝ) : ℕ → (ℕ → ℝ) × (ℕ → ℝ)
  | 0 => (fun _ => 0, fun _ => 0)
  | k+1 =>
    let prev := ogmCoeffs N L k
    let aPrev := prev.1
    let ePrev := prev.2
    if h : k < N then
      (fun j =>
        if j < k then aPrev j + (1 / theta N (k+1)) * ePrev j
        else if j = k then -(1 + (2 * theta N k - 1) / theta N (k+1)) / L
        else 0,
       fun j =>
        if j < k then (1 - 1 / theta N (k+1)) * ePrev j
        else if j = k then -(2 * theta N k - 1) * (1 - 1 / theta N (k+1)) / L
        else 0)
    else prev

noncomputable def ogmACoeff (N : ℕ) (L : ℝ) (k j : ℕ) : ℝ := (ogmCoeffs N L k).1 j
noncomputable def ogmECoeff (N : ℕ) (L : ℝ) (k j : ℕ) : ℝ := (ogmCoeffs N L k).2 j

noncomputable def ogmW (N : ℕ) (L : ℝ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  Matrix.of fun i j => if h : j.val < i.val then ogmACoeff N L i.val j.val else 0

theorem ogmW_strict (N : ℕ) (L : ℝ) (i j : Fin (N+1))
    (h : i.val ≤ j.val) : ogmW N L i j = 0 := by
  simp only [ogmW, Matrix.of_apply, dite_eq_right (show ¬ j.val < i.val by omega)]

theorem aCoeff_succ_lt (N L k j) (hk : k < N) (hj : j < k) : ogmACoeff N L (k+1) j = ogmACoeff N L k j + (1 / theta N (k+1)) * ogmECoeff N L k j := by
  simp only [ogmACoeff, ogmECoeff, ogmCoeffs, hk, dite_true, hj, ite_true]
theorem aCoeff_succ_eq (N L k) (hk : k < N) : ogmACoeff N L (k+1) k = -(1 + (2 * theta N k - 1) / theta N (k+1)) / L := by
  simp only [ogmACoeff, ogmCoeffs, hk, dite_true]
  simp only [show ¬(k < k) from by omega, ite_false]
  simp
theorem eCoeff_succ_lt (N L k j) (hk : k < N) (hj : j < k) : ogmECoeff N L (k+1) j = (1 - 1 / theta N (k+1)) * ogmECoeff N L k j := by
  simp only [ogmACoeff, ogmECoeff, ogmCoeffs, hk, dite_true, hj, ite_true]
theorem eCoeff_succ_eq (N L k) (hk : k < N) : ogmECoeff N L (k+1) k = -(2 * theta N k - 1) * (1 - 1 / theta N (k+1)) / L := by
  simp only [ogmECoeff, ogmCoeffs, hk, dite_true]
  simp only [show ¬(k < k) from by omega, ite_false]
  simp

theorem ogmW_last_entry_simple (N : ℕ) (hN : 1 ≤ N) (L : ℝ) :
    ogmW N L ⟨N, by omega⟩ ⟨N-1, by omega⟩ = ogmACoeff N L N (N-1) := by
  have hlt : (⟨N-1, by omega⟩ : Fin (N+1)).val < (⟨N, by omega⟩ : Fin (N+1)).val := by simp; omega
  simp [ogmW, Matrix.of_apply, hlt]

theorem ogmW_last_is_d (N : ℕ) (hN : 1 ≤ N) (L : ℝ) :
    ogmW N L ⟨N, by omega⟩ ⟨N-1, by omega⟩ = -(1 + (2 * theta N (N-1) - 1) / theta N N) / L := by
  rw [ogmW_last_entry_simple N hN L]
  set M := N - 1 with hM_def
  have hN_eq : N = M + 1 := by omega
  have hM_lt : M < M+1 := by omega
  have hrw : ogmACoeff N L N (N-1) = ogmACoeff (M+1) L (M+1) M := by
    rw [show N - 1 = M from by omega, hN_eq]
  rw [hrw]
  have h1 := aCoeff_succ_eq (M+1) L M hM_lt
  have htheta1 : theta (M+1) M = theta N (N-1) := by
    rw [show M+1 = N from by omega, show M = N-1 from by omega]
  have htheta2 : theta (M+1) (M+1) = theta N N := by
    rw [show M+1 = N from by omega]
  rw [htheta1, htheta2] at h1
  exact h1

noncomputable def ogmY (N : ℕ) (L : ℝ) (x0 : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) : ℝ :=
  x0 + ∑ j : Fin k, ogmACoeff N L k j.val * g ⟨j.val, by omega⟩

noncomputable def ogmEta (N : ℕ) (L : ℝ) (g : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) : ℝ :=
  ∑ j : Fin k, ogmECoeff N L k j.val * g ⟨j.val, by omega⟩

theorem ogmY_succ (N L x0 g k) (hk : k ≤ N) (hkN : k < N) :
    ogmY N L x0 g (k+1) (by omega) = ogmY N L x0 g k hk + betaCoeff N k * ogmEta N L g k hk + ogmACoeff N L (k+1) k * g ⟨k, hkN⟩ := by
  unfold ogmY ogmEta betaCoeff
  have hsplit : (∑ j : Fin (k+1), ogmACoeff N L (k+1) j.val * g ⟨j.val, by omega⟩) =
      (∑ j : Fin k, ogmACoeff N L (k+1) (Fin.castSucc j).val * g ⟨(Fin.castSucc j).val, by omega⟩) + ogmACoeff N L (k+1) (Fin.last k).val * g ⟨(Fin.last k).val, by omega⟩ := by
    rw [Fin.sum_univ_castSucc]
  rw [hsplit]
  have hcast : ∀ j : Fin k, ogmACoeff N L (k+1) (Fin.castSucc j).val = ogmACoeff N L k j.val + (1 / theta N (k+1)) * ogmECoeff N L k j.val := by
    intro j; have hj : j.val < k := j.isLt; exact aCoeff_succ_lt N L k j.val hkN hj
  have hlast : (Fin.last k).val = k := by simp [Fin.val_last]
  have h_sum_cast : (∑ j : Fin k, ogmACoeff N L (k+1) (Fin.castSucc j).val * g ⟨(Fin.castSucc j).val, by omega⟩) =
      (∑ j : Fin k, (ogmACoeff N L k j.val + (1 / theta N (k+1)) * ogmECoeff N L k j.val) * g ⟨j.val, by omega⟩) := by
    apply Finset.sum_congr rfl; intro j _; have h1 := hcast j
    have hg_eq : g ⟨(Fin.castSucc j).val, by omega⟩ = g ⟨j.val, by omega⟩ := by apply congrArg g; apply Fin.ext; simp [Fin.val_castSucc]
    rw [h1, hg_eq]
  rw [h_sum_cast]
  have hsplit2 : (∑ j : Fin k, (ogmACoeff N L k j.val + 1 / theta N (k+1) * ogmECoeff N L k j.val) * g ⟨j.val, by omega⟩) =
      (∑ j : Fin k, ogmACoeff N L k j.val * g ⟨j.val, by omega⟩) + (1 / theta N (k+1)) * (∑ j : Fin k, ogmECoeff N L k j.val * g ⟨j.val, by omega⟩) := by
    have h1 : ∀ j : Fin k, (ogmACoeff N L k j.val + 1 / theta N (k+1) * ogmECoeff N L k j.val) * g ⟨j.val, by omega⟩ =
        ogmACoeff N L k j.val * g ⟨j.val, by omega⟩ + 1 / theta N (k+1) * (ogmECoeff N L k j.val * g ⟨j.val, by omega⟩) := by intro j; ring
    simp_rw [h1]; rw [Finset.sum_add_distrib]; have h2 : (∑ x : Fin k, 1 / theta N (k + 1) * (ogmECoeff N L k x.val * g ⟨x.val, by omega⟩)) = 1 / theta N (k+1) * ∑ x : Fin k, ogmECoeff N L k x.val * g ⟨x.val, by omega⟩ := by rw [Finset.mul_sum]
    rw [h2]
  rw [hsplit2]
  have h_last_eq : ogmACoeff N L (k+1) (Fin.last k).val * g ⟨(Fin.last k).val, by omega⟩ = ogmACoeff N L (k+1) k * g ⟨k, hkN⟩ := by
    have h1 : ogmACoeff N L (k+1) (Fin.last k).val = ogmACoeff N L (k+1) k := by rw [hlast]
    have h2 : g ⟨(Fin.last k).val, by omega⟩ = g ⟨k, hkN⟩ := by apply congrArg g; apply Fin.ext; simp [hlast]
    rw [h1, h2]
  rw [h_last_eq]; ring

theorem ogmEta_succ (N L g k) (hk : k ≤ N) (hkN : k < N) :
    ogmEta N L g (k+1) (by omega) = (1 - betaCoeff N k) * ogmEta N L g k hk + ogmECoeff N L (k+1) k * g ⟨k, hkN⟩ := by
  unfold ogmEta betaCoeff
  have hsplit : (∑ j : Fin (k+1), ogmECoeff N L (k+1) j.val * g ⟨j.val, by omega⟩) =
      (∑ j : Fin k, ogmECoeff N L (k+1) (Fin.castSucc j).val * g ⟨(Fin.castSucc j).val, by omega⟩) + ogmECoeff N L (k+1) (Fin.last k).val * g ⟨(Fin.last k).val, by omega⟩ := by
    rw [Fin.sum_univ_castSucc]
  rw [hsplit]
  have hcast : ∀ j : Fin k, ogmECoeff N L (k+1) (Fin.castSucc j).val = (1 - 1 / theta N (k+1)) * ogmECoeff N L k j.val := by
    intro j; have hj : j.val < k := j.isLt; exact eCoeff_succ_lt N L k j.val hkN hj
  have hlast : (Fin.last k).val = k := by simp [Fin.val_last]
  have h_sum_cast : (∑ j : Fin k, ogmECoeff N L (k+1) (Fin.castSucc j).val * g ⟨(Fin.castSucc j).val, by omega⟩) =
      (∑ j : Fin k, ((1 - 1 / theta N (k+1)) * ogmECoeff N L k j.val) * g ⟨j.val, by omega⟩) := by
    apply Finset.sum_congr rfl; intro j _; have h1 := hcast j
    have hg_eq : g ⟨(Fin.castSucc j).val, by omega⟩ = g ⟨j.val, by omega⟩ := by apply congrArg g; apply Fin.ext; simp [Fin.val_castSucc]
    rw [h1, hg_eq]
  rw [h_sum_cast]
  have h_factor : (∑ j : Fin k, (1 - 1 / theta N (k + 1)) * ogmECoeff N L k j.val * g ⟨j.val, by omega⟩) =
      (1 - 1 / theta N (k+1)) * (∑ j : Fin k, ogmECoeff N L k j.val * g ⟨j.val, by omega⟩) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [h_factor]
  have h_last_eq : ogmECoeff N L (k+1) (Fin.last k).val * g ⟨(Fin.last k).val, by omega⟩ = ogmECoeff N L (k+1) k * g ⟨k, hkN⟩ := by
    have h1 : ogmECoeff N L (k+1) (Fin.last k).val = ogmECoeff N L (k+1) k := by rw [hlast]
    have h2 : g ⟨(Fin.last k).val, by omega⟩ = g ⟨k, hkN⟩ := by apply congrArg g; apply Fin.ext; simp [hlast]
    rw [h1, h2]
  rw [h_last_eq]

noncomputable def ogmMachine (N : ℕ) (L : ℝ) : RegisterMachine.Machine N 2 where
  F := fun k => Matrix.of fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => betaCoeff N k.val
    | 1, 0 => 0
    | 1, 1 => 1 - betaCoeff N k.val
    | _, _ => 0
  b := fun k => fun i =>
    match i.val with
    | 0 => -(1 + (2 * theta N k.val - 1) * betaCoeff N k.val) / L
    | 1 => -(2 * theta N k.val - 1) * (1 - betaCoeff N k.val) / L
    | _ => 0
  c := fun _ => e1 2
  o := e1 2

theorem ogmW_target_eq (N L x0 g k) (hk : k ≤ N) : RegisterMachine.target N (ogmW N L) x0 g ⟨k, by omega⟩ = ogmY N L x0 g k hk := by
  unfold RegisterMachine.target ogmY
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val < k := j.isLt
  have hW : (ogmW N L) ⟨k, by omega⟩ ⟨j.val, by omega⟩ = ogmACoeff N L k j.val := by simp [ogmW, Matrix.of_apply, hj]
  rw [hW]

theorem stateNat_eq (N L x0 g k) (hk : k ≤ N) :
    stateNat N 2 (ogmMachine N L) x0 g k = fun i =>
      if i.val = 0 then ogmY N L x0 g k hk
      else if i.val = 1 then ogmEta N L g k hk else 0 := by
  induction k with
  | zero => simp [stateNat, ogmY, ogmEta, e1]
  | succ k ih =>
    have hk' : k ≤ N := by omega
    have hkN : k < N := by omega
    rw [stateNat_succ (N:=N) (s:=2) (ogmMachine N L) x0 g k hkN, ih hk']
    funext i
    fin_cases i
    · simp [Fin.sum_univ_two, ogmMachine, Matrix.of_apply,
        ogmY_succ N L x0 g k hk' hkN, aCoeff_succ_eq N L k hkN, betaCoeff]
      ring_nf
      simp
    · simp [Fin.sum_univ_two, ogmMachine, Matrix.of_apply,
        ogmEta_succ N L g k hk' hkN, eCoeff_succ_eq N L k hkN, betaCoeff]

theorem ogmRealizes (N L x0 g) (k : Fin N) :
    RegisterMachine.dot ((ogmMachine N L).c k) (stateFin N 2 (ogmMachine N L) x0 g ⟨k.val, by omega⟩) = RegisterMachine.target N (ogmW N L) x0 g ⟨k.val, by omega⟩ := by
  have hk : k.val ≤ N := by omega
  have hstate : stateFin N 2 (ogmMachine N L) x0 g ⟨k.val, by omega⟩ = stateNat N 2 (ogmMachine N L) x0 g k.val := rfl
  rw [hstate, stateNat_eq N L x0 g k.val hk, ogmW_target_eq N L x0 g k.val hk]
  simp [RegisterMachine.dot, ogmMachine, e1, Fin.sum_univ_two]

theorem ogmRealizes_terminal (N L x0 g) :
    RegisterMachine.dot ((ogmMachine N L).o) (stateFin N 2 (ogmMachine N L) x0 g ⟨N, by omega⟩) = RegisterMachine.target N (ogmW N L) x0 g ⟨N, by omega⟩ := by
  have hk : N ≤ N := le_rfl
  have hstate : stateFin N 2 (ogmMachine N L) x0 g ⟨N, by omega⟩ = stateNat N 2 (ogmMachine N L) x0 g N := rfl
  rw [hstate, stateNat_eq N L x0 g N hk, ogmW_target_eq N L x0 g N hk]
  simp [RegisterMachine.dot, ogmMachine, e1, Fin.sum_univ_two]

theorem ogmRealizes_init (N L x0 g) :
    stateFin N 2 (ogmMachine N L) x0 g ⟨0, by omega⟩ = fun i => e1 2 i * x0 := by
  have hstate : stateFin N 2 (ogmMachine N L) x0 g ⟨0, by omega⟩ = stateNat N 2 (ogmMachine N L) x0 g 0 := rfl
  rw [hstate, stateNat_eq N L x0 g 0 (by omega)]
  funext i; fin_cases i <;> simp [e1, ogmY, ogmEta]

theorem ogmMachine_realizes (N L) :
    RegisterMachine.Realizes N 2 (ogmW N L) (ogmMachine N L) := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro x0 g k
    exact ogmRealizes N L x0 g k
  · intro x0 g
    exact ogmRealizes_terminal N L x0 g
  · intro x0 g
    exact ogmRealizes_init N L x0 g

theorem ogmHasRealization (N L) : RegisterMachine.HasRealization N (ogmW N L) 2 :=
  ⟨ogmMachine N L, ogmMachine_realizes N L⟩

/-- This same two-register machine implements every query and output in every
finite vector dimension, for arbitrary formal gradient inputs. -/
theorem ogmVectorRealizes (N L) :
    RegisterMachine.VectorRealizes N 2 (ogmW N L) (ogmMachine N L) :=
  (RegisterMachine.vectorRealizes_iff_scalar N 2 (ogmW N L) (ogmMachine N L)).mpr
    (ogmMachine_realizes N L)

end SmoothOGM
