module
public import RealizationCore.RegisterMachine
public import Mathlib
@[expose] public section
noncomputable section
namespace RegisterMachine

open Matrix Finset

-- Part 1: q_k = state on ones with zero gradients

def qFin (N s : ℕ) (M : Machine N s) (k : Fin (N+1)) : Fin s → ℝ :=
  stateFin N s M 1 (fun _ => (0:ℝ)) k

lemma target_zero_grad (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : ℝ) (k : Fin (N+1)) :
    target N W x0 (fun _ => (0:ℝ)) k = x0 := by
  simp [target]

lemma qFin_zero_eq_e1 (N s : ℕ) (M : Machine N s) :
    qFin N s M ⟨0, by omega⟩ = e1 s := by
  funext i
  simp [qFin, stateFin, stateNat]

lemma dot_c_qFin (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s)
    (hR : Realizes N s W M) (k : Fin N) :
    dot (M.c k) (qFin N s M ⟨k.val, by omega⟩) = 1 := by
  have h := hR.2.1 1 (fun _ => (0:ℝ)) k
  simp only [target_zero_grad] at h
  exact h

lemma dot_o_qFin (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s)
    (hR : Realizes N s W M) :
    dot M.o (qFin N s M ⟨N, by omega⟩) = 1 := by
  have h := hR.2.2.1 1 (fun _ => (0:ℝ))
  simp only [target_zero_grad] at h
  exact h

lemma F_mul_qFin (N s : ℕ) (M : Machine N s) (k : ℕ) (hk : k < N) :
    M.F ⟨k, hk⟩ *ᵥ qFin N s M ⟨k, by omega⟩ = qFin N s M ⟨k+1, by omega⟩ := by
  simp only [qFin, stateFin]
  have h := stateNat_succ N s M 1 (fun _ => (0:ℝ)) k hk
  simp only [h]
  funext i
  simp [Matrix.mulVec, dotProduct]

-- Part 2: abstract invertible matrix construction

def onesVec (s : ℕ) : Fin s → ℝ := fun _ => 1

def dotLinear (s : ℕ) (c : Fin s → ℝ) : (Fin s → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin s, c i • LinearMap.proj (R:=ℝ) (φ:=fun _ : Fin s => ℝ) i

lemma dotLinear_apply_eq_dot (s : ℕ) (c v : Fin s → ℝ) :
    dotLinear s c v = dot c v := by
  simp [dotLinear, dot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]

def e1Linear (s : ℕ) : (Fin s → ℝ) →ₗ[ℝ] ℝ := dotLinear s (e1 s)

lemma e1_dot_ones {s : ℕ} (hs : 0 < s) : dot (e1 s) (onesVec s) = 1 := by
  simp only [dot, e1, onesVec]
  have h : ∀ i : Fin s, (if i.val = 0 then (1:ℝ) else 0) * (1:ℝ) = if i = ⟨0, hs⟩ then 1 else 0 := by
    intro i
    by_cases hi : i.val = 0
    · have he : i = ⟨0, hs⟩ := Fin.ext hi
      simp [he]
    · have hne : i ≠ ⟨0, hs⟩ := by intro he; apply hi; rw [he]
      simp [hi, hne]
  simp only [h]
  simp

lemma e1Linear_apply_onesVec {s : ℕ} (hs : 0 < s) : e1Linear s (onesVec s) = 1 := by
  simp only [e1Linear, dotLinear_apply_eq_dot, e1_dot_ones hs]

lemma dotLinear_ne_zero_of_dot_eq_one {s : ℕ} {c q : Fin s → ℝ} (h : dot c q = 1) :
    dotLinear s c ≠ 0 := by
  intro h0
  have : dot c q = 0 := by
    have h1 : dotLinear s c q = 0 := by rw [h0]; rfl
    rwa [dotLinear_apply_eq_dot] at h1
  linarith

lemma e1Linear_ne_zero {s : ℕ} (hs : 0 < s) : e1Linear s ≠ 0 := by
  intro h0
  have h1 : e1Linear s (onesVec s) = 0 := by rw [h0]; rfl
  have h2 : e1Linear s (onesVec s) = 1 := e1Linear_apply_onesVec hs
  linarith

lemma finrank_fin_fun_real (s : ℕ) : Module.finrank ℝ (Fin s → ℝ) = s := by
  rw [Module.finrank_fin_fun]

lemma ker_finrank_of_dot_eq_one {s : ℕ} {c q : Fin s → ℝ} (hs : 0 < s) (h : dot c q = 1) :
    Module.finrank ℝ (LinearMap.ker (dotLinear s c)) = s - 1 := by
  have hne : dotLinear s c ≠ 0 := dotLinear_ne_zero_of_dot_eq_one h
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero (K:=ℝ) (V₁:=Fin s → ℝ) hne
  rw [finrank_fin_fun_real] at h1
  omega

lemma ker_finrank_e1Linear {s : ℕ} (hs : 0 < s) :
    Module.finrank ℝ (LinearMap.ker (e1Linear s)) = s - 1 := by
  have hne : e1Linear s ≠ 0 := e1Linear_ne_zero hs
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero (K:=ℝ) (V₁:=Fin s → ℝ) hne
  rw [finrank_fin_fun_real] at h1
  omega

def kerEquiv {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    (LinearMap.ker (dotLinear s c) ≃ₗ[ℝ] LinearMap.ker (e1Linear s)) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [ker_finrank_of_dot_eq_one hs h, ker_finrank_e1Linear hs]
  )

def projCMap {s : ℕ} (c q : Fin s → ℝ) : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
  LinearMap.id - (dotLinear s c).smulRight q

def projEMap {s : ℕ} : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
  LinearMap.id - (e1Linear s).smulRight (onesVec s)

lemma projCMap_apply' {s : ℕ} (c q v : Fin s → ℝ) :
    projCMap c q v = v - (dotLinear s c v) • q := by
  simp [projCMap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]

lemma projEMap_apply' {s : ℕ} (v : Fin s → ℝ) :
    projEMap (s:=s) v = v - (e1Linear s v) • onesVec s := by
  simp [projEMap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]

lemma dotLinear_projCMap {s : ℕ} (c q : Fin s → ℝ) (h : dot c q = 1) (v : Fin s → ℝ) :
    dotLinear s c (projCMap c q v) = 0 := by
  have hq : dotLinear s c q = 1 := by rw [dotLinear_apply_eq_dot, h]
  calc dotLinear s c (projCMap c q v)
      = dotLinear s c (v - (dotLinear s c v) • q) := by rw [projCMap_apply']
    _ = dotLinear s c v - dotLinear s c ((dotLinear s c v) • q) := by rw [map_sub]
    _ = dotLinear s c v - (dotLinear s c v) • dotLinear s c q := by rw [LinearMap.map_smul]
    _ = dotLinear s c v - (dotLinear s c v) * 1 := by rw [hq, smul_eq_mul]
    _ = 0 := by ring

lemma e1Linear_projEMap {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ) :
    e1Linear s (projEMap v) = 0 := by
  have hq : e1Linear s (onesVec s) = 1 := e1Linear_apply_onesVec hs
  calc e1Linear s (projEMap v)
      = e1Linear s (v - (e1Linear s v) • onesVec s) := by rw [projEMap_apply']
    _ = e1Linear s v - e1Linear s ((e1Linear s v) • onesVec s) := by rw [map_sub]
    _ = e1Linear s v - (e1Linear s v) • e1Linear s (onesVec s) := by rw [LinearMap.map_smul]
    _ = e1Linear s v - (e1Linear s v) * 1 := by rw [hq, smul_eq_mul]
    _ = 0 := by ring

def projToKerC {s : ℕ} (c q : Fin s → ℝ) (h : dot c q = 1) :
    (Fin s → ℝ) →ₗ[ℝ] ↥(LinearMap.ker (dotLinear s c)) :=
  LinearMap.codRestrict (LinearMap.ker (dotLinear s c)) (projCMap c q) (fun v => by
    rw [LinearMap.mem_ker, dotLinear_projCMap c q h v])

def projToKerE {s : ℕ} (hs : 0 < s) :
    (Fin s → ℝ) →ₗ[ℝ] ↥(LinearMap.ker (e1Linear s)) :=
  LinearMap.codRestrict (LinearMap.ker (e1Linear s)) projEMap (fun v => by
    rw [LinearMap.mem_ker, e1Linear_projEMap hs v])

def A_lin {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
  (dotLinear s c).smulRight (onesVec s) + (Submodule.subtype (LinearMap.ker (e1Linear s))).comp ((kerEquiv hs h).toLinearMap.comp (projToKerC c q h))

lemma A_lin_apply {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    A_lin hs h v = (dotLinear s c v) • onesVec s + ↑(kerEquiv hs h (projToKerC c q h v)) := by
  simp [A_lin, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]

def B_lin {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
  (e1Linear s).smulRight q + (Submodule.subtype (LinearMap.ker (dotLinear s c))).comp ((kerEquiv hs h).symm.toLinearMap.comp (projToKerE hs))

lemma B_lin_apply {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (w : Fin s → ℝ) :
    B_lin hs h w = (e1Linear s w) • q + ↑((kerEquiv hs h).symm (projToKerE hs w)) := by
  simp [B_lin, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]

lemma A_lin_q_eq_ones {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    A_lin hs h q = onesVec s := by
  have h1 : projToKerC c q h q = 0 := by
    apply Subtype.ext
    simp [projToKerC, projCMap_apply', dotLinear_apply_eq_dot, h]
  have h2 : dotLinear s c q = 1 := by rw [dotLinear_apply_eq_dot, h]
  calc A_lin hs h q
      = (dotLinear s c q) • onesVec s + ↑(kerEquiv hs h (projToKerC c q h q)) := by rw [A_lin_apply]
    _ = (1 : ℝ) • onesVec s + ↑(kerEquiv hs h (0 : ↥(LinearMap.ker (dotLinear s c)))) := by rw [h2, h1]
    _ = onesVec s + (0 : Fin s → ℝ) := by simp [map_zero]
    _ = onesVec s := by simp

lemma e1Linear_A_lin {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    e1Linear s (A_lin hs h v) = dotLinear s c v := by
  rw [A_lin_apply]
  simp only [map_add, LinearMap.map_smul, e1Linear_apply_onesVec hs]
  have h0 : e1Linear s (↑(kerEquiv hs h (projToKerC c q h v)) : Fin s → ℝ) = 0 := by
    have : (↑(kerEquiv hs h (projToKerC c q h v)) : Fin s → ℝ) ∈ LinearMap.ker (e1Linear s) :=
      (kerEquiv hs h (projToKerC c q h v)).property
    rwa [LinearMap.mem_ker] at this
  simp [h0, smul_eq_mul, mul_one]

lemma projToKerE_A_lin {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    projToKerE hs (A_lin hs h v) = kerEquiv hs h (projToKerC c q h v) := by
  apply Subtype.ext
  have h1 : A_lin hs h v = (dotLinear s c v) • onesVec s + ↑(kerEquiv hs h (projToKerC c q h v)) := A_lin_apply hs h v
  have h2 : e1Linear s (A_lin hs h v) = dotLinear s c v := e1Linear_A_lin hs h v
  calc (projToKerE hs (A_lin hs h v) : Fin s → ℝ)
      = projEMap (A_lin hs h v) := by simp [projToKerE]
    _ = (A_lin hs h v) - (e1Linear s (A_lin hs h v)) • onesVec s := by rw [projEMap_apply']
    _ = ((dotLinear s c v) • onesVec s + ↑(kerEquiv hs h (projToKerC c q h v))) - (dotLinear s c v) • onesVec s := by
          rw [h2, h1]
    _ = ↑(kerEquiv hs h (projToKerC c q h v)) := by abel

lemma B_lin_A_lin {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    B_lin hs h (A_lin hs h v) = v := by
  have h1 : e1Linear s (A_lin hs h v) = dotLinear s c v := e1Linear_A_lin hs h v
  have h2 : projToKerE hs (A_lin hs h v) = kerEquiv hs h (projToKerC c q h v) := projToKerE_A_lin hs h v
  calc B_lin hs h (A_lin hs h v)
      = (e1Linear s (A_lin hs h v)) • q + ↑((kerEquiv hs h).symm (projToKerE hs (A_lin hs h v))) := by rw [B_lin_apply]
    _ = (dotLinear s c v) • q + ↑((kerEquiv hs h).symm (kerEquiv hs h (projToKerC c q h v))) := by rw [h1, h2]
    _ = (dotLinear s c v) • q + ↑(projToKerC c q h v) := by rw [LinearEquiv.symm_apply_apply]
    _ = (dotLinear s c v) • q + (v - (dotLinear s c v) • q) := by
        have : (↑(projToKerC c q h v) : Fin s → ℝ) = projCMap c q v := by simp [projToKerC]
        rw [this, projCMap_apply']
    _ = v := by abel

lemma A_lin_B_lin {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (w : Fin s → ℝ) :
    A_lin hs h (B_lin hs h w) = w := by
  have h1 : dotLinear s c (B_lin hs h w) = e1Linear s w := by
    have h0 : dotLinear s c (↑((kerEquiv hs h).symm (projToKerE hs w)) : Fin s → ℝ) = 0 := by
      have : (↑((kerEquiv hs h).symm (projToKerE hs w)) : Fin s → ℝ) ∈ LinearMap.ker (dotLinear s c) :=
        ((kerEquiv hs h).symm (projToKerE hs w)).property
      rwa [LinearMap.mem_ker] at this
    calc dotLinear s c (B_lin hs h w)
        = dotLinear s c ((e1Linear s w) • q + ↑((kerEquiv hs h).symm (projToKerE hs w))) := by rw [B_lin_apply]
      _ = (e1Linear s w) • dotLinear s c q + dotLinear s c (↑((kerEquiv hs h).symm (projToKerE hs w))) := by rw [map_add, LinearMap.map_smul]
      _ = (e1Linear s w) * 1 + 0 := by rw [dotLinear_apply_eq_dot, h, h0, smul_eq_mul]
      _ = e1Linear s w := by ring
  have h2 : projToKerC c q h (B_lin hs h w) = (kerEquiv hs h).symm (projToKerE hs w) := by
    apply Subtype.ext
    calc (projToKerC c q h (B_lin hs h w) : Fin s → ℝ)
        = projCMap c q (B_lin hs h w) := by simp [projToKerC]
      _ = (B_lin hs h w) - (dotLinear s c (B_lin hs h w)) • q := by rw [projCMap_apply']
      _ = (B_lin hs h w) - (e1Linear s w) • q := by rw [h1]
      _ = ((e1Linear s w) • q + ↑((kerEquiv hs h).symm (projToKerE hs w))) - (e1Linear s w) • q := by rw [B_lin_apply]
      _ = ↑((kerEquiv hs h).symm (projToKerE hs w)) := by abel
  calc A_lin hs h (B_lin hs h w)
      = (dotLinear s c (B_lin hs h w)) • onesVec s + ↑(kerEquiv hs h (projToKerC c q h (B_lin hs h w))) := by rw [A_lin_apply]
    _ = (e1Linear s w) • onesVec s + ↑(kerEquiv hs h ((kerEquiv hs h).symm (projToKerE hs w))) := by rw [h1, h2]
    _ = (e1Linear s w) • onesVec s + ↑(projToKerE hs w) := by rw [LinearEquiv.apply_symm_apply]
    _ = (e1Linear s w) • onesVec s + (w - (e1Linear s w) • onesVec s) := by
        have : (↑(projToKerE hs w) : Fin s → ℝ) = projEMap w := by simp [projToKerE]
        rw [this, projEMap_apply']
    _ = w := by abel

def A_equiv {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) : (Fin s → ℝ) ≃ₗ[ℝ] (Fin s → ℝ) :=
  LinearEquiv.ofLinearMap (A_lin hs h) (B_lin hs h)
    (LinearMap.ext fun w => A_lin_B_lin hs h w) (LinearMap.ext fun v => B_lin_A_lin hs h v)

def A_mat {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) : Matrix (Fin s) (Fin s) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin s)) (Pi.basisFun ℝ (Fin s)) (A_lin hs h)

def A_mat_inv {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) : Matrix (Fin s) (Fin s) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin s)) (Pi.basisFun ℝ (Fin s)) (B_lin hs h)

lemma A_mat_mulVec {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    A_mat hs h *ᵥ v = A_lin hs h v := by
  have h1 : (Pi.basisFun ℝ (Fin s)).repr v = v := by ext i; simp [Pi.basisFun]
  have h2 : (Pi.basisFun ℝ (Fin s)).repr (A_lin hs h v) = A_lin hs h v := by ext i; simp [Pi.basisFun]
  have h3 := LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin s)) (Pi.basisFun ℝ (Fin s)) (A_lin hs h) v
  rw [h1, h2] at h3
  exact h3

lemma A_mat_inv_mulVec {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    A_mat_inv hs h *ᵥ v = B_lin hs h v := by
  have h1 : (Pi.basisFun ℝ (Fin s)).repr v = v := by ext i; simp [Pi.basisFun]
  have h2 : (Pi.basisFun ℝ (Fin s)).repr (B_lin hs h v) = B_lin hs h v := by ext i; simp [Pi.basisFun]
  have h3 := LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin s)) (Pi.basisFun ℝ (Fin s)) (B_lin hs h) v
  rw [h1, h2] at h3
  exact h3

lemma A_mat_q_eq_ones {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    A_mat hs h *ᵥ q = onesVec s := by
  rw [A_mat_mulVec, A_lin_q_eq_ones]

lemma e1_dot_A_mat {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ) :
    dot (e1 s) (A_mat hs h *ᵥ v) = dot c v := by
  rw [A_mat_mulVec]
  have h1 : dot (e1 s) (A_lin hs h v) = e1Linear s (A_lin hs h v) := by
    simp [e1Linear, dotLinear_apply_eq_dot]
  rw [h1, e1Linear_A_lin hs h v, dotLinear_apply_eq_dot]

lemma B_lin_ones_eq_q {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    B_lin hs h (onesVec s) = q := by
  have h1 : e1Linear s (onesVec s) = 1 := e1Linear_apply_onesVec hs
  have h2 : projToKerE hs (onesVec s) = 0 := by
    apply Subtype.ext
    simp [projToKerE, projEMap_apply', h1]
  simp [B_lin_apply, h1, h2]

lemma A_mat_inv_ones_eq_q {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    A_mat_inv hs h *ᵥ onesVec s = q := by
  rw [A_mat_inv_mulVec, B_lin_ones_eq_q hs h]

lemma A_equiv_q_eq_ones {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    A_equiv hs h q = onesVec s := A_lin_q_eq_ones hs h

lemma A_equiv_symm_ones_eq_q {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    (A_equiv hs h).symm (onesVec s) = q := B_lin_ones_eq_q hs h

lemma e1_comp_A_equiv {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) :
    (e1Linear s).comp (A_equiv hs h : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ)) = dotLinear s c := by
  apply LinearMap.ext
  intro v
  exact e1Linear_A_lin hs h v

lemma A_equiv_maps_ker {s : ℕ} (hs : 0 < s) {c q : Fin s → ℝ} (h : dot c q = 1) (v : Fin s → ℝ)
    (hv : dotLinear s c v = 0) : e1Linear s (A_equiv hs h v) = 0 := by
  have h1 : e1Linear s (A_equiv hs h v) = dotLinear s c v := e1Linear_A_lin hs h v
  rw [h1, hv]


end RegisterMachine
