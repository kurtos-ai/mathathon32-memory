module
public import Continuation.Smooth.Attain.Coeff
public import Continuation.Smooth.Attain.Continuity
@[expose] public section
noncomputable section
namespace SmoothAttain

/-!
Scalar quadratic smooth instance, actual one-register risk and its lower bound.
Only the scalar declarations are retained here. Polynomial coefficient identities come
from Continuation.Smooth.Attain.Coeff; recurrence/continuity helpers from Continuation.Smooth.Attain.Continuity.
-/
def scalarObj (lam : ℝ) (xStar x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  lam / 2 * ‖x - xStar‖ ^ 2

def scalarGrad (lam : ℝ) (xStar x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  lam • (x - xStar)

theorem scalar_hasGradientAt (lam : ℝ) (xStar x : EuclideanSpace ℝ (Fin 1)) :
    HasGradientAt (scalarObj lam xStar) (scalarGrad lam xStar x) x := by
  unfold scalarObj scalarGrad
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => lam / 2 * ‖y - xStar‖ ^ 2)
      (lam • innerSL ℝ (x - xStar)) x := by
    have hsub : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => y - xStar)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) x :=
      hasFDerivAt_sub_const xStar
    have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => ‖y - xStar‖ ^ 2)
        (2 • innerSL ℝ (x - xStar)) x := hsub.norm_sq
    have h3 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => lam / 2 * ‖y - xStar‖ ^ 2)
        ((lam / 2 : ℝ) • (2 • innerSL ℝ (x - xStar) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) x := by
      have heq : (fun y : EuclideanSpace ℝ (Fin 1) => lam / 2 * ‖y - xStar‖ ^ 2) =
          ((lam / 2 : ℝ) • fun y => ‖y - xStar‖ ^ 2) := by funext y; simp [smul_eq_mul]
      rw [heq]; exact h2.const_smul (lam / 2)
    have heq2 : (lam / 2 : ℝ) • (2 • innerSL ℝ (x - xStar) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) =
        lam • innerSL ℝ (x - xStar) := by ext y; simp [_root_.smul_apply]; ring
    rwa [heq2] at h3
  have hDual : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1))) (lam • (x - xStar)) =
      lam • innerSL ℝ (x - xStar) := by
    simp only [map_smul, map_sub]
    have h : ∀ (y : EuclideanSpace ℝ (Fin 1)), (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1))) y = innerSL ℝ y := by
      intro y; ext z; simp
    rw [h x, h xStar]
  rw [hDual]; exact h1

theorem scalar_lipschitz {lam : ℝ} (hLam : lam ∈ Set.Icc 0 L) (xStar : EuclideanSpace ℝ (Fin 1)) :
    LipschitzWith ⟨L, hLam.1.trans hLam.2⟩ (scalarGrad lam xStar) := by
  unfold scalarGrad
  apply LipschitzWith.of_dist_le_mul; intro x y
  simp only [dist_eq_norm]
  have h1 : lam • (x - xStar) - lam • (y - xStar) = lam • (x - y) := by
    have : lam • (x - xStar) - lam • (y - xStar) = lam • ((x - xStar) - (y - xStar)) := by rw [← smul_sub]
    rw [this]; congr 1; abel
  rw [h1]
  calc ‖lam • (x - y)‖ = ‖(lam : ℝ)‖ * ‖x - y‖ := norm_smul lam (x - y)
    _ = lam * ‖x - y‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hLam.1]
    _ ≤ L * ‖x - y‖ := mul_le_mul_of_nonneg_right hLam.2 (norm_nonneg _)
    _ = (⟨L, hLam.1.trans hLam.2⟩ : NNReal) * ‖x - y‖ := by simp

theorem scalar_convexOn {lam : ℝ} (hlam : 0 ≤ lam) (xStar : EuclideanSpace ℝ (Fin 1)) :
    ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin 1) => lam / 2 * ‖x - xStar‖ ^ 2) := by
  have h1 : ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin 1) => ‖x - xStar‖) := by
    have h : (fun x : EuclideanSpace ℝ (Fin 1) => ‖x - xStar‖) = (fun z' => dist z' xStar) := by
      funext x; simp [dist_eq_norm]
    rw [h]
    exact convexOn_dist xStar convex_univ
  have h2 : ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin 1) => ‖x - xStar‖ ^ 2) := h1.pow (fun x _ => norm_nonneg _) 2
  have hlam2 : 0 ≤ lam / 2 := by linarith
  have h3 : ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin 1) => (lam / 2) • (‖x - xStar‖ ^ 2)) :=
    ConvexOn.smul hlam2 h2
  have heq : (fun x : EuclideanSpace ℝ (Fin 1) => lam / 2 * ‖x - xStar‖ ^ 2) = (fun x => (lam / 2) • (‖x - xStar‖ ^ 2)) := by
    funext x; simp [smul_eq_mul]
  rw [heq]
  exact h3

def scalarInstance (lam : ℝ) (hLam : lam ∈ Set.Icc (0 : ℝ) L) (xStar x0 : EuclideanSpace ℝ (Fin 1))
    (hNear : ‖x0 - xStar‖ ≤ R) :
    Instance 1 L R where
  f := scalarObj lam xStar
  G := scalarGrad lam xStar
  hasGrad := scalar_hasGradientAt lam xStar
  convex := scalar_convexOn hLam.1 xStar
  lip := ⟨L, hLam.1.trans hLam.2⟩
  lip_eq := rfl
  lipschitz := scalar_lipschitz hLam xStar
  x0 := x0
  xStar := xStar
  isMin := by
    intro y _
    show scalarObj lam xStar xStar ≤ scalarObj lam xStar y
    unfold scalarObj
    have h1 : ‖(xStar : EuclideanSpace ℝ (Fin 1)) - xStar‖ = 0 := by simp
    rw [h1]; simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero]
    have : 0 ≤ lam / 2 * ‖y - xStar‖ ^ 2 := by
      apply mul_nonneg
      · linarith [hLam.1]
      · positivity
    linarith
  near := hNear

-- BETA: scalar error polynomial and loss

def prodRange' {N : ℕ} (α : Fin N → ℝ) (lam : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, if h : i < N then (1 - α ⟨i, h⟩ * lam) else 1

lemma prodRange'_zero {N : ℕ} (α : Fin N → ℝ) (lam : ℝ) : prodRange' α lam 0 = 1 := by
  unfold prodRange'; simp

lemma prodRange'_succ {N : ℕ} (α : Fin N → ℝ) (lam : ℝ) (k : ℕ) (hk : k < N) :
    prodRange' α lam (k+1) = (1 - α ⟨k, hk⟩ * lam) * prodRange' α lam k := by
  unfold prodRange'
  rw [Finset.prod_range_succ]
  have h1 : (if h : k < N then (1 - α ⟨k, h⟩ * lam) else (1 : ℝ)) = (1 - α ⟨k, hk⟩ * lam) := by
    simp [hk]
  rw [h1, mul_comm]

lemma prodRange'_eq_pReal {N : ℕ} (α : Fin N → ℝ) (lam : ℝ) : prodRange' α lam N = pReal α lam := by
  unfold prodRange' pReal
  rw [← Finset.prod_fin_eq_prod_range (fun i : Fin N => 1 - α i * lam)]

theorem scalar_iter_sub_range (lam : ℝ) (hLam : lam ∈ Set.Icc (0 : ℝ) L)
    (xStar x0 : EuclideanSpace ℝ (Fin 1)) (hNear : ‖x0 - xStar‖ ≤ R)
    (α : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar =
      (prodRange' α lam k) • (x0 - xStar) := by
  induction k with
  | zero =>
    simp [iter, prodRange'_zero, scalarInstance]
  | succ k ih =>
    have hk_le : k ≤ N := by omega
    have hk_lt : k < N := by omega
    have ih' := ih hk_le
    have hStep : iter (scalarInstance lam hLam xStar x0 hNear) α (k+1) =
        iter (scalarInstance lam hLam xStar x0 hNear) α k - α ⟨k, hk_lt⟩ • scalarGrad lam xStar (iter (scalarInstance lam hLam xStar x0 hNear) α k) := by
      simp [iter, hk_lt, scalarInstance]
    calc iter (scalarInstance lam hLam xStar x0 hNear) α (k + 1) - xStar
        = iter (scalarInstance lam hLam xStar x0 hNear) α k - α ⟨k, hk_lt⟩ • scalarGrad lam xStar (iter (scalarInstance lam hLam xStar x0 hNear) α k) - xStar := by rw [hStep]
      _ = iter (scalarInstance lam hLam xStar x0 hNear) α k - α ⟨k, hk_lt⟩ • (lam • (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar)) - xStar := by simp only [scalarGrad]
      _ = (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar) - (α ⟨k, hk_lt⟩ * lam) • (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar) := by
            have hsmul : α ⟨k, hk_lt⟩ • (lam • (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar)) = (α ⟨k, hk_lt⟩ * lam) • (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar) := by
              rw [smul_smul, mul_comm]
            rw [hsmul]
            have hAbel : iter (scalarInstance lam hLam xStar x0 hNear) α k - (α ⟨k, hk_lt⟩ * lam) • (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar) - xStar =
                (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar) - (α ⟨k, hk_lt⟩ * lam) • (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar) := by abel
            rw [hAbel]
      _ = (1 - α ⟨k, hk_lt⟩ * lam) • (iter (scalarInstance lam hLam xStar x0 hNear) α k - xStar) := by
            rw [sub_smul, one_smul]
      _ = (1 - α ⟨k, hk_lt⟩ * lam) • ((prodRange' α lam k) • (x0 - xStar)) := by rw [ih']
      _ = ((1 - α ⟨k, hk_lt⟩ * lam) * prodRange' α lam k) • (x0 - xStar) := by rw [mul_smul]
      _ = prodRange' α lam (k+1) • (x0 - xStar) := by rw [prodRange'_succ α lam k hk_lt]

theorem scalar_terminalLoss_eq (lam : ℝ) (hLam : lam ∈ Set.Icc (0 : ℝ) L)
    (xStar x0 : EuclideanSpace ℝ (Fin 1)) (hNear : ‖x0 - xStar‖ ≤ R)
    (α : Fin N → ℝ) :
    terminalLoss (scalarInstance lam hLam xStar x0 hNear) α =
      lam / 2 * (pReal α lam) ^ 2 * ‖x0 - xStar‖ ^ 2 := by
  have hIter : iter (scalarInstance lam hLam xStar x0 hNear) α N - xStar =
      (pReal α lam) • (x0 - xStar) := by
    have h := scalar_iter_sub_range lam hLam xStar x0 hNear α N (le_refl N)
    rw [prodRange'_eq_pReal] at h
    exact h
  show (scalarInstance lam hLam xStar x0 hNear).f (iter (scalarInstance lam hLam xStar x0 hNear) α N) - (scalarInstance lam hLam xStar x0 hNear).f (scalarInstance lam hLam xStar x0 hNear).xStar = _
  change scalarObj lam xStar (iter (scalarInstance lam hLam xStar x0 hNear) α N) - scalarObj lam xStar xStar = _
  have h1 : scalarObj lam xStar (iter (scalarInstance lam hLam xStar x0 hNear) α N) = lam / 2 * ‖iter (scalarInstance lam hLam xStar x0 hNear) α N - xStar‖ ^ 2 := rfl
  have h2 : scalarObj lam xStar xStar = 0 := by unfold scalarObj; simp
  rw [h1, h2, sub_zero, hIter]
  have hNorm : ‖pReal α lam • (x0 - xStar)‖ ^ 2 = (pReal α lam) ^ 2 * ‖x0 - xStar‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    have : |pReal α lam| ^ 2 = (pReal α lam) ^ 2 := sq_abs _
    rw [this]
  rw [hNorm]
  ring

-- Helper to build extremal point with norm R
def mkX (R : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single (0 : Fin 1) R

lemma norm_mkX (R : ℝ) : ‖mkX R‖ = ‖R‖ := by
  unfold mkX EuclideanSpace.single
  exact PiLp.norm_single (p:=2) (β:=fun _ : Fin 1 => ℝ) (i:=(0 : Fin 1)) (b:=R)

lemma norm_mkX_eq_abs (R : ℝ) : ‖mkX R‖ = |R| := by
  rw [norm_mkX, Real.norm_eq_abs]

lemma norm_mkX_eq_R (R : ℝ) (hR : 0 ≤ R) : ‖mkX R‖ = R := by
  rw [norm_mkX_eq_abs, abs_of_nonneg hR]

lemma norm_sub_mkX_zero (R : ℝ) (hR : 0 ≤ R) : ‖mkX R - (0 : EuclideanSpace ℝ (Fin 1))‖ = R := by
  simp only [sub_zero, norm_mkX_eq_R R hR]

def scalarInstanceExtremal {L R : ℝ} (lam : ℝ) (hLam : lam ∈ Set.Icc (0 : ℝ) L) (hR : 0 ≤ R) :
    Instance 1 L R :=
  scalarInstance lam hLam 0 (mkX R) ((norm_sub_mkX_zero R hR).le)

theorem scalar_extremal_loss {N : ℕ} {L R : ℝ} (hR : 0 ≤ R) (lam : ℝ) (hLam : lam ∈ Set.Icc (0 : ℝ) L) (α : Fin N → ℝ) :
    terminalLoss (scalarInstanceExtremal (L:=L) lam hLam hR) α = R ^ 2 / 2 * (lam * (pReal α lam) ^ 2) := by
  have h : terminalLoss (scalarInstance lam hLam 0 (mkX R) ((norm_sub_mkX_zero R hR).le)) α = lam / 2 * (pReal α lam) ^ 2 * ‖mkX R - 0‖ ^ 2 :=
    scalar_terminalLoss_eq lam hLam 0 (mkX R) ((norm_sub_mkX_zero R hR).le) α
  have h2 : (scalarInstanceExtremal (L:=L) lam hLam hR) = scalarInstance lam hLam 0 (mkX R) ((norm_sub_mkX_zero R hR).le) := rfl
  rw [h2, h, norm_sub_mkX_zero R hR]
  ring

-- Real-to-EReal continuity
lemma continuous_real_toEReal : Continuous (Real.toEReal) := by
  unfold Real.toEReal
  exact WithBot.continuous_coe.comp WithTop.continuous_coe

theorem terminalLoss_ereal_lsc (I : Instance n L R) :
    LowerSemicontinuous (fun α : Fin N → ℝ => (terminalLoss I α : EReal)) := by
  have hMon : Monotone (Real.toEReal) := EReal.coe_strictMono.monotone
  have hCont : Continuous (Real.toEReal) := continuous_real_toEReal
  have hLSC : LowerSemicontinuous (fun α : Fin N → ℝ => terminalLoss I α) := terminalLoss_lsc I
  exact hCont.comp_lowerSemicontinuous hLSC hMon

-- ALL-DIMENSION INSTANCE TYPE and EReal RISK
def AllInstances (L R : ℝ) := Σ (n : {n : ℕ // 0 < n}), Instance n.val L R

def risk0 {N : ℕ} (L R : ℝ) (α : Fin N → ℝ) : EReal :=
  ⨆ (I : AllInstances L R), (terminalLoss I.2 α : EReal)

theorem risk0_lsc {N : ℕ} (L R : ℝ) : LowerSemicontinuous (risk0 (N:=N) L R) := by
  unfold risk0
  exact lowerSemicontinuous_iSup (fun I => terminalLoss_ereal_lsc I.2)

-- BETA lower bound: risk dominates scalar quadratic loss
theorem risk0_ge_scalar {N : ℕ} {L R : ℝ} (hR : 0 ≤ R) (lam : ℝ) (hLam : lam ∈ Set.Icc (0 : ℝ) L) (α : Fin N → ℝ) :
    ((R ^ 2 / 2 * (lam * (pReal α lam) ^ 2) : ℝ) : EReal) ≤ risk0 (N:=N) L R α := by
  unfold risk0
  let hInst : AllInstances L R := ⟨⟨1, by omega⟩, scalarInstanceExtremal (L:=L) lam hLam hR⟩
  have hLe : (terminalLoss hInst.2 α : EReal) ≤ ⨆ (I : AllInstances L R), (terminalLoss I.2 α : EReal) :=
    le_iSup (fun I : AllInstances L R => (terminalLoss I.2 α : EReal)) hInst
  have hEq : (terminalLoss hInst.2 α : EReal) = ((R ^ 2 / 2 * (lam * (pReal α lam) ^ 2) : ℝ) : EReal) := by
    have : hInst.2 = scalarInstanceExtremal (L:=L) lam hLam hR := rfl
    rw [this, scalar_extremal_loss hR lam hLam α]
  rw [← hEq]
  exact hLe


end SmoothAttain
