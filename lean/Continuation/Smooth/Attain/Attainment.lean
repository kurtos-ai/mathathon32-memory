module
public import Continuation.Smooth.Attain.Coercivity
public import Continuation.Smooth.Attain.ScalarRisk
public import Continuation.Smooth.Necessary
public import Continuation.Smooth.ActualInterpolation
public import Continuation.Smooth.Attain.Coeff
public import Continuation.Smooth.Attain.Continuity
@[expose] public section
noncomputable section
namespace SmoothAttain

open Real

theorem sublevel_pReal_sq_le {N : ℕ} {L R C : ℝ} (hL : 0 < L) (hR : 0 < R) {β : Fin N → ℝ}
    (hRisk : risk0 L R β ≤ (C : EReal)) {lam : ℝ} (hlam : lam ∈ Set.Icc (L/2) L) :
    (pReal β lam) ^ 2 ≤ 4 * C / (L * R ^ 2) := by
  have hR0 : (0 : ℝ) ≤ R := le_of_lt hR
  have hlam0 : lam ∈ Set.Icc (0 : ℝ) L := by
    constructor
    · have h1 : 0 ≤ L / 2 := by linarith
      have h2 : L / 2 ≤ lam := hlam.1
      linarith
    · exact hlam.2
  have h_ge : ((R ^ 2 / 2 * (lam * (pReal β lam) ^ 2) : ℝ) : EReal) ≤ risk0 L R β :=
    risk0_ge_scalar hR0 lam hlam0 β
  have h_le : ((R ^ 2 / 2 * (lam * (pReal β lam) ^ 2) : ℝ) : EReal) ≤ (C : EReal) :=
    le_trans h_ge hRisk
  have h_real_le : R ^ 2 / 2 * (lam * (pReal β lam) ^ 2) ≤ C := by
    rwa [EReal.coe_le_coe_iff] at h_le
  have hR2div_nonneg : 0 ≤ R ^ 2 / 2 := by positivity
  have hp2_nonneg : 0 ≤ (pReal β lam) ^ 2 := sq_nonneg _
  have h_mono : R ^ 2 / 2 * (L / 2 * (pReal β lam) ^ 2) ≤ R ^ 2 / 2 * (lam * (pReal β lam) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hR2div_nonneg
    apply mul_le_mul_of_nonneg_right hlam.1 hp2_nonneg
  have h_LR_le : R ^ 2 / 2 * (L / 2 * (pReal β lam) ^ 2) ≤ C := le_trans h_mono h_real_le
  have h_left_eq : R ^ 2 / 2 * (L / 2 * (pReal β lam) ^ 2) = L * R ^ 2 / 4 * (pReal β lam) ^ 2 := by ring
  rw [h_left_eq] at h_LR_le
  have hLR4pos : 0 < L * R ^ 2 / 4 := by positivity
  have h_div : (pReal β lam) ^ 2 ≤ C / (L * R ^ 2 / 4) := by
    rw [le_div_iff₀ hLR4pos]
    have : (pReal β lam) ^ 2 * (L * R ^ 2 / 4) = L * R ^ 2 / 4 * (pReal β lam) ^ 2 := by ring
    rw [this]
    exact h_LR_le
  have h_four_eq : C / (L * R ^ 2 / 4) = 4 * C / (L * R ^ 2) := by field_simp
  rw [h_four_eq] at h_div
  exact h_div

lemma risk0_nonneg {N : ℕ} (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (α : Fin N → ℝ) :
    (0 : EReal) ≤ risk0 L R α := by
  have hL0 : (L/2) ∈ Set.Icc (0 : ℝ) L := by constructor <;> linarith
  let I : AllInstances L R := ⟨⟨1, by omega⟩, scalarInstanceExtremal (L:=L) (L/2) hL0 hR⟩
  have h1 : (0 : EReal) ≤ (terminalLoss I.2 α : EReal) := by
    have h_nn : 0 ≤ terminalLoss I.2 α := by
      have hmin : IsMinOn I.2.f Set.univ I.2.xStar := I.2.isMin
      have h_le : I.2.f I.2.xStar ≤ I.2.f (iter I.2 α N) := hmin (Set.mem_univ _)
      unfold terminalLoss
      linarith
    exact EReal.coe_nonneg.mpr h_nn
  have h2 : (terminalLoss I.2 α : EReal) ≤ risk0 L R α := le_iSup (fun I : AllInstances L R => (terminalLoss I.2 α : EReal)) I
  exact le_trans h1 h2

theorem sublevel_pReal_abs_le {N : ℕ} {L R C : ℝ} (hL : 0 < L) (hR : 0 < R) (hC : 0 ≤ C) {β : Fin N → ℝ}
    (hRisk : risk0 L R β ≤ (C : EReal)) {lam : ℝ} (hlam : lam ∈ Set.Icc (L/2) L) :
    |pReal β lam| ≤ Real.sqrt (4 * C / (L * R ^ 2)) := by
  have h_sq := sublevel_pReal_sq_le hL hR hRisk hlam
  exact Real.abs_le_sqrt h_sq

theorem sublevel_sum_sq_le_B {N : ℕ} {L R C : ℝ} (hL : 0 < L) (hR : 0 < R) {β : Fin N → ℝ}
    (hRisk : risk0 L R β ≤ (C : EReal)) :
    ∑ i : Fin N, (β i) ^ 2 ≤ B_bound N L (Real.sqrt (4 * C / (L * R ^ 2))) hL := by
  have hS_nonneg : 0 ≤ Real.sqrt (4 * C / (L * R ^ 2)) := Real.sqrt_nonneg _
  by_cases hC : 0 ≤ C
  · have h_abs : ∀ m : Fin N, |pReal β (lam N L m)| ≤ Real.sqrt (4 * C / (L * R ^ 2)) := by
      intro m
      have hlam_mem : lam N L m ∈ Set.Icc (L/2) L := lam_mem_Icc hL m
      exact sublevel_pReal_abs_le hL hR hC hRisk hlam_mem
    exact sumAlphaSq_le_B_bound hL hS_nonneg h_abs
  · push_neg at hC
    have h_risk_nonneg : (0 : EReal) ≤ risk0 L R β := risk0_nonneg L R hL (le_of_lt hR) β
    have hC_EReal_lt : (C : EReal) < (0 : EReal) := by
      have h0 : (C : EReal) < (0 : ℝ) := EReal.coe_lt_coe hC
      have h_eq : ((0 : ℝ) : EReal) = 0 := by simp
      rw [h_eq] at h0
      exact h0
    have h_lt : risk0 L R β < (0 : EReal) := lt_of_le_of_lt hRisk hC_EReal_lt
    have h_false : False := (not_lt.mpr h_risk_nonneg) h_lt
    exact False.elim h_false

def finiteSublevel (N : ℕ) (L R C : ℝ) : Set (Fin N → ℝ) :=
  {α | risk0 L R α ≤ (C : EReal)}

lemma finiteSublevel_closed {N : ℕ} (L R C : ℝ) : IsClosed (finiteSublevel N L R C) := by
  unfold finiteSublevel
  have h_lsc : LowerSemicontinuous (risk0 (N:=N) L R) := risk0_lsc L R
  exact h_lsc.isClosed_preimage C

lemma norm_bound_of_sum_sq_le {N : ℕ} {α : Fin N → ℝ} {B : ℝ} (h_sum : ∑ i : Fin N, (α i) ^ 2 ≤ B) :
    ‖α‖ ≤ Real.sqrt B + 1 := by
  have h_each : ∀ i : Fin N, |α i| ≤ Real.sqrt B := by
    intro i
    have h_i : (α i) ^ 2 ≤ B := by
      have h_le : (α i) ^ 2 ≤ ∑ j : Fin N, (α j) ^ 2 := by
        apply Finset.single_le_sum (fun j _ => sq_nonneg (α j)) (Finset.mem_univ i)
      linarith
    exact Real.abs_le_sqrt h_i
  have h_norm_le : ‖α‖ ≤ Real.sqrt B + 1 := by
    by_cases hN : N = 0
    · have h_zero : α = 0 := by
        funext i
        have : IsEmpty (Fin N) := by rw [hN]; infer_instance
        exact this.elim i
      have : ‖α‖ = ‖(0 : Fin N → ℝ)‖ := by rw [h_zero]
      simp [this]
      positivity
    · have h_le_sqrt : ‖α‖ ≤ Real.sqrt B := by
        have h_forall : ∀ i : Fin N, ‖α i‖ ≤ Real.sqrt B := by
          intro i
          have h1 : |α i| ≤ Real.sqrt B := h_each i
          have h2 : ‖α i‖ = |α i| := Real.norm_eq_abs (α i)
          rw [h2]
          exact h1
        rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
        exact h_forall
      linarith
  exact h_norm_le

lemma finiteSublevel_bounded {N : ℕ} (L R C : ℝ) (hL : 0 < L) (hR : 0 < R) :
    Bornology.IsBounded (finiteSublevel N L R C) := by
  let B := B_bound N L (Real.sqrt (4 * C / (L * R ^ 2))) hL
  have h_bound : ∀ α ∈ finiteSublevel N L R C, ∑ i : Fin N, (α i) ^ 2 ≤ B := by
    intro α hα
    unfold finiteSublevel at hα
    exact sublevel_sum_sq_le_B hL hR hα
  have h_norm : ∀ α ∈ finiteSublevel N L R C, ‖α‖ ≤ Real.sqrt B + 1 := by
    intro α hα
    have h_sum := h_bound α hα
    exact norm_bound_of_sum_sq_le h_sum
  rw [isBounded_iff_forall_norm_le]
  exact ⟨Real.sqrt B + 1, fun x hx => h_norm x hx⟩

theorem finiteSublevel_isCompact {N : ℕ} (L R C : ℝ) (hL : 0 < L) (hR : 0 < R) :
    IsCompact (finiteSublevel N L R C) := by
  have h_closed : IsClosed (finiteSublevel N L R C) := finiteSublevel_closed (N:=N) L R C
  have h_bounded : Bornology.IsBounded (finiteSublevel N L R C) := finiteSublevel_bounded (N:=N) L R C hL hR
  exact Metric.isCompact_of_isClosed_isBounded h_closed h_bounded

lemma iter_zero_aux {n N : ℕ} {L R : ℝ} (I : Instance n L R) (α : Fin N → ℝ) (hα : ∀ k : Fin N, α k = 0) (k : ℕ) (hk : k ≤ N) :
    iter I α k = I.x0 := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have hk_le : k ≤ N := by omega
    have ih_eq := ih hk_le
    have h_lt : k < N := by omega
    have hαk : α ⟨k, h_lt⟩ = 0 := hα ⟨k, h_lt⟩
    simp only [iter, h_lt, dite_true, ih_eq, hαk, zero_smul, sub_zero]

lemma iter_zero {n N : ℕ} {L R : ℝ} (I : Instance n L R) (k : ℕ) (hk : k ≤ N) :
    iter I (0 : Fin N → ℝ) k = I.x0 := by
  apply iter_zero_aux I 0 (fun _ => by simp) k hk

lemma terminalLoss_zero {n N : ℕ} {L R : ℝ} (I : Instance n L R) :
    terminalLoss I (0 : Fin N → ℝ) = I.f I.x0 - I.f I.xStar := by
  unfold terminalLoss
  have h : iter I (0 : Fin N → ℝ) N = I.x0 := iter_zero I N (le_refl N)
  rw [h]

theorem terminalLoss_le_half {n N : ℕ} {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (I : Instance n L R) :
    terminalLoss I (0 : Fin N → ℝ) ≤ L * R ^ 2 / 2 := by
  have h0 : terminalLoss I (0 : Fin N → ℝ) = I.f I.x0 - I.f I.xStar := terminalLoss_zero I
  rw [h0]
  have hGradZero : I.G I.xStar = 0 := Instance.gradient_at_minimizer I
  have hLip : LipschitzWith I.lip I.G := I.lipschitz
  have hLip_eq : (I.lip : ℝ) = L := I.lip_eq
  have h_descent := SmoothNecessary.descent I.hasGrad hLip I.xStar (I.x0 - I.xStar)
  have h_add : I.xStar + (I.x0 - I.xStar) = I.x0 := by abel
  have h_descent2 : I.f I.x0 ≤ I.f I.xStar + inner (𝕜:=ℝ) (I.G I.xStar) (I.x0 - I.xStar) + (I.lip : ℝ) / 2 * ‖I.x0 - I.xStar‖ ^ 2 := by
    have h1 := h_descent
    rw [h_add] at h1
    exact h1
  have h_inner_zero : inner (𝕜:=ℝ) (I.G I.xStar) (I.x0 - I.xStar) = 0 := by
    rw [hGradZero]
    simp
  rw [h_inner_zero, hLip_eq] at h_descent2
  have h_norm_le : ‖I.x0 - I.xStar‖ ≤ R := I.near
  have h_norm_sq_le : ‖I.x0 - I.xStar‖ ^ 2 ≤ R ^ 2 := by
    have h_nn : 0 ≤ ‖I.x0 - I.xStar‖ := norm_nonneg _
    have h1 : ‖I.x0 - I.xStar‖ ^ 2 ≤ R ^ 2 := by
      apply sq_le_sq'
      · linarith
      · exact h_norm_le
    exact h1
  have h_L2_nonneg : 0 ≤ L / 2 := by linarith
  have h_le2 : L / 2 * ‖I.x0 - I.xStar‖ ^ 2 ≤ L / 2 * R ^ 2 := mul_le_mul_of_nonneg_left h_norm_sq_le h_L2_nonneg
  have h_eq : L * R ^ 2 / 2 = L / 2 * R ^ 2 := by ring
  linarith

theorem risk0_at_zero_le {N : ℕ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    risk0 (N:=N) L R (0 : Fin N → ℝ) ≤ (L * R ^ 2 / 2 : EReal) := by
  have hR0 : 0 ≤ R := le_of_lt hR
  have h_bound : ∀ (I : AllInstances L R), (terminalLoss I.2 (0 : Fin N → ℝ) : EReal) ≤ (L * R ^ 2 / 2 : EReal) := by
    intro I
    have h_real : terminalLoss I.2 (0 : Fin N → ℝ) ≤ L * R ^ 2 / 2 := terminalLoss_le_half hL hR0 I.2
    exact EReal.coe_le_coe_iff.mpr h_real
  unfold risk0
  exact iSup_le h_bound

theorem finiteSublevel_nonempty {N : ℕ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    (finiteSublevel N L R (L * R ^ 2 / 2)).Nonempty := by
  use (0 : Fin N → ℝ)
  unfold finiteSublevel
  exact risk0_at_zero_le hL hR

-- (E) Attainment
theorem exists_minimizer {N : ℕ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    ∃ α : Fin N → ℝ, IsMinOn (risk0 (N:=N) L R) Set.univ α := by
  let C := L * R ^ 2 / 2
  let S := finiteSublevel N L R C
  have hS_compact : IsCompact S := finiteSublevel_isCompact (N:=N) L R C hL hR
  have hS_nonempty : S.Nonempty := finiteSublevel_nonempty (N:=N) hL hR
  have h_lsc : LowerSemicontinuous (risk0 (N:=N) L R) := risk0_lsc L R
  have h_lscOn : LowerSemicontinuousOn (risk0 (N:=N) L R) S := h_lsc.lowerSemicontinuousOn S
  obtain ⟨a, ha_mem, ha_min⟩ := LowerSemicontinuousOn.exists_isMinOn hS_nonempty hS_compact h_lscOn
  have ha_le_C : risk0 (N:=N) L R a ≤ (C : EReal) := ha_mem
  have h_global : ∀ β : Fin N → ℝ, risk0 (N:=N) L R a ≤ risk0 (N:=N) L R β := by
    intro β
    by_cases hβ : risk0 (N:=N) L R β ≤ (C : EReal)
    · have hβ_mem : β ∈ S := hβ
      exact ha_min hβ_mem
    · have h_gt : (C : EReal) < risk0 (N:=N) L R β := lt_of_not_ge hβ
      exact le_trans ha_le_C (le_of_lt h_gt)
  use a
  intro x hx
  exact h_global x

theorem isMinOn_attains_iInf {N : ℕ} {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    ∃ α : Fin N → ℝ, (⨅ β : Fin N → ℝ, risk0 (N:=N) L R β) = risk0 (N:=N) L R α ∧ ∀ β, risk0 (N:=N) L R α ≤ risk0 (N:=N) L R β := by
  obtain ⟨a, ha⟩ := exists_minimizer (N:=N) hL hR
  have ha' : ∀ β : Fin N → ℝ, risk0 (N:=N) L R a ≤ risk0 (N:=N) L R β := fun β => ha (Set.mem_univ β)
  have h_iInf_le : (⨅ β : Fin N → ℝ, risk0 (N:=N) L R β) ≤ risk0 (N:=N) L R a := iInf_le (risk0 (N:=N) L R) a
  have h_le_iInf : risk0 (N:=N) L R a ≤ (⨅ β : Fin N → ℝ, risk0 (N:=N) L R β) := le_iInf ha'
  have h_eq : (⨅ β : Fin N → ℝ, risk0 (N:=N) L R β) = risk0 (N:=N) L R a := le_antisymm h_iInf_le h_le_iInf
  exact ⟨a, h_eq, ha'⟩


end SmoothAttain
