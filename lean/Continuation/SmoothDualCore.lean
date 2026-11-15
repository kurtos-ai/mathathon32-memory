module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Finset.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

open Finset EuclideanSpace

noncomputable section

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

namespace SmoothDual

variable {d n : ℕ} [NeZero n] {L : ℝ} (hL : 0 < L)
variable (x : Fin n → E d) (g : Fin n → E d) (f : Fin n → ℝ)

variable (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖^2 ≥ 0)

def hComp (i : Fin n) : ℝ := @inner ℝ (E d) _ (g i) (x i) - f i

def Hi (L : ℝ) (i : Fin n) (u : E d) : ℝ :=
  hComp (x:=x) (g:=g) (f:=f) i + @inner ℝ (E d) _ (x i) (u - g i) + (1/(2*L)) * ‖u - g i‖^2

def H (L : ℝ) (u : E d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => Hi (x:=x) (g:=g) (f:=f) L i u)

lemma Hi_eq (i : Fin n) (u : E d) :
    Hi (x:=x) (g:=g) (f:=f) L i u = @inner ℝ (E d) _ (x i) u - f i + (1/(2*L)) * ‖u - g i‖^2 := by
  unfold Hi hComp
  have hcomm : @inner ℝ (E d) _ (g i) (x i) = @inner ℝ (E d) _ (x i) (g i) := real_inner_comm _ _
  simp only [inner_sub_right]
  linarith

lemma Hi_at_g (i : Fin n) : Hi (x:=x) (g:=g) (f:=f) L i (g i) = hComp (x:=x) (g:=g) (f:=f) i := by
  unfold Hi
  simp [sub_self, norm_zero]

lemma Hi_at_g_eq_h (i : Fin n) : Hi (x:=x) (g:=g) (f:=f) L i (g i) = @inner ℝ (E d) _ (g i) (x i) - f i := by
  rw [Hi_at_g]; rfl

lemma norm_sq_convex_combo (a b : E d) (t : ℝ) :
    ‖t • a + (1 - t) • b‖ ^ 2 = t * ‖a‖ ^ 2 + (1 - t) * ‖b‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
  have h1 : ‖t • a + (1 - t) • b‖ ^ 2 = ‖t • a‖ ^ 2 + 2 * @inner ℝ (E d) _ (t • a) ((1 - t) • b) + ‖(1 - t) • b‖ ^ 2 := by
    rw [norm_add_sq_real]
  have h2 : @inner ℝ (E d) _ (t • a) ((1 - t) • b) = t * (1 - t) * @inner ℝ (E d) _ a b := by
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have h3 : ‖t • a‖ ^ 2 = t ^ 2 * ‖a‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h4 : ‖(1 - t) • b‖ ^ 2 = (1 - t) ^ 2 * ‖b‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h5 : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * @inner ℝ (E d) _ a b + ‖b‖ ^ 2 := by rw [norm_sub_sq_real]
  calc ‖t • a + (1 - t) • b‖ ^ 2
      = t ^ 2 * ‖a‖ ^ 2 + 2 * (t * (1 - t) * @inner ℝ (E d) _ a b) + (1 - t) ^ 2 * ‖b‖ ^ 2 := by rw [h1, h2, h3, h4]
    _ = t * ‖a‖ ^ 2 + (1 - t) * ‖b‖ ^ 2 - t * (1 - t) * (‖a‖ ^ 2 - 2 * @inner ℝ (E d) _ a b + ‖b‖ ^ 2) := by ring
    _ = t * ‖a‖ ^ 2 + (1 - t) * ‖b‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by rw [h5]

lemma Hi_convex_combo (i : Fin n) (u v : E d) (t : ℝ) :
    Hi (x:=x) (g:=g) (f:=f) L i (t • u + (1 - t) • v) =
      t * Hi (x:=x) (g:=g) (f:=f) L i u + (1 - t) * Hi (x:=x) (g:=g) (f:=f) L i v
        - t * (1 - t) / (2 * L) * ‖u - v‖ ^ 2 := by
  rw [Hi_eq, Hi_eq, Hi_eq]
  have hlin : @inner ℝ (E d) _ (x i) (t • u + (1 - t) • v) =
      t * @inner ℝ (E d) _ (x i) u + (1 - t) * @inner ℝ (E d) _ (x i) v := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  have heq : t • u + (1 - t) • v - g i = t • (u - g i) + (1 - t) • (v - g i) := by module
  have hquad : ‖t • u + (1 - t) • v - g i‖ ^ 2 =
      t * ‖u - g i‖ ^ 2 + (1 - t) * ‖v - g i‖ ^ 2 - t * (1 - t) * ‖u - v‖ ^ 2 := by
    have h1 : ‖t • (u - g i) + (1 - t) • (v - g i)‖ ^ 2 =
        t * ‖u - g i‖ ^ 2 + (1 - t) * ‖v - g i‖ ^ 2 - t * (1 - t) * ‖(u - g i) - (v - g i)‖ ^ 2 :=
      norm_sq_convex_combo (d:=d) (a:=u - g i) (b:=v - g i) t
    have h2 : (u - g i) - (v - g i) = u - v := by abel
    rw [heq, h1, h2]
  calc @inner ℝ (E d) _ (x i) (t • u + (1 - t) • v) - f i + 1 / (2 * L) * ‖t • u + (1 - t) • v - g i‖ ^ 2
      = (t * @inner ℝ (E d) _ (x i) u + (1 - t) * @inner ℝ (E d) _ (x i) v) - f i
          + 1 / (2 * L) * (t * ‖u - g i‖ ^ 2 + (1 - t) * ‖v - g i‖ ^ 2 - t * (1 - t) * ‖u - v‖ ^ 2) := by rw [hlin, hquad]
    _ = t * (@inner ℝ (E d) _ (x i) u - f i + 1 / (2 * L) * ‖u - g i‖ ^ 2)
          + (1 - t) * (@inner ℝ (E d) _ (x i) v - f i + 1 / (2 * L) * ‖v - g i‖ ^ 2)
          - t * (1 - t) / (2 * L) * ‖u - v‖ ^ 2 := by ring

theorem H_ge_Hi (u : E d) (i : Fin n) : Hi (x:=x) (g:=g) (f:=f) L i u ≤ H (x:=x) (g:=g) (f:=f) L u := by
  unfold H; exact Finset.le_sup' (fun j => Hi (x:=x) (g:=g) (f:=f) L j u) (Finset.mem_univ i)

theorem H_exists_eq (u : E d) : ∃ i : Fin n, H (x:=x) (g:=g) (f:=f) L u = Hi (x:=x) (g:=g) (f:=f) L i u := by
  have h := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => Hi (x:=x) (g:=g) (f:=f) L i u)
  obtain ⟨i, _, hi⟩ := h
  have : H (x:=x) (g:=g) (f:=f) L u = Finset.univ.sup' Finset.univ_nonempty (fun i => Hi (x:=x) (g:=g) (f:=f) L i u) := rfl
  exact ⟨i, by rw [this, hi]⟩

theorem H_attained (u : E d) : ∃ i, ∀ j, H (x:=x) (g:=g) (f:=f) L u = Hi (x:=x) (g:=g) (f:=f) L i u ∧
    Hi (x:=x) (g:=g) (f:=f) L j u ≤ H (x:=x) (g:=g) (f:=f) L u := by
  obtain ⟨i, hi⟩ := H_exists_eq (x:=x) (g:=g) (f:=f) (L:=L) u
  exact ⟨i, fun j => ⟨hi, H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) u j⟩⟩

theorem H_strongConvex : StrongConvexOn (Set.univ : Set (E d)) (1 / L) (H (x:=x) (g:=g) (f:=f) L) := by
  constructor
  · exact convex_univ
  · intro u _ v _ a b ha hb hab
    obtain ⟨i0, hi0⟩ := H_exists_eq (x:=x) (g:=g) (f:=f) (L:=L) (a • u + b • v)
    have hHi0 : H (x:=x) (g:=g) (f:=f) L (a • u + b • v) = Hi (x:=x) (g:=g) (f:=f) L i0 (a • u + b • v) := hi0
    have hb_eq : b = 1 - a := by linarith
    rw [hHi0]
    have hpoint : a • u + b • v = a • u + (1 - a) • v := by rw [hb_eq]
    have hcomb : Hi (x:=x) (g:=g) (f:=f) L i0 (a • u + b • v) =
        a * Hi (x:=x) (g:=g) (f:=f) L i0 u + b * Hi (x:=x) (g:=g) (f:=f) L i0 v
          - a * b / (2 * L) * ‖u - v‖ ^ 2 := by
      calc Hi (x:=x) (g:=g) (f:=f) L i0 (a • u + b • v)
          = Hi (x:=x) (g:=g) (f:=f) L i0 (a • u + (1 - a) • v) := by rw [hpoint]
        _ = a * Hi (x:=x) (g:=g) (f:=f) L i0 u + (1 - a) * Hi (x:=x) (g:=g) (f:=f) L i0 v
              - a * (1 - a) / (2 * L) * ‖u - v‖ ^ 2 := Hi_convex_combo (x:=x) (g:=g) (f:=f) (i:=i0) (u:=u) (v:=v) (t:=a)
        _ = a * Hi (x:=x) (g:=g) (f:=f) L i0 u + b * Hi (x:=x) (g:=g) (f:=f) L i0 v
              - a * b / (2 * L) * ‖u - v‖ ^ 2 := by rw [hb_eq]
    rw [hcomb]
    have h1 : Hi (x:=x) (g:=g) (f:=f) L i0 u ≤ H (x:=x) (g:=g) (f:=f) L u := H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) (u:=u) (i:=i0)
    have h2 : Hi (x:=x) (g:=g) (f:=f) L i0 v ≤ H (x:=x) (g:=g) (f:=f) L v := H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) (u:=v) (i:=i0)
    have hm : (1 : ℝ) / L / 2 = 1 / (2 * L) := by ring
    calc a * Hi (x:=x) (g:=g) (f:=f) L i0 u + b * Hi (x:=x) (g:=g) (f:=f) L i0 v - a * b / (2 * L) * ‖u - v‖ ^ 2
        ≤ a * H (x:=x) (g:=g) (f:=f) L u + b * H (x:=x) (g:=g) (f:=f) L v - a * b / (2 * L) * ‖u - v‖ ^ 2 := by gcongr
      _ = a • H (x:=x) (g:=g) (f:=f) L u + b • H (x:=x) (g:=g) (f:=f) L v - a * b * ((1 / L) / 2 * ‖u - v‖ ^ 2) := by simp only [smul_eq_mul]; rw [hm]; ring

theorem H_strongConvex_t (u v : E d) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    H (x:=x) (g:=g) (f:=f) L (t • u + (1 - t) • v) ≤
      t * H (x:=x) (g:=g) (f:=f) L u + (1 - t) * H (x:=x) (g:=g) (f:=f) L v
        - t * (1 - t) / (2 * L) * ‖u - v‖ ^ 2 := by
  obtain ⟨i0, hi0⟩ := H_exists_eq (x:=x) (g:=g) (f:=f) (L:=L) (t • u + (1 - t) • v)
  have hHi0 : H (x:=x) (g:=g) (f:=f) L (t • u + (1 - t) • v) = Hi (x:=x) (g:=g) (f:=f) L i0 (t • u + (1 - t) • v) := hi0
  rw [hHi0, Hi_convex_combo (x:=x) (g:=g) (f:=f) (i:=i0) (u:=u) (v:=v) (t:=t)]
  have h1 : Hi (x:=x) (g:=g) (f:=f) L i0 u ≤ H (x:=x) (g:=g) (f:=f) L u := H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) (u:=u) (i:=i0)
  have h2 : Hi (x:=x) (g:=g) (f:=f) L i0 v ≤ H (x:=x) (g:=g) (f:=f) L v := H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) (u:=v) (i:=i0)
  have ha : 0 ≤ t := ht.1.le
  have hb : 0 ≤ 1 - t := by linarith [ht.2]
  gcongr

theorem H_le_at_g (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖ ^ 2 ≥ 0)
    (i j : Fin n) : Hi (x:=x) (g:=g) (f:=f) L j (g i) ≤ Hi (x:=x) (g:=g) (f:=f) L i (g i) := by
  rw [Hi_eq (x:=x) (g:=g) (f:=f) (L:=L) (i:=j) (u:=g i), Hi_eq (x:=x) (g:=g) (f:=f) (L:=L) (i:=i) (u:=g i)]
  have hzero : ‖g i - g i‖ = (0 : ℝ) := by simp
  have hzero2 : ‖g i - g i‖ ^ 2 = (0 : ℝ) := by rw [hzero, zero_pow (by norm_num)]
  rw [hzero2, mul_zero, add_zero]
  have h := hTHG j i
  have hinner : @inner ℝ (E d) _ (g i) (x j - x i) = @inner ℝ (E d) _ (g i) (x j) - @inner ℝ (E d) _ (g i) (x i) := inner_sub_right (𝕜:=ℝ) (x:=g i) (y:=x j) (z:=x i)
  have hcomm1 : @inner ℝ (E d) _ (g i) (x j) = @inner ℝ (E d) _ (x j) (g i) := real_inner_comm _ _
  have hcomm2 : @inner ℝ (E d) _ (g i) (x i) = @inner ℝ (E d) _ (x i) (g i) := real_inner_comm _ _
  have hnorm : ‖g j - g i‖ = ‖g i - g j‖ := by rw [norm_sub_rev]
  have hsym : ‖g i - g j‖ ^ 2 = ‖g j - g i‖ ^ 2 := by rw [hnorm]
  have h' : f j - f i - (@inner ℝ (E d) _ (g i) (x j) - @inner ℝ (E d) _ (g i) (x i)) - 1/(2*L) * ‖g j - g i‖ ^ 2 ≥ 0 := by
    have : @inner ℝ (E d) _ (g i) (x j - x i) = @inner ℝ (E d) _ (g i) (x j) - @inner ℝ (E d) _ (g i) (x i) := inner_sub_right _ _ _
    rw [this] at h; exact h
  have h'' : f j - f i - (@inner ℝ (E d) _ (x j) (g i) - @inner ℝ (E d) _ (x i) (g i)) - 1/(2*L) * ‖g i - g j‖ ^ 2 ≥ 0 := by
    rw [hcomm1, hcomm2, ←hsym] at h'; exact h'
  linarith

theorem H_contact (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖ ^ 2 ≥ 0)
    (i : Fin n) : H (x:=x) (g:=g) (f:=f) L (g i) = hComp (x:=x) (g:=g) (f:=f) i := by
  have hi_eq : Hi (x:=x) (g:=g) (f:=f) L i (g i) = hComp (x:=x) (g:=g) (f:=f) i := Hi_at_g (x:=x) (g:=g) (f:=f) (i:=i)
  have h_le : H (x:=x) (g:=g) (f:=f) L (g i) ≤ Hi (x:=x) (g:=g) (f:=f) L i (g i) := by
    unfold H
    apply Finset.sup'_le
    intro j _
    exact H_le_at_g (x:=x) (g:=g) (f:=f) (L:=L) hTHG i j
  have h_ge : Hi (x:=x) (g:=g) (f:=f) L i (g i) ≤ H (x:=x) (g:=g) (f:=f) L (g i) :=
    H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) (u:=g i) (i:=i)
  linarith

theorem H_contact' (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖ ^ 2 ≥ 0)
    (i : Fin n) : H (x:=x) (g:=g) (f:=f) L (g i) = @inner ℝ (E d) _ (g i) (x i) - f i := by
  rw [H_contact (x:=x) (g:=g) (f:=f) (L:=L) hTHG (i:=i)]
  rfl

theorem H_subgradient (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖ ^ 2 ≥ 0)
    (i : Fin n) (u : E d) :
    H (x:=x) (g:=g) (f:=f) L u ≥ H (x:=x) (g:=g) (f:=f) L (g i) + @inner ℝ (E d) _ (x i) (u - g i) + 1/(2*L) * ‖u - g i‖ ^ 2 := by
  have hHgi : H (x:=x) (g:=g) (f:=f) L (g i) = hComp (x:=x) (g:=g) (f:=f) i := H_contact (x:=x) (g:=g) (f:=f) (L:=L) hTHG (i:=i)
  have h1 : H (x:=x) (g:=g) (f:=f) L u ≥ Hi (x:=x) (g:=g) (f:=f) L i u := H_ge_Hi (x:=x) (g:=g) (f:=f) (L:=L) (u:=u) (i:=i)
  have h2 : Hi (x:=x) (g:=g) (f:=f) L i u = hComp (x:=x) (g:=g) (f:=f) i + @inner ℝ (E d) _ (x i) (u - g i) + 1/(2*L) * ‖u - g i‖ ^ 2 := rfl
  linarith

theorem H_subgradient_weak (hL : 0 < L) (hTHG : ∀ i j : Fin n, f i - f j - @inner ℝ (E d) _ (g j) (x i - x j) - (1/(2*L)) * ‖g i - g j‖ ^ 2 ≥ 0)
    (i : Fin n) (u : E d) :
    H (x:=x) (g:=g) (f:=f) L u ≥ H (x:=x) (g:=g) (f:=f) L (g i) + @inner ℝ (E d) _ (x i) (u - g i) := by
  have h := H_subgradient (x:=x) (g:=g) (f:=f) (L:=L) hTHG (i:=i) (u:=u)
  have hpos : 0 ≤ 1/(2*L) * ‖u - g i‖ ^ 2 := by
    apply mul_nonneg
    · apply div_nonneg (by linarith) (by linarith)
    · exact sq_nonneg _
  linarith

end SmoothDual
