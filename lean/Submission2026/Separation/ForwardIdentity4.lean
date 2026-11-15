module

public import Submission2026.Separation.PathIdentities4

@[expose] public section
noncomputable section

/-! The actual five-coordinate forward data and residual identity. Entries
outside 0,...,4 are unused. No residual identity or target inequality is an
input hypothesis. -/
namespace Submission2026.Separation.ForwardIdentity4
open Submission2026.Separation.PathIdentities4
open scoped BigOperators

def tau (T : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := T i i
def mass (T : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := sum5 (fun k => T k i)
def omega (T : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := sum5 (T i) - if i = 4 then 1 else 0
def prefixSum (f : ℕ → ℝ) (i : ℕ) : ℝ := sum5 (fun j => if j ≤ i then f j else 0)
def suffix (f : ℕ → ℝ) (i : ℕ) : ℝ := sum5 (fun j => if i < j then f j else 0)
def epsilon (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  prefixSum (fun j => b j * mass T j) i - b i * tau T i

def Upper4 (T : ℕ → ℕ → ℝ) : Prop := ∀ i ≤ 4, ∀ j < i, T i j = 0
def Solves4 (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ) : Prop :=
  ∀ i ≤ 4, sum5 (fun j => T i j * b j) = if i = 4 then 1 else 0

structure ForwardData4 (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ) : Prop where
  upper : Upper4 T
  solves : Solves4 T b
  diag_nonneg : ∀ i ≤ 4, 0 ≤ tau T i
  off_nonpos : ∀ i ≤ 4, ∀ j ≤ 4, i < j → T i j ≤ 0
  omega_nonneg : ∀ i ≤ 4, 0 ≤ omega T i
  mass_nonneg : ∀ i ≤ 4, 0 ≤ mass T i
  b_nonneg : ∀ i ≤ 4, 0 ≤ b i
  b_le_one : ∀ i ≤ 4, b i ≤ 1

theorem total_weight (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (hb : Solves4 T b) :
    sum5 (fun i => b i * mass T i) = 1 := by
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  have h4 := hb 4 (by omega)
  norm_num [sum5] at h0 h1 h2 h3 h4
  unfold sum5 mass
  dsimp [sum5]
  linear_combination h0 + h1 + h2 + h3 + h4

theorem prefix_mass_sub_tau (T : ℕ → ℕ → ℝ) (hu : Upper4 T)
    (i : ℕ) (hi : i ≤ 4) :
    prefixSum (mass T) i - tau T i =
      sum5 (fun k => if k < i then omega T k else 0) +
      sum5 (fun k => sum5 (fun j => if k < i ∧ i < j then -T k j else 0)) := by
  have h10 := hu 1 (by omega) 0 (by omega)
  have h20 := hu 2 (by omega) 0 (by omega)
  have h21 := hu 2 (by omega) 1 (by omega)
  have h30 := hu 3 (by omega) 0 (by omega)
  have h31 := hu 3 (by omega) 1 (by omega)
  have h32 := hu 3 (by omega) 2 (by omega)
  have h40 := hu 4 (by omega) 0 (by omega)
  have h41 := hu 4 (by omega) 1 (by omega)
  have h42 := hu 4 (by omega) 2 (by omega)
  have h43 := hu 4 (by omega) 3 (by omega)
  interval_cases i <;>
    norm_num [prefixSum, mass, tau, omega, sum5, h10, h20, h21, h30, h31, h32, h40, h41, h42, h43] <;> ring

theorem epsilon_eq (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hu : Upper4 T) (hb : Solves4 T b) (i : ℕ) (hi : i ≤ 4) :
    epsilon T b i = sum5 (fun j => sum5 (fun k =>
      if j < i ∧ i < k then -T j k * b k else 0)) := by
  have h10 := hu 1 (by omega) 0 (by omega)
  have h20 := hu 2 (by omega) 0 (by omega)
  have h21 := hu 2 (by omega) 1 (by omega)
  have h30 := hu 3 (by omega) 0 (by omega)
  have h31 := hu 3 (by omega) 1 (by omega)
  have h32 := hu 3 (by omega) 2 (by omega)
  have h40 := hu 4 (by omega) 0 (by omega)
  have h41 := hu 4 (by omega) 1 (by omega)
  have h42 := hu 4 (by omega) 2 (by omega)
  have h43 := hu 4 (by omega) 3 (by omega)
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  norm_num [sum5, h10, h20, h21, h30, h31, h32, h40, h41, h42, h43] at h0 h1 h2 h3
  interval_cases i <;>
    norm_num [epsilon, prefixSum, mass, tau, sum5, h10, h20, h21, h30, h31, h32, h40, h41, h42, h43] <;>
    linarith only [h0, h1, h2, h3]

theorem sum5_nonneg (f : ℕ → ℝ) (h : ∀ i ≤ 4, 0 ≤ f i) : 0 ≤ sum5 f := by
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (h 0 (by omega))
    (h 1 (by omega))) (h 2 (by omega))) (h 3 (by omega))) (h 4 (by omega))

theorem prefix_mass_sub_tau_nonneg (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hf : ForwardData4 T b) (i : ℕ) (hi : i ≤ 4) :
    0 ≤ prefixSum (mass T) i - tau T i := by
  rw [prefix_mass_sub_tau T hf.upper i hi]
  apply add_nonneg
  · apply sum5_nonneg
    intro k hk
    split_ifs
    · exact hf.omega_nonneg k hk
    · exact le_rfl
  · apply sum5_nonneg
    intro k hk
    apply sum5_nonneg
    intro j hj
    split_ifs with h
    · exact neg_nonneg.mpr (hf.off_nonpos k hk j hj (by omega))
    · exact le_rfl

theorem epsilon_nonneg (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hf : ForwardData4 T b) (i : ℕ) (hi : i ≤ 4) : 0 ≤ epsilon T b i := by
  rw [epsilon_eq T b hf.upper hf.solves i hi]
  apply sum5_nonneg
  intro j hj
  apply sum5_nonneg
  intro k hk
  split_ifs with h
  · exact mul_nonneg (neg_nonneg.mpr (hf.off_nonpos j hj k hk (by omega))) (hf.b_nonneg k hk)
  · exact le_rfl

/-- Ordered-pair bilinear form from the paper, with j<k. -/
def energy (b ν u v : ℕ → ℝ) : ℝ := sum5 (fun k => sum5 (fun j =>
  if j < k then b k * ν k * ν j * (u k - u j) * (v k - v j) else 0))

def xi (ν : ℕ → ℝ) : ℝ := (sum5 ν - ν 4) / ν 4

def kappa (r : ℝ) (ν : ℕ → ℝ) (k : ℕ) : ℝ :=
  (if k = 4 then xi ν / 2 else 0) - r / 2 * ν k *
    sum5 (fun j => if j < k then ν j * (tail ν j - tail ν k) ^ 2 else 0)

def boundary (r : ℝ) (ν : ℕ → ℝ) : ℝ := pathLambda ν - sum5 (kappa r ν)

def dualValue (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ) : ℝ :=
  sum5 (fun k => b k * (tau T k * prefixSum ν k / ν k +
    ν k * sum5 (fun i => if i < k then tau T i / ν i else 0))) -
  b 4 * xi ν / 2 - energy b ν (fun i => mass T i / ν i) (fun i => mass T i / ν i) / (2 * r)

theorem bilinear_tail (m b ν : ℕ → ℝ) (hn : ∀ i ≤ 4, ν i ≠ 0) :
    energy b ν (fun i => m i / ν i) (tail ν) =
      sum5 (fun i => suffix (fun k => b k * ν k) i / ν i * prefixSum m i) -
      sum5 (fun i => prefixSum ν i / ν i *
        (sum5 (fun j => b j * m j) - prefixSum (fun j => b j * m j) i)) := by
  have hn0 := hn 0 (by omega)
  have hn1 := hn 1 (by omega)
  have hn2 := hn 2 (by omega)
  have hn3 := hn 3 (by omega)
  have hn4 := hn 4 (by omega)
  norm_num [energy, tail, prefixSum, suffix, sum5, Finset.sum_Ico_succ_top,
    Finset.sum_range_succ]
  field_simp
  ring

theorem energy_square_expansion (r : ℝ) (b ν u h : ℕ → ℝ) :
    energy b ν u u = energy b ν (fun i => u i - r * h i) (fun i => u i - r * h i) +
      2 * r * energy b ν u h - r ^ 2 * energy b ν h h := by
  norm_num [energy, sum5]
  ring

theorem energy_kappa (r : ℝ) (b ν : ℕ → ℝ) :
    r / 2 * energy b ν (tail ν) (tail ν) = b 4 * xi ν / 2 - sum5 (fun k => b k * kappa r ν k) := by
  norm_num [energy, kappa, sum5]
  ring

theorem tau_sum (τ b ν : ℕ → ℝ) :
    sum5 (fun k => b k * (τ k * prefixSum ν k / ν k +
      ν k * sum5 (fun i => if i < k then τ i / ν i else 0))) =
    sum5 (fun i => τ i / ν i * (b i * prefixSum ν i + suffix (fun k => b k * ν k) i)) := by
  norm_num [sum5, prefixSum, suffix]
  ring

/-- The paper's master identity, with the terminal zero B_4 term included
in the first sum. Every quantity is computed from T,b,nu. -/
theorem master_identity (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ)
    (hr : r ≠ 0) (hn : ∀ i ≤ 4, ν i ≠ 0) (hb : Solves4 T b) :
    dualValue r T b ν = boundary r ν -
      sum5 (fun i => suffix (fun k => b k * ν k) i / ν i * (prefixSum (mass T) i - tau T i)) -
      sum5 (fun i => prefixSum ν i / ν i * epsilon T b i) +
      sum5 (fun k => (1 - b k) * kappa r ν k) -
      energy b ν (fun i => mass T i / ν i - r * tail ν i)
        (fun i => mass T i / ν i - r * tail ν i) / (2 * r) := by
  let u : ℕ → ℝ := fun i => mass T i / ν i
  let z : ℕ → ℝ := fun i => u i - r * tail ν i
  have he := energy_square_expansion r b ν u (tail ν)
  have hk := energy_kappa r b ν
  have hbil := bilinear_tail (mass T) b ν hn
  rw [total_weight T b hb] at hbil
  have hprep : dualValue r T b ν =
      sum5 (fun i => tau T i / ν i * (b i * prefixSum ν i + suffix (fun k => b k * ν k) i)) -
      energy b ν u (tail ν) - sum5 (fun k => b k * kappa r ν k) - energy b ν z z / (2 * r) := by
    unfold dualValue
    rw [tau_sum]
    change _ - _ - energy b ν u u / (2 * r) = _
    rw [he]
    calc
      _ = sum5 (fun i => tau T i / ν i * (b i * prefixSum ν i + suffix (fun k => b k * ν k) i)) -
          energy b ν u (tail ν) - energy b ν z z / (2 * r) +
          (r / 2 * energy b ν (tail ν) (tail ν) - b 4 * xi ν / 2) := by
        dsimp [z]
        field_simp
        ring
      _ = _ := by rw [hk]; ring
  rw [hprep]
  change _ - energy b ν (fun i => mass T i / ν i) (tail ν) - _ - _ = _
  rw [hbil]
  dsimp [z, u]
  norm_num [boundary, pathLambda, ExtremalMemory.D, epsilon, prefixSum, suffix, sum5]
  ring

theorem energy_nonneg (b ν u : ℕ → ℝ)
    (hb : ∀ i ≤ 4, 0 ≤ b i) (hn : ∀ i ≤ 4, 0 ≤ ν i) : 0 ≤ energy b ν u u := by
  unfold energy
  apply sum5_nonneg
  intro k hk
  apply sum5_nonneg
  intro j hj
  split_ifs
  · nlinarith [mul_nonneg (mul_nonneg (hb k hk) (hn k hk)) (hn j hj), sq_nonneg (u k - u j)]
  · exact le_rfl

theorem dualValue_le_boundary (r : ℝ) (T : ℕ → ℕ → ℝ) (b ν : ℕ → ℝ)
    (hr : 0 < r) (hn : ∀ i ≤ 4, 0 < ν i) (hf : ForwardData4 T b)
    (hk : ∀ i ≤ 4, kappa r ν i ≤ 0) : dualValue r T b ν ≤ boundary r ν := by
  have hB : ∀ i ≤ 4, 0 ≤ suffix (fun k => b k * ν k) i := by
    intro i hi
    apply sum5_nonneg
    intro k hki
    split_ifs
    · exact mul_nonneg (hf.b_nonneg k hki) (le_of_lt (hn k hki))
    · exact le_rfl
  have hM := sum5_nonneg (fun i => suffix (fun k => b k * ν k) i / ν i *
      (prefixSum (mass T) i - tau T i)) (fun i hi =>
    mul_nonneg (div_nonneg (hB i hi) (le_of_lt (hn i hi))) (prefix_mass_sub_tau_nonneg T b hf i hi))
  have hE := sum5_nonneg (fun i => prefixSum ν i / ν i * epsilon T b i) (by
    intro i hi
    apply mul_nonneg _ (epsilon_nonneg T b hf i hi)
    apply div_nonneg _ (le_of_lt (hn i hi))
    apply sum5_nonneg
    intro j hj
    split_ifs
    · exact le_of_lt (hn j hj)
    · exact le_rfl)
  have hK : sum5 (fun k => (1 - b k) * kappa r ν k) ≤ 0 := by
    have h := sum5_nonneg (fun k => -((1 - b k) * kappa r ν k)) (by
      intro k hki
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hf.b_le_one k hki)) (hk k hki)))
    dsimp [sum5] at h ⊢
    linarith only [h]
  have hV := div_nonneg (energy_nonneg b ν (fun i => mass T i / ν i - r * tail ν i)
    hf.b_nonneg (fun i hi => le_of_lt (hn i hi))) (show (0 : ℝ) ≤ 2 * r by positivity)
  rw [master_identity r T b ν (ne_of_gt hr) (fun i hi => ne_of_gt (hn i hi)) hf.solves]
  linarith

theorem kappa_terminal (δ ν : ℕ → ℝ) (r : ℝ)
    (hp : ExtremalMemory.PathConditions4 δ ν r) : kappa r ν 4 = 0 := by
  have h := first_path_identity δ ν r hp
  norm_num [kappa, xi, sum5, Finset.sum_Ico_succ_top, Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem kappa_nonpos (δ ν : ℕ → ℝ) (r : ℝ)
    (hp : ExtremalMemory.PathConditions4 δ ν r) (i : ℕ) (hi : i ≤ 4) : kappa r ν i ≤ 0 := by
  by_cases h : i = 4
  · subst i
    rw [kappa_terminal δ ν r hp]
  · unfold kappa
    simp only [h, ite_false, zero_sub, neg_nonpos]
    apply mul_nonneg
    · exact mul_nonneg (div_nonneg (le_of_lt hp.rate_pos) (by norm_num)) (le_of_lt (hp.slack_pos i hi))
    · apply sum5_nonneg
      intro j hj
      split_ifs
      · exact mul_nonneg (le_of_lt (hp.slack_pos j hj)) (sq_nonneg _)
      · exact le_rfl

theorem boundary_eq_totalStep (δ ν : ℕ → ℝ) (r : ℝ)
    (hp : ExtremalMemory.PathConditions4 δ ν r) : boundary r ν = 1 + totalStep δ ν r := by
  have hs := second_path_identity δ ν r hp
  have hk : sum5 (kappa r ν) = xi ν / 2 - r / 2 * pairVariation ν (tail ν) := by
    norm_num [sum5, kappa, pairVariation]
    ring
  unfold boundary
  rw [hk, totalStep_eq δ ν r hp]
  unfold xi
  have hr := ne_of_gt hp.rate_pos
  have hn := ne_of_gt (hp.slack_pos 4 (by omega))
  field_simp at hs ⊢
  nlinarith only [hs]

/-- The actual N=4 forward-data upper bound at positive stationary path data.
The path identities and all residual signs are derived, not assumed. -/
theorem dualValue_le_path_totalStep (δ ν : ℕ → ℝ) (r : ℝ)
    (hp : ExtremalMemory.PathConditions4 δ ν r) (T : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hf : ForwardData4 T b) : dualValue r T b ν ≤ 1 + totalStep δ ν r := by
  rw [← boundary_eq_totalStep δ ν r hp]
  exact dualValue_le_boundary r T b ν hp.rate_pos hp.slack_pos hf (kappa_nonpos δ ν r hp)

#print axioms dualValue_le_path_totalStep
#print axioms master_identity
#print axioms dualValue_le_boundary
#print axioms bilinear_tail
#print axioms epsilon_nonneg
end Submission2026.Separation.ForwardIdentity4
