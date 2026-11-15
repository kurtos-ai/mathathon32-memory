module
public import Continuation.Quadratic.Foundations
public import Continuation.Quadratic.ChebyshevCandidate
public import Continuation.Quadratic.MatrixResidual
public import Continuation.Quadratic.SpectralRisk
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Polynomial.Roots
@[expose] public section
noncomputable section
namespace QuadraticLower
open Polynomial QuadraticFoundations QuadraticSpectral QuadraticResidual Real
open Finset Matrix

-- Definition of Chebyshev roots for p_star
def root_j (N : ℕ) (L : ℝ) (j : Fin N) : ℝ :=
  L * (Real.cos (((2 * (j.val : ℝ) + 1) * Real.pi) / (4 * (N : ℝ) + 2)))^2

-- auxiliary angle
def theta_j (N : ℕ) (j : Fin N) : ℝ :=
  ((2 * (j.val : ℝ) + 1) * Real.pi) / (4 * (N : ℝ) + 2)

theorem theta_j_eq (N : ℕ) (j : Fin N) :
    theta_j N j = ((2 * (j.val : ℝ) + 1) * Real.pi) / (4 * (N : ℝ) + 2) := rfl

theorem theta_j_pos (N : ℕ) (j : Fin N) : 0 < theta_j N j := by
  unfold theta_j
  apply div_pos
  · apply mul_pos
    · have : 0 ≤ (j.val : ℝ) := by exact_mod_cast Nat.zero_le j.val
      linarith
    · exact Real.pi_pos
  · have : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    linarith

theorem theta_j_lt_pi_div_two (N : ℕ) (j : Fin N) : theta_j N j < Real.pi / 2 := by
  unfold theta_j
  have hN : (0 : ℝ) < 4 * (N : ℝ) + 2 := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hj : (j.val : ℝ) < (N : ℝ) := by exact_mod_cast j.isLt
  have h1 : (2 * (j.val : ℝ) + 1) < 2 * (N : ℝ) + 1 := by linarith
  have h2 : 2 * (N : ℝ) + 1 < 4 * (N : ℝ) + 2 := by linarith
  calc ((2 * ↑j.val + 1) * π) / (4 * ↑N + 2)
      < ((2 * ↑N + 1) * π) / (4 * ↑N + 2) := by
          apply div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h1 hpi) hN
    _ = π / 2 := by
          have : (4 * (N : ℝ) + 2) = 2 * (2 * (N : ℝ) + 1) := by ring
          rw [this]
          field_simp

theorem theta_j_mem_Ioo (N : ℕ) (j : Fin N) : theta_j N j ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  ⟨theta_j_pos N j, theta_j_lt_pi_div_two N j⟩

theorem theta_j_mem_Icc_zero_pi (N : ℕ) (j : Fin N) : theta_j N j ∈ Set.Icc (0 : ℝ) Real.pi := by
  constructor
  · linarith [theta_j_pos N j]
  · have h := theta_j_lt_pi_div_two N j
    linarith [Real.pi_pos, Real.pi_div_two_pos.le]

theorem cos_theta_j_pos (N : ℕ) (j : Fin N) : 0 < Real.cos (theta_j N j) := by
  have hmem : theta_j N j ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [theta_j_pos N j, Real.pi_pos]
    · exact theta_j_lt_pi_div_two N j
  exact Real.cos_pos_of_mem_Ioo hmem

theorem cos_theta_j_lt_one (N : ℕ) (j : Fin N) : Real.cos (theta_j N j) < 1 := by
  have h0_lt_theta : (0 : ℝ) < theta_j N j := theta_j_pos N j
  have htheta_le_pi : theta_j N j ≤ Real.pi := by
    have h := theta_j_lt_pi_div_two N j
    linarith [Real.pi_pos]
  have hcos_lt : Real.cos (theta_j N j) < Real.cos 0 := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) htheta_le_pi h0_lt_theta
  simp at hcos_lt
  exact hcos_lt

theorem root_j_pos (N : ℕ) (L : ℝ) (hL : 0 < L) (j : Fin N) : 0 < root_j N L j := by
  unfold root_j
  apply mul_pos hL
  exact sq_pos_of_pos (cos_theta_j_pos N j)

theorem root_j_lt_L (N : ℕ) (L : ℝ) (hL : 0 < L) (j : Fin N) : root_j N L j < L := by
  unfold root_j
  have hcos_lt : Real.cos (theta_j N j) < 1 := cos_theta_j_lt_one N j
  have hcos_nonneg : 0 ≤ Real.cos (theta_j N j) := le_of_lt (cos_theta_j_pos N j)
  have hsq_lt : (Real.cos (theta_j N j))^2 < 1 := by
    have h1 : Real.cos (theta_j N j) < 1 := hcos_lt
    have h2 : 0 ≤ Real.cos (theta_j N j) := hcos_nonneg
    nlinarith [sq_nonneg (Real.cos (theta_j N j)), sq_nonneg (1 - Real.cos (theta_j N j))]
  calc L * (Real.cos (theta_j N j))^2 < L * 1 := by
        apply mul_lt_mul_of_pos_left hsq_lt hL
    _ = L := by ring

theorem root_j_mem_Ioo (N : ℕ) (L : ℝ) (hL : 0 < L) (j : Fin N) : root_j N L j ∈ Set.Ioo 0 L :=
  ⟨root_j_pos N L hL j, root_j_lt_L N L hL j⟩

theorem root_j_ne_zero (N : ℕ) (L : ℝ) (hL : 0 < L) (j : Fin N) : root_j N L j ≠ 0 :=
  ne_of_gt (root_j_pos N L hL j)

-- distinctness: theta_j strictly increasing in j, cos strictly decreasing, hence injective
theorem theta_j_strictMono (N : ℕ) : StrictMono (fun j : Fin N => theta_j N j) := by
  intro a b hab
  unfold theta_j
  have hN : (0 : ℝ) < 4 * (N : ℝ) + 2 := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : (2 * (a.val : ℝ) + 1) < 2 * (b.val : ℝ) + 1 := by
    have : (a.val : ℝ) < (b.val : ℝ) := by exact_mod_cast hab
    linarith
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h1 hpi) hN

theorem cos_theta_j_strictAnti (N : ℕ) : StrictAnti (fun j : Fin N => Real.cos (theta_j N j)) := by
  intro a b hab
  have htheta_lt : theta_j N a < theta_j N b := theta_j_strictMono N hab
  have ha_mem : theta_j N a ∈ Set.Icc (0 : ℝ) Real.pi := theta_j_mem_Icc_zero_pi N a
  have hb_mem : theta_j N b ∈ Set.Icc (0 : ℝ) Real.pi := theta_j_mem_Icc_zero_pi N b
  exact Real.strictAntiOn_cos ha_mem hb_mem htheta_lt

theorem root_j_injective (N : ℕ) (L : ℝ) (hL : 0 < L) : Function.Injective (root_j N L) := by
  intro a b hab
  unfold root_j at hab
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hcos_sq_eq : (Real.cos (theta_j N a))^2 = (Real.cos (theta_j N b))^2 := by
    have : L * (Real.cos (theta_j N a))^2 = L * (Real.cos (theta_j N b))^2 := hab
    exact mul_left_cancel₀ hL_ne this
  have hcos_pos_a : 0 < Real.cos (theta_j N a) := cos_theta_j_pos N a
  have hcos_pos_b : 0 < Real.cos (theta_j N b) := cos_theta_j_pos N b
  have hcos_eq : Real.cos (theta_j N a) = Real.cos (theta_j N b) := by
    nlinarith [sq_nonneg (Real.cos (theta_j N a) - Real.cos (theta_j N b)),
               sq_nonneg (Real.cos (theta_j N a) + Real.cos (theta_j N b)),
               hcos_pos_a, hcos_pos_b]
  have hanti := cos_theta_j_strictAnti N
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := hanti hlt
    linarith
  · have hstrict := hanti hgt
    linarith

theorem root_j_pairwise_distinct (N : ℕ) (L : ℝ) (hL : 0 < L) (a b : Fin N) (hab : a ≠ b) :
    root_j N L a ≠ root_j N L b :=
  fun h => hab (root_j_injective N L hL h)

-- cos ((2k+1)π/2) = 0 lemma
theorem cos_nat_pi_add_pi_div_two (k : ℕ) : Real.cos ((k : ℝ) * Real.pi + Real.pi / 2) = 0 := by
  induction k with
  | zero =>
    simp [Real.cos_pi_div_two]
  | succ n ih =>
    have h1 : ((n + 1 : ℕ) : ℝ) * Real.pi + Real.pi / 2 = ((n : ℝ) * Real.pi + Real.pi / 2) + Real.pi := by
      push_cast; ring
    rw [h1, Real.cos_add_pi, ih, neg_zero]

theorem cos_two_mul_add_one_pi_div_two (k : ℕ) : Real.cos (((2 * (k : ℝ) + 1) * Real.pi / 2)) = 0 := by
  have heq : ((2 * (k : ℝ) + 1) * Real.pi / 2) = (k : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [heq, cos_nat_pi_add_pi_div_two k]

-- p_star evaluation at root_j is zero
theorem p_star_eval_root_j (N : ℕ) (L : ℝ) (hL : 0 < L) (j : Fin N) :
    (p_star N L).eval (root_j N L j) = 0 := by
  unfold root_j
  -- use p_star_eval with u = cos (theta_j)
  have htheta : theta_j N j = ((2 * (j.val : ℝ) + 1) * Real.pi) / (4 * (N : ℝ) + 2) := rfl
  have hu : L * (Real.cos (theta_j N j))^2 = L * (Real.cos (theta_j N j))^2 := rfl
  -- prepare u
  let u := Real.cos (theta_j N j)
  have hLu : L * u ^ 2 = L * (Real.cos (theta_j N j))^2 := rfl
  have h_eval : u * (p_star N L).eval (L * u ^ 2) = ((-1 : ℝ) ^ N / (2 * (N : ℝ) + 1)) * (chebM N).eval u :=
    p_star_eval N L u hL
  -- we need to show chebM N eval u = 0
  have hcheb_zero : (chebM N).eval u = 0 := by
    unfold u
    rw [chebM_eval_cos N (theta_j N j)]
    -- need (2N+1)*theta_j = (2j+1)π/2
    have hangle : (2 * (N : ℝ) + 1) * theta_j N j = ((2 * (j.val : ℝ) + 1) * Real.pi / 2) := by
      unfold theta_j
      have hN_real : (4 * (N : ℝ) + 2) = 2 * (2 * (N : ℝ) + 1) := by ring
      rw [hN_real]
      field_simp
    rw [hangle]
    -- now use cos((2j+1)π/2)=0
    have : ((2 * (j.val : ℝ) + 1) * Real.pi / 2) = (j.val : ℝ) * Real.pi + Real.pi / 2 := by ring
    rw [this]
    exact cos_nat_pi_add_pi_div_two j.val
  rw [hcheb_zero] at h_eval
  have h1 : u * (p_star N L).eval (L * u ^ 2) = 0 := by rw [h_eval, mul_zero]
  have hu_ne : u ≠ 0 := ne_of_gt (cos_theta_j_pos N j)
  exact (mul_eq_zero.mp h1).resolve_left hu_ne

theorem p_star_ne_zero (N : ℕ) (L : ℝ) (hL : 0 < L) : p_star N L ≠ 0 := by
  intro h
  have h0 := p_star_at_zero N L hL
  rw [h, Polynomial.eval_zero] at h0
  linarith

theorem p_star_natDegree_eq (N : ℕ) (L : ℝ) (hL : 0 < L) : (p_star N L).natDegree = N := by
  have hle := p_star_natDegree_le N L
  have hne := p_star_ne_zero N L hL
  have hroots : ∀ j : Fin N, (p_star N L).IsRoot (root_j N L j) := by
    intro j
    rw [Polynomial.IsRoot, p_star_eval_root_j N L hL j]
  let s : Finset ℝ := Finset.univ.image (root_j N L)
  have hs_card : s.card = N := by
    rw [Finset.card_image_of_injective _ (root_j_injective N L hL)]
    simp
  have hs_mem_roots : ∀ x ∈ s, x ∈ (p_star N L).roots := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    rw [Polynomial.mem_roots hne]
    exact hroots j
  have hs_sub : s.val ⊆ (p_star N L).roots := by
    intro x hx
    have hx_mem : x ∈ s := Finset.mem_val.mp hx
    exact hs_mem_roots x hx_mem
  have hge : N ≤ (p_star N L).natDegree := by
    have h1 : s.card ≤ (p_star N L).natDegree := Polynomial.card_le_degree_of_subset_roots hs_sub
    rw [hs_card] at h1
    exact h1
  omega

-- factorization
def q_factor (N : ℕ) (L : ℝ) : ℝ[X] :=
  Finset.prod Finset.univ (fun j : Fin N => (1 - Polynomial.C ((root_j N L j)⁻¹) * X))

theorem q_factor_eval_zero (N : ℕ) (L : ℝ) : (q_factor N L).eval 0 = 1 := by
  unfold q_factor
  simp [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

theorem q_factor_natDegree_le (N : ℕ) (L : ℝ) : (q_factor N L).natDegree ≤ N := by
  unfold q_factor
  -- each factor degree ≤1, product degree ≤ N
  have h1 : ∀ j : Fin N, ((1 : ℝ[X]) - Polynomial.C ((root_j N L j)⁻¹) * X).natDegree ≤ 1 := by
    intro j
    have hle : (Polynomial.C ((root_j N L j)⁻¹) * X).natDegree ≤ 1 := by
      calc (Polynomial.C ((root_j N L j)⁻¹) * X).natDegree ≤ (Polynomial.C ((root_j N L j)⁻¹)).natDegree + X.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 := by simp
    calc ((1 : ℝ[X]) - Polynomial.C ((root_j N L j)⁻¹) * X).natDegree
        ≤ max (1 : ℝ[X]).natDegree (Polynomial.C ((root_j N L j)⁻¹) * X).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ 1 := by simp [hle]
  -- use natDegree_prod_le
  calc (Finset.prod Finset.univ (fun j : Fin N => (1 - Polynomial.C ((root_j N L j)⁻¹) * X))).natDegree
      ≤ Finset.sum Finset.univ (fun j : Fin N => ((1 - Polynomial.C ((root_j N L j)⁻¹) * X).natDegree)) := Polynomial.natDegree_prod_le _ _
    _ ≤ Finset.sum Finset.univ (fun _ : Fin N => 1) := by
        apply Finset.sum_le_sum
        intro j _; exact h1 j
    _ = N := by simp

theorem q_factor_eval_root (N : ℕ) (L : ℝ) (hL : 0 < L) (k : Fin N) :
    (q_factor N L).eval (root_j N L k) = 0 := by
  unfold q_factor
  rw [Polynomial.eval_prod]
  have hk_mem : k ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ k
  have hfactor_zero : (1 - (Polynomial.C ((root_j N L k)⁻¹) * X : ℝ[X])).eval (root_j N L k) = 0 := by
    simp [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, inv_mul_cancel₀ (root_j_ne_zero N L hL k)]
  have hprod_zero : ∏ i ∈ Finset.univ, ((1 - Polynomial.C ((root_j N L i)⁻¹) * X : ℝ[X]).eval (root_j N L k)) = 0 := by
    apply Finset.prod_eq_zero hk_mem hfactor_zero
  exact hprod_zero

theorem p_star_factorization (N : ℕ) (L : ℝ) (hL : 0 < L) :
    p_star N L = q_factor N L := by
  unfold q_factor
  have hp0_eq : (p_star N L).eval 0 = 1 := p_star_at_zero N L hL
  have hq0_eq : (Finset.prod Finset.univ (fun j : Fin N => (1 - Polynomial.C ((root_j N L j)⁻¹) * X : ℝ[X]))).eval 0 = 1 := by
    simp [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hq_le : (q_factor N L).natDegree ≤ N := q_factor_natDegree_le N L
  have hp_le : (p_star N L).natDegree ≤ N := p_star_natDegree_le N L
  let q : ℝ[X] := Finset.prod Finset.univ (fun j : Fin N => (1 - Polynomial.C ((root_j N L j)⁻¹) * X : ℝ[X]))
  have hq_roots : ∀ k : Fin N, q.eval (root_j N L k) = 0 := fun k => q_factor_eval_root N L hL k
  have hp_roots : ∀ k : Fin N, (p_star N L).eval (root_j N L k) = 0 := fun k => p_star_eval_root_j N L hL k
  have hq_at_zero : q.eval 0 = 1 := hq0_eq
  have hp_at_zero : (p_star N L).eval 0 = 1 := hp0_eq
  let h : ℝ[X] := p_star N L - q
  have hh_le : h.natDegree ≤ N := by
    have h1 : (p_star N L).natDegree ≤ N := hp_le
    have h2 : q.natDegree ≤ N := hq_le
    calc h.natDegree = (p_star N L - q).natDegree := rfl
      _ ≤ max (p_star N L).natDegree q.natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ N := Nat.max_le.mpr ⟨h1, h2⟩
  have hh_roots : ∀ k : Fin N, h.IsRoot (root_j N L k) := by
    intro k
    show (p_star N L - q).eval (root_j N L k) = 0
    rw [Polynomial.eval_sub, hp_roots k, hq_roots k, sub_self]
  have hh_zero_root : h.IsRoot 0 := by
    show (p_star N L - q).eval 0 = 0
    rw [Polynomial.eval_sub, hp_at_zero, hq_at_zero, sub_self]
  have hdistinct_zero : ∀ k : Fin N, (0 : ℝ) ≠ root_j N L k := by
    intro k
    exact ne_of_lt (root_j_pos N L hL k)
  by_contra hne
  have h_hne : h ≠ 0 := by
    intro h_eq
    apply hne
    have h_eq2 : p_star N L - q = 0 := h_eq
    exact sub_eq_zero.mp h_eq2
  let s : Finset ℝ := {0} ∪ Finset.univ.image (root_j N L)
  have hs_card : s.card = N + 1 := by
    have h0_not_mem : (0 : ℝ) ∉ Finset.univ.image (root_j N L) := by
      rw [Finset.mem_image]
      intro h
      obtain ⟨j, _, hj⟩ := h
      exact Ne.symm (hdistinct_zero j) hj
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr h0_not_mem)]
    rw [Finset.card_image_of_injective _ (root_j_injective N L hL)]
    simp [Nat.add_comm]
  have hs_roots : ∀ x ∈ s, h.IsRoot x := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx0 | hxIm
    · rw [Finset.mem_singleton.mp hx0]; exact hh_zero_root
    · rw [Finset.mem_image] at hxIm
      obtain ⟨j, _, rfl⟩ := hxIm
      exact hh_roots j
  have hs_sub : s.val ⊆ h.roots := by
    intro x hx
    have hx_mem : x ∈ s := Finset.mem_val.mp hx
    have hroot : h.IsRoot x := hs_roots x hx_mem
    have hx_in_roots : x ∈ h.roots := (Polynomial.mem_roots h_hne).mpr hroot
    exact hx_in_roots
  have hle : s.card ≤ h.natDegree := Polynomial.card_le_degree_of_subset_roots hs_sub
  have hlt : N + 1 ≤ N := by
    calc N + 1 = s.card := hs_card.symm
      _ ≤ h.natDegree := hle
      _ ≤ N := hh_le
  omega
-- sched definitions
def schedD (N : ℕ) (L : ℝ) : Fin N → ℝ := fun j => -((root_j N L j)⁻¹)

def schedT (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := 0

theorem productPoly_schedD_eq_q_factor (N : ℕ) (L : ℝ) :
    productPoly (schedD N L) = q_factor N L := by
  unfold productPoly schedD q_factor
  apply Finset.prod_congr rfl
  intro j _
  have h1 : (C (1 : ℝ) + C (schedD N L j) * X : ℝ[X]) = 1 - C ((root_j N L j)⁻¹) * X := by
    have h1a : schedD N L j = -((root_j N L j)⁻¹) := rfl
    rw [h1a]
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := Polynomial.C_1
    have hCneg : C (-((root_j N L j)⁻¹)) = -C ((root_j N L j)⁻¹) := by
      simp only [Polynomial.C_neg]
    rw [hC1, hCneg]
    ring
  exact h1

theorem schedD_pN_eq_p_star (N : ℕ) (L : ℝ) (hL : 0 < L) :
    pN N (schedD N L) (schedT N) = p_star N L := by
  have h1 : pN N (schedD N L) (schedT N) = productPoly (schedD N L) := by
    unfold schedT
    exact pN_T_zero_eq_productPoly N (schedD N L)
  rw [h1, productPoly_schedD_eq_q_factor N L, ← p_star_factorization N L hL]

-- risk bounds
theorem quadratic_risk_le (N : ℕ) (L R : ℝ) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef)
    (hQL : (L • (1 : Matrix (Fin n) (Fin n) ℝ) - Q).PosSemidef)
    (e : Fin n → ℝ) (he : e ⬝ᵥ e ≤ R ^ 2) :
    let p := p_star N L
    let v := (Polynomial.aeval Q p) *ᵥ e
    v ⬝ᵥ (Q *ᵥ v) / 2 ≤ L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) := by
  intro p v
  have hB : ∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 ≤ L / (2 * (N : ℝ) + 1) ^ 2 :=
    fun x hx => p_star_weight_le N L hL x hx
  have hbound := polynomial_energy_bound Q hQ L (L / (2 * (N : ℝ) + 1) ^ 2) hQL p hB e
  have hR2_nonneg : 0 ≤ R ^ 2 := sq_nonneg R
  have hB_nonneg : 0 ≤ L / (2 * (N : ℝ) + 1) ^ 2 := by positivity
  have h1 : v ⬝ᵥ (Q *ᵥ v) ≤ L / (2 * (N : ℝ) + 1) ^ 2 * (e ⬝ᵥ e) := hbound
  have h2 : L / (2 * (N : ℝ) + 1) ^ 2 * (e ⬝ᵥ e) ≤ L / (2 * (N : ℝ) + 1) ^ 2 * R ^ 2 :=
    mul_le_mul_of_nonneg_left he hB_nonneg
  have h3 : v ⬝ᵥ (Q *ᵥ v) ≤ L / (2 * (N : ℝ) + 1) ^ 2 * R ^ 2 := le_trans h1 h2
  have h4 : v ⬝ᵥ (Q *ᵥ v) / 2 ≤ L / (2 * (N : ℝ) + 1) ^ 2 * R ^ 2 / 2 := by linarith
  have heq : L / (2 * (N : ℝ) + 1) ^ 2 * R ^ 2 / 2 = L * R ^ 2 / (2 * (2 * (N : ℝ) + 1) ^ 2) := by
    have hpos : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  linarith

theorem p_star_lossSet_isGreatest (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    IsGreatest (lossSet L R (p_star N L)) (R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2)) := by
  have h_at : L * (p_star N L).eval L ^ 2 = L / (2 * (N : ℝ) + 1) ^ 2 := p_star_weight_at_L N L hL
  have hmax : ∀ x ∈ Set.Icc 0 L, x * (p_star N L).eval x ^ 2 ≤ L * (p_star N L).eval L ^ 2 := by
    intro x hx
    calc x * (p_star N L).eval x ^ 2 ≤ L / (2 * (N : ℝ) + 1) ^ 2 := p_star_weight_le N L hL x hx
      _ = L * (p_star N L).eval L ^ 2 := h_at.symm
  have h := isGreatest_lossSet L R (p_star N L) L ⟨hL.le, le_refl _⟩ hmax
  have heq : R ^ 2 / 2 * (L * (p_star N L).eval L ^ 2) = R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) := by rw [h_at]
  rw [heq] at h
  exact h

theorem historyLossSet_schedD_isGreatest (N : ℕ) (L R : ℝ) (hL : 0 < L) :
    IsGreatest (historyLossSet N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R)
      (R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2)) := by
  have h_eq : historyLossSet N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R =
      lossSet L R (p_star N L) := by
    have h1 : QuadraticFoundations.pIter N (schedD N L) (schedT N) N = p_star N L := by
      have h2 := schedD_pN_eq_p_star N L hL
      unfold pN at h2
      exact h2
    have h2 : historyLossSet N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R =
        lossSet L R (QuadraticFoundations.pIter N (schedD N L) (schedT N) N) := by
      exact QuadraticSpectral.historyLossSet_eq N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R
    rw [h2, h1]
  rw [h_eq]
  exact p_star_lossSet_isGreatest N L R hL

theorem history_risk_value (N : ℕ) (L R : ℝ) (hL : 0 < L) (hL0 : 0 ≤ L) :
    ∃ μ ∈ Set.Icc 0 L,
      let p := QuadraticFoundations.pIter N (schedD N L) (schedT N : Matrix (Fin N) (Fin N) ℝ) N
      (∀ x ∈ Set.Icc 0 L, x * p.eval x ^ 2 ≤ μ * p.eval μ ^ 2) ∧
      sSup (historyLossSet N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R) =
        R ^ 2 / 2 * (μ * p.eval μ ^ 2) := by
  have h_eq : QuadraticFoundations.pIter N (schedD N L) (schedT N : Matrix (Fin N) (Fin N) ℝ) N = p_star N L :=
    schedD_pN_eq_p_star N L hL
  have h_hist_eq : historyLossSet N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R =
      lossSet L R (p_star N L) := by
    calc historyLossSet N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R
        = lossSet L R (QuadraticFoundations.pIter N (schedD N L) (schedT N) N) := QuadraticSpectral.historyLossSet_eq N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R
      _ = lossSet L R (p_star N L) := by rw [h_eq]
  have h_greatest := p_star_lossSet_isGreatest N L R hL
  refine ⟨L, ⟨hL.le, le_refl _⟩, ?_, ?_⟩
  · intro x hx
    have hle : x * (p_star N L).eval x ^ 2 ≤ L / (2 * (N : ℝ) + 1) ^ 2 := p_star_weight_le N L hL x hx
    have hat : L * (p_star N L).eval L ^ 2 = L / (2 * (N : ℝ) + 1) ^ 2 := p_star_weight_at_L N L hL
    have h_eq2 : QuadraticFoundations.pIter N (schedD N L) (schedT N) N = p_star N L := h_eq
    rw [h_eq2] at *
    linarith
  · have hL_weight : L * (p_star N L).eval L ^ 2 = L / (2 * (N : ℝ) + 1) ^ 2 := p_star_weight_at_L N L hL
    have hsSup : sSup (lossSet L R (p_star N L)) = R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) :=
      h_greatest.isLUB.csSup_eq ⟨_, h_greatest.1⟩
    have h_final : sSup (historyLossSet N (schedD N L) ⟨schedT N, by intro i j hij; simp [schedT]⟩ L R) = R ^ 2 / 2 * (L / (2 * (N : ℝ) + 1) ^ 2) := by
      rw [h_hist_eq, hsSup]
    rw [h_final]
    have h_eq2 : QuadraticFoundations.pIter N (schedD N L) (schedT N) N = p_star N L := h_eq
    rw [h_eq2, hL_weight]


end QuadraticLower
