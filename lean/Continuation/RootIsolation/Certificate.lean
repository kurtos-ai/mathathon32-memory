module
public import Continuation.RootIsolation.SquarefreePreprocessing
public import Continuation.RootIsolation.CertifiedSeparation
public import Continuation.RootIsolation.Separation
public import Continuation.RootIsolation.RationalBound
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Analysis.Complex.Polynomial.Basic

set_option maxHeartbeats 400000

@[expose] public section
open Polynomial Filter Topology RootIsolation RootIsolation.SimpleRoots
namespace RootIsolation.Effective

noncomputable section

lemma squarefree_parts_eq (p : ℚ[X]) :
    RootIsolation.squarefreePart p = SquarefreePreprocessing.squarefreePart p := rfl

theorem rootMultiplicity_div_gcd_eq_one
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (p : K[X]) (hp : p ≠ 0) (a : K)
    (hq : (p / EuclideanDomain.gcd p p.derivative).IsRoot a) :
    (p / EuclideanDomain.gcd p p.derivative).rootMultiplicity a = 1 := by
  let d := EuclideanDomain.gcd p p.derivative
  let q := p / d
  have hd : d ≠ 0 := by
    intro hzero
    have h := (EuclideanDomain.gcd_eq_zero_iff (R := K[X])).mp hzero
    exact hp h.1
  have hp_eq : d * q = p := EuclideanDomain.mul_div_cancel' hd
    (EuclideanDomain.gcd_dvd_left _ _)
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hp
    rw [← hp_eq, hzero, mul_zero]
  have hpRoot : p.IsRoot a := by
    rw [← hp_eq]
    exact Polynomial.root_mul_left_of_isRoot d hq
  have hpder : p.derivative ≠ 0 := by
    intro hzero
    have hc := eq_C_of_derivative_eq_zero hzero
    apply hp
    rw [hc, Polynomial.IsRoot.def, Polynomial.eval_C] at hpRoot
    rw [hc, hpRoot, C_0]
  have hmul := Polynomial.rootMultiplicity_mul (x := a) (p := d) (q := q) (by
    rw [hp_eq]
    exact hp)
  have hgcd := SquarefreePreprocessing.rootMultiplicity_gcd_eq_min hp hpder (a := a)
  have hdermul := Polynomial.derivative_rootMultiplicity_of_root (R := K) hpRoot
  have hmp : 1 ≤ p.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hp).2 hpRoot
  rw [hp_eq] at hmul
  dsimp only [d, q] at hmul hgcd ⊢
  rw [hgcd, hdermul, SquarefreePreprocessing.nat_min_sub_one] at hmul
  omega

theorem derivative_not_isRoot_div_gcd
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (p : K[X]) (hp : p ≠ 0) (a : K)
    (hq : (p / EuclideanDomain.gcd p p.derivative).IsRoot a) :
    ¬ (p / EuclideanDomain.gcd p p.derivative).derivative.IsRoot a := by
  intro hqd
  let q := p / EuclideanDomain.gcd p p.derivative
  have hmult := rootMultiplicity_div_gcd_eq_one p hp a hq
  have hdermult := Polynomial.derivative_rootMultiplicity_of_root (R := K) hq
  have hzero : q.derivative.rootMultiplicity a = 0 := by
    dsimp only [q] at hdermult ⊢
    rw [hdermult, hmult]
  by_cases hqd0 : q.derivative = 0
  · exfalso
    have hd : EuclideanDomain.gcd p p.derivative ≠ 0 := by
      intro hzero
      exact hp ((EuclideanDomain.gcd_eq_zero_iff (R := K[X])).mp hzero).1
    have hq0 : q ≠ 0 := by
      intro hqzero
      have heq := EuclideanDomain.mul_div_cancel' hd (EuclideanDomain.gcd_dvd_left p p.derivative)
      apply hp
      rw [← heq, show p / EuclideanDomain.gcd p p.derivative = 0 from hqzero, mul_zero]
    apply hq0
    change q.IsRoot a at hq
    have hc := eq_C_of_derivative_eq_zero hqd0
    rw [hc, Polynomial.IsRoot.def, Polynomial.eval_C] at hq
    rw [hc, hq, C_0]
  · have hpos : 0 < q.derivative.rootMultiplicity a :=
      (Polynomial.rootMultiplicity_pos hqd0).2 hqd
    rw [hzero] at hpos
    exact Nat.lt_irrefl 0 hpos

lemma squarefreePart_map (p : ℚ[X]) :
    (RootIsolation.squarefreePart p).map (algebraMap ℚ ℂ) =
      p.map (algebraMap ℚ ℂ) /
        EuclideanDomain.gcd (p.map (algebraMap ℚ ℂ)) (p.map (algebraMap ℚ ℂ)).derivative := by
  simp only [RootIsolation.squarefreePart, Polynomial.map_div, Polynomial.gcd_map,
    Polynomial.derivative_map]

theorem squarefreePart_isCoprime (p : ℚ[X]) (hp : p ≠ 0) :
    IsCoprime (RootIsolation.squarefreePart p) (RootIsolation.squarefreePart p).derivative := by
  apply EuclideanDomain.isCoprime_of_dvd
  · rintro ⟨hq, -⟩
    exact RootIsolation.squarefreePart_ne_zero hp hq
  · intro r hr hr0 hrq hrqd
    let f : ℚ →+* ℂ := algebraMap ℚ ℂ
    have hrf0 : r.map f ≠ 0 := Polynomial.map_ne_zero hr0
    have hrfunit : ¬ IsUnit (r.map f) := by
      intro hu
      exact hr ((Polynomial.isUnit_map f).mp hu)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (r.map f)
      (Polynomial.degree_pos_of_ne_zero_of_nonunit hrf0 hrfunit).ne'
    have hqz : ((RootIsolation.squarefreePart p).map f).IsRoot z := by
      obtain ⟨u, hu⟩ := (Polynomial.map_dvd_map' f).2 hrq
      rw [Polynomial.IsRoot.def, hu, Polynomial.eval_mul, hz, zero_mul]
    have hqdz : ((RootIsolation.squarefreePart p).derivative.map f).IsRoot z := by
      obtain ⟨u, hu⟩ := (Polynomial.map_dvd_map' f).2 hrqd
      rw [Polynomial.IsRoot.def, hu, Polynomial.eval_mul, hz, zero_mul]
    rw [squarefreePart_map] at hqz
    rw [← Polynomial.derivative_map, squarefreePart_map] at hqdz
    exact derivative_not_isRoot_div_gcd (p.map f) (Polynomial.map_ne_zero hp) z hqz hqdz

def bezoutNormalizer (q : ℚ[X]) : ℚ[X] :=
  C ((EuclideanDomain.gcd q q.derivative).coeff 0)⁻¹

def bezoutA (q : ℚ[X]) (_h : IsCoprime q q.derivative) : ℚ[X] :=
  bezoutNormalizer q * EuclideanDomain.gcdA q q.derivative

def bezoutB (q : ℚ[X]) (_h : IsCoprime q q.derivative) : ℚ[X] :=
  bezoutNormalizer q * EuclideanDomain.gcdB q q.derivative

theorem bezoutNormalizer_mul_gcd (q : ℚ[X]) (h : IsCoprime q q.derivative) :
    bezoutNormalizer q * EuclideanDomain.gcd q q.derivative = 1 := by
  let g := EuclideanDomain.gcd q q.derivative
  have hu : IsUnit g := EuclideanDomain.gcd_isUnit_iff.mpr h
  have hdeg : g.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hu
  have hg : g = C (g.coeff 0) := eq_C_of_degree_le_zero hdeg.le
  have hc : g.coeff 0 ≠ 0 := by
    intro hzero
    rw [hg, hzero, C_0] at hu
    exact not_isUnit_zero hu
  unfold bezoutNormalizer
  change C (g.coeff 0)⁻¹ * g = 1
  calc
    C (g.coeff 0)⁻¹ * g = C (g.coeff 0)⁻¹ * C (g.coeff 0) :=
      congrArg (fun t : ℚ[X] => C (g.coeff 0)⁻¹ * t) hg
    _ = C ((g.coeff 0)⁻¹ * g.coeff 0) := Polynomial.C_mul.symm
    _ = 1 := by rw [inv_mul_cancel₀ hc, Polynomial.C_1]

theorem bezoutIdentity (q : ℚ[X]) (h : IsCoprime q q.derivative) :
    bezoutA q h * q + bezoutB q h * q.derivative = 1 := by
  calc
    bezoutA q h * q + bezoutB q h * q.derivative =
        bezoutNormalizer q * (q * EuclideanDomain.gcdA q q.derivative +
          q.derivative * EuclideanDomain.gcdB q q.derivative) := by
            simp only [bezoutA, bezoutB]
            ring
    _ = bezoutNormalizer q * EuclideanDomain.gcd q q.derivative := by
          rw [EuclideanDomain.gcd_eq_gcd_ab]
    _ = 1 := bezoutNormalizer_mul_gcd q h

def A (p : ℚ[X]) (hp : p ≠ 0) : ℚ[X] :=
  bezoutA (RootIsolation.squarefreePart p) (squarefreePart_isCoprime p hp)

def B (p : ℚ[X]) (hp : p ≠ 0) : ℚ[X] :=
  bezoutB (RootIsolation.squarefreePart p) (squarefreePart_isCoprime p hp)

theorem A_mul_squarefreePart_add_B_mul_derivative (p : ℚ[X]) (hp : p ≠ 0) :
    A p hp * RootIsolation.squarefreePart p +
      B p hp * (RootIsolation.squarefreePart p).derivative = 1 :=
  bezoutIdentity _ _

theorem bezoutIdentity_map (p : ℚ[X]) (hp : p ≠ 0) :
    (A p hp).map (algebraMap ℚ ℝ) * (RootIsolation.squarefreePart p).map (algebraMap ℚ ℝ) +
      (B p hp).map (algebraMap ℚ ℝ) *
        ((RootIsolation.squarefreePart p).map (algebraMap ℚ ℝ)).derivative = 1 := by
  have h := congrArg (fun r : ℚ[X] => r.map (algebraMap ℚ ℝ))
    (A_mul_squarefreePart_add_B_mul_derivative p hp)
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.derivative_map] using h

def rootBound (p : ℚ[X]) : ℚ := rationalRootBound p

def coefficientBound (p : ℚ[X]) (hp : p ≠ 0) : ℚ :=
  max 1 (coeffAbsSum (B p hp) (rootBound p))

def curvatureBound (p : ℚ[X]) : ℚ :=
  max 1 (coeffAbsSum (RootIsolation.squarefreePart p).derivative.derivative (rootBound p))

def epsilon (p : ℚ[X]) (hp : p ≠ 0) : ℚ :=
  separationEps (coefficientBound p hp) (curvatureBound p)

def gridStep (p : ℚ[X]) (hp : p ≠ 0) : ℚ := epsilon p hp / 2

lemma one_le_rootBound (p : ℚ[X]) : 1 ≤ rootBound p := rationalRootBound_one_le p

lemma one_le_coefficientBound (p : ℚ[X]) (hp : p ≠ 0) : 1 ≤ coefficientBound p hp :=
  le_max_left _ _

lemma one_le_curvatureBound (p : ℚ[X]) : 1 ≤ curvatureBound p := le_max_left _ _

lemma rootBound_spec (p : ℚ[X]) (hp : p ≠ 0) (x : ℝ)
    (hx : (RootIsolation.squarefreePart p).aeval x = 0) : |x| ≤ (rootBound p : ℝ) := by
  have hxp : p.aeval x = 0 := RootIsolation.root_of_squarefreePart_root p x hx
  have h := root_norm_lt_rationalRootBound p hp x hxp
  rw [Real.norm_eq_abs] at h
  exact h.le

lemma rootBound_norm_spec (p : ℚ[X]) (hp : p ≠ 0) (x : ℝ)
    (hx : (RootIsolation.squarefreePart p).aeval x = 0) : ‖x‖ ≤ (rootBound p : ℝ) := by
  rw [Real.norm_eq_abs]
  exact rootBound_spec p hp x hx

lemma coefficientBound_spec (p : ℚ[X]) (hp : p ≠ 0) :
    (coeffAbsSum (B p hp) (rootBound p) : ℝ) ≤ (coefficientBound p hp : ℝ) := by
  exact_mod_cast (le_max_right 1 (coeffAbsSum (B p hp) (rootBound p)))

lemma curvatureBound_spec (p : ℚ[X]) :
    (coeffAbsSum (RootIsolation.squarefreePart p).derivative.derivative (rootBound p) : ℝ) ≤
      (curvatureBound p : ℝ) := by
  exact_mod_cast (le_max_right 1
    (coeffAbsSum (RootIsolation.squarefreePart p).derivative.derivative (rootBound p)))

lemma epsilon_pos (p : ℚ[X]) (hp : p ≠ 0) : 0 < epsilon p hp := by
  apply separationEps_pos
  · exact lt_of_lt_of_le zero_lt_one (one_le_coefficientBound p hp)
  · exact lt_of_lt_of_le zero_lt_one (one_le_curvatureBound p)

lemma gridStep_pos (p : ℚ[X]) (hp : p ≠ 0) : 0 < gridStep p hp := by
  unfold gridStep
  exact div_pos (epsilon_pos p hp) (by norm_num)

lemma squarefreePart_derivative_ne_zero (p : ℚ[X]) (hp : p ≠ 0) (x : ℝ)
    (hx : (RootIsolation.squarefreePart p).aeval x = 0) :
    (RootIsolation.squarefreePart p).derivative.aeval x ≠ 0 := by
  rw [squarefree_parts_eq] at hx ⊢
  exact SquarefreePreprocessing.squarefree_deriv_ne_zero p hp x hx

theorem roots_separated (p : ℚ[X]) (hp : p ≠ 0) (a b : ℝ)
    (ha : (RootIsolation.squarefreePart p).aeval a = 0)
    (hb : (RootIsolation.squarefreePart p).aeval b = 0) (hab : a ≠ b) :
    (epsilon p hp : ℝ) ≤ |a - b| := by
  apply separation_ge_eps (RootIsolation.squarefreePart p)
    (RootIsolation.squarefreePart_ne_zero hp) (A p hp) (B p hp)
    (rootBound p) (coefficientBound p hp) (curvatureBound p)
    (one_le_rootBound p) (one_le_coefficientBound p hp) (one_le_curvatureBound p)
  · exact bezoutIdentity_map p hp
  · exact rootBound_spec p hp
  · exact coefficientBound_spec p hp
  · exact curvatureBound_spec p
  · exact ha
  · exact hb
  · exact hab

theorem eq_of_roots_mem_same_filteredInterval (p : ℚ[X]) (hp : p ≠ 0)
    (I : IsoInterval) (hI : I ∈ filteredIntervals (RootIsolation.squarefreePart p)
      (rootBound p) (gridStep p hp))
    (x y : ℝ) (hx : (RootIsolation.squarefreePart p).aeval x = 0)
    (hy : (RootIsolation.squarefreePart p).aeval y = 0)
    (hxI : x ∈ I.toSet) (hyI : y ∈ I.toSet) : x = y := by
  have hI0 := hI
  rw [filteredIntervals, List.mem_append, List.mem_map, List.mem_map] at hI
  rcases hI with ⟨r, hr, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩
  · change x = (r : ℝ) at hxI
    change y = (r : ℝ) at hyI
    exact hxI.trans hyI.symm
  · rw [signChangingIntervals_mem_iff] at hab
    have hwidth : b = a + gridStep p hp := partition_interval_length' _ _ _ _ hab.1
    have hwidth_real : (b : ℝ) - (a : ℝ) = (gridStep p hp : ℝ) := by
      have hcast : ((b : ℚ) : ℝ) = ((a + gridStep p hp : ℚ) : ℝ) := by rw [hwidth]
      rw [hcast]
      push_cast
      ring
    by_contra hxy
    have hsep := roots_separated p hp x y hx hy hxy
    have hxyI : |x - y| ≤ (b : ℝ) - (a : ℝ) := by
      apply abs_le.mpr
      constructor <;> dsimp only [IsoInterval.toSet] at hxI hyI <;> linarith [hxI.1, hxI.2, hyI.1, hyI.2]
    have hstep : (gridStep p hp : ℝ) < (epsilon p hp : ℝ) := by
      have he : (0 : ℝ) < (epsilon p hp : ℝ) := by exact_mod_cast epsilon_pos p hp
      unfold gridStep
      push_cast
      linarith
    rw [hwidth_real] at hxyI
    linarith

theorem existsUnique_root_of_mem_filteredInterval (p : ℚ[X]) (hp : p ≠ 0)
    (I : IsoInterval) (hI : I ∈ filteredIntervals (RootIsolation.squarefreePart p)
      (rootBound p) (gridStep p hp)) :
    ∃! x : ℝ, (RootIsolation.squarefreePart p).aeval x = 0 ∧ x ∈ I.toSet := by
  have hI0 := hI
  rw [filteredIntervals, List.mem_append, List.mem_map, List.mem_map] at hI
  rcases hI with ⟨r, hr, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩
  · rw [pointRoots_mem_iff] at hr
    have hroot : (RootIsolation.squarefreePart p).aeval (r : ℝ) = 0 := by
      rw [aeval_coe_eq_coe_eval, hr.2]
      simp
    refine ⟨(r : ℝ), ⟨hroot, rfl⟩, ?_⟩
    intro y hy
    exact eq_of_roots_mem_same_filteredInterval p hp _ hI0 y (r : ℝ) hy.1 hroot hy.2 rfl
  · rw [signChangingIntervals_mem_iff] at hab
    have hsign : (RootIsolation.squarefreePart p).aeval (a : ℝ) *
        (RootIsolation.squarefreePart p).aeval (b : ℝ) < 0 := by
      rw [aeval_coe_eq_coe_eval, aeval_coe_eq_coe_eval]
      exact_mod_cast hab.2
    have hablt : (a : ℝ) < (b : ℝ) := by
      have hwidth := partition_interval_length' (rootBound p) (gridStep p hp) a b hab.1
      have hcast : ((b : ℚ) : ℝ) = ((a + gridStep p hp : ℚ) : ℝ) := by rw [hwidth]
      have hstep : (0 : ℝ) < (gridStep p hp : ℝ) := by exact_mod_cast gridStep_pos p hp
      rw [hcast]
      push_cast
      linarith
    have hcont : ContinuousOn (fun x : ℝ => (RootIsolation.squarefreePart p).aeval x)
        (Set.Icc (a : ℝ) (b : ℝ)) := (poly_aeval_continuous _).continuousOn
    have hex : ∃ x ∈ Set.Ioo (a : ℝ) (b : ℝ),
        (RootIsolation.squarefreePart p).aeval x = 0 := by
      rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have hm : (0 : ℝ) ∈ Set.Ioo ((RootIsolation.squarefreePart p).aeval (b : ℝ))
            ((RootIsolation.squarefreePart p).aeval (a : ℝ)) := ⟨hb, ha⟩
        obtain ⟨x, hx, hzero⟩ := intermediate_value_Ioo' hablt.le hcont hm
        exact ⟨x, hx, hzero⟩
      · have hm : (0 : ℝ) ∈ Set.Ioo ((RootIsolation.squarefreePart p).aeval (a : ℝ))
            ((RootIsolation.squarefreePart p).aeval (b : ℝ)) := ⟨ha, hb⟩
        obtain ⟨x, hx, hzero⟩ := intermediate_value_Ioo hablt.le hcont hm
        exact ⟨x, hx, hzero⟩
    obtain ⟨x, hxI, hx⟩ := hex
    refine ⟨x, ⟨hx, hxI⟩, ?_⟩
    intro y hy
    exact eq_of_roots_mem_same_filteredInterval p hp _ hI0 y x hy.1 hx hy.2 hxI

def intervals (p : ℚ[X]) (hp : p ≠ 0) : List IsoInterval :=
  filteredIntervals (RootIsolation.squarefreePart p) (rootBound p) (gridStep p hp)

/-- The coverage theorem at the explicitly computed grid step, rather than an existentially
quantified step computed by an opaque proof. -/
theorem every_simple_root_mem_filteredIntervals_eps_div_two
    (p : Polynomial ℚ) (eps : ℚ) (heps : 0 < eps)
    (hsep : ∀ x y : ℝ, p.aeval x = 0 → p.aeval y = 0 → x ≠ y → (eps : ℝ) ≤ |x - y|)
    (B : ℚ) (hB : 0 < B) (hBspec : ∀ x : ℝ, p.aeval x = 0 → ‖x‖ ≤ (B : ℝ))
    (h_simple : ∀ x : ℝ, p.aeval x = 0 → p.derivative.aeval x ≠ 0) :
    ∀ x : ℝ, p.aeval x = 0 → ∃ I ∈ filteredIntervals p B (eps / 2), x ∈ I.toSet := by
  let delta : ℚ := eps / 2
  have h_delta_pos : 0 < delta := by simp [delta]; linarith
  intro x hx
  have hd : p.derivative.aeval x ≠ 0 := h_simple x hx
  have hp_ne : p ≠ 0 := by intro h_eq; simp [h_eq] at hd
  have h_cover := cover_from_cauchyBound p hp_ne B hB hBspec delta h_delta_pos x hx
  obtain ⟨a, b, h_mem, h_x_mem⟩ := h_cover
  have h_x_le : (a : ℝ) ≤ x := h_x_mem.1
  have h_x_ge : x ≤ (b : ℝ) := h_x_mem.2
  have h_b_eq : b = a + delta := partition_interval_length' B delta a b h_mem
  have h_ba_real : (b : ℝ) - (a : ℝ) = (delta : ℝ) := by
    have h_eq : b = a + delta := h_b_eq
    have h_cast : ((b : ℚ) : ℝ) = ((a + delta : ℚ) : ℝ) := by rw [h_eq]
    rw [h_cast]; push_cast; ring
  have h_delta_lt_eps : (delta : ℝ) < (eps : ℝ) := by
    show ((eps / 2 : ℚ) : ℝ) < (eps : ℝ)
    have h_eps_pos : 0 < (eps : ℝ) := by exact_mod_cast heps
    push_cast; linarith
  have h_unique_in_cell : ∀ y, p.aeval y = 0 → y ∈ Set.Icc (a : ℝ) (b : ℝ) → y = x := by
    intro y hy hy_mem
    by_contra h_ne
    have h_y_ne_x : y ≠ x := h_ne
    have h_sep_le : (eps : ℝ) ≤ |x - y| := hsep x y hx hy (Ne.symm h_y_ne_x)
    have h_dist_le : |x - y| ≤ (b : ℝ) - (a : ℝ) := by
      have ha_le_x : (a : ℝ) ≤ x := h_x_le
      have hx_le_b : x ≤ (b : ℝ) := h_x_ge
      have ha_le_y : (a : ℝ) ≤ y := hy_mem.1
      have hy_le_b : y ≤ (b : ℝ) := hy_mem.2
      apply abs_le.mpr
      constructor
      · linarith
      · linarith
    have h_le : |x - y| ≤ (delta : ℝ) := by rw [h_ba_real] at h_dist_le; exact h_dist_le
    linarith
  by_cases h_x_eq_a : x = (a : ℝ)
  · have h_eval_a : p.eval a = 0 := by
      have h_aeval : p.aeval (a : ℝ) = 0 := by rw [← h_x_eq_a]; exact hx
      have h_coe : p.aeval (a : ℝ) = ((p.eval a : ℚ) : ℝ) := aeval_coe_eq_coe_eval p a
      rw [h_coe] at h_aeval
      exact_mod_cast h_aeval
    have h_a_in : a ∈ pointRoots p B delta := by
      rw [pointRoots_mem_iff]
      constructor
      · obtain ⟨i, h_i, h_a_eq, _⟩ := partitionPoints_consecutive_form' B delta a b h_mem
        have h_i_lt : i < (partitionPoints B delta).length := Nat.lt_of_succ_lt h_i
        have h_a_eq' : a = (partitionPoints B delta)[i]'h_i_lt := h_a_eq
        rw [h_a_eq']
        exact List.getElem_mem h_i_lt
      · exact h_eval_a
    have h_iso : IsoInterval.point a ∈ filteredIntervals p B delta := by
      simp only [filteredIntervals, List.mem_append, List.mem_map]
      left
      exact ⟨a, h_a_in, rfl⟩
    exact ⟨IsoInterval.point a, h_iso, by simp [IsoInterval.toSet, h_x_eq_a]⟩
  · by_cases h_x_eq_b : x = (b : ℝ)
    · have h_eval_b : p.eval b = 0 := by
        have h_aeval : p.aeval (b : ℝ) = 0 := by rw [← h_x_eq_b]; exact hx
        have h_coe : p.aeval (b : ℝ) = ((p.eval b : ℚ) : ℝ) := aeval_coe_eq_coe_eval p b
        rw [h_coe] at h_aeval
        exact_mod_cast h_aeval
      have h_b_in : b ∈ pointRoots p B delta := by
        rw [pointRoots_mem_iff]
        constructor
        · obtain ⟨i, h_i, _, h_b_eq2⟩ := partitionPoints_consecutive_form' B delta a b h_mem
          have h_b_eq' : b = (partitionPoints B delta)[i + 1]'h_i := h_b_eq2
          rw [h_b_eq']
          exact List.getElem_mem h_i
        · exact h_eval_b
      have h_iso : IsoInterval.point b ∈ filteredIntervals p B delta := by
        simp only [filteredIntervals, List.mem_append, List.mem_map]
        left
        exact ⟨b, h_b_in, rfl⟩
      exact ⟨IsoInterval.point b, h_iso, by simp [IsoInterval.toSet, h_x_eq_b]⟩
    · have h_a_lt_x : (a : ℝ) < x := lt_of_le_of_ne h_x_le (Ne.symm h_x_eq_a)
      have h_x_lt_b : x < (b : ℝ) := lt_of_le_of_ne h_x_ge h_x_eq_b
      have h_a_not_root : p.aeval (a : ℝ) ≠ 0 := by
        intro h_eq
        have h_mem_a : (a : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨le_refl _, le_of_lt (lt_trans h_a_lt_x h_x_lt_b)⟩
        have h_eq_x : (a : ℝ) = x := h_unique_in_cell (a : ℝ) h_eq h_mem_a
        linarith
      have h_b_not_root : p.aeval (b : ℝ) ≠ 0 := by
        intro h_eq
        have h_mem_b : (b : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨le_of_lt (lt_trans h_a_lt_x h_x_lt_b), le_refl _⟩
        have h_eq_x : (b : ℝ) = x := h_unique_in_cell (b : ℝ) h_eq h_mem_b
        linarith
      have h_sign : p.aeval (a : ℝ) * p.aeval (b : ℝ) < 0 :=
        endpoint_sign_of_unique_simple_root p x (a : ℝ) (b : ℝ) hx hd h_a_lt_x h_x_lt_b h_unique_in_cell h_a_not_root h_b_not_root
      have h_prod : p.eval a * p.eval b < 0 := by
        have h_aeval_a : p.aeval (a : ℝ) = ((p.eval a : ℚ) : ℝ) := aeval_coe_eq_coe_eval p a
        have h_aeval_b : p.aeval (b : ℝ) = ((p.eval b : ℚ) : ℝ) := aeval_coe_eq_coe_eval p b
        have h_sign' : ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) < 0 := by
          rw [← h_aeval_a, ← h_aeval_b]; exact h_sign
        have h_cast : ((p.eval a * p.eval b : ℚ) : ℝ) = ((p.eval a : ℚ) : ℝ) * ((p.eval b : ℚ) : ℝ) := by push_cast; ring
        rw [← h_cast] at h_sign'
        exact_mod_cast h_sign'
      have h_open : (a, b) ∈ signChangingIntervals p B delta := by
        rw [signChangingIntervals_mem_iff]; exact ⟨h_mem, h_prod⟩
      have h_iso : IsoInterval.openInterval a b ∈ filteredIntervals p B delta := by
        simp only [filteredIntervals, List.mem_append, List.mem_map]
        right
        exact ⟨(a, b), h_open, rfl⟩
      exact ⟨IsoInterval.openInterval a b, h_iso, by simp [IsoInterval.toSet]; exact ⟨h_a_lt_x, h_x_lt_b⟩⟩

theorem every_squarefreePart_root_mem_intervals (p : ℚ[X]) (hp : p ≠ 0) (x : ℝ)
    (hx : (RootIsolation.squarefreePart p).aeval x = 0) :
    ∃ I ∈ intervals p hp, x ∈ I.toSet := by
  apply every_simple_root_mem_filteredIntervals_eps_div_two
    (RootIsolation.squarefreePart p) (epsilon p hp) (epsilon_pos p hp)
  · exact roots_separated p hp
  · exact lt_of_lt_of_le zero_lt_one (one_le_rootBound p)
  · exact rootBound_norm_spec p hp
  · exact squarefreePart_derivative_ne_zero p hp
  · exact hx

theorem every_root_mem_intervals (p : ℚ[X]) (hp : p ≠ 0) (x : ℝ)
    (hx : p.aeval x = 0) : ∃ I ∈ intervals p hp, x ∈ I.toSet := by
  apply every_squarefreePart_root_mem_intervals p hp x
  rw [squarefree_parts_eq]
  exact (SquarefreePreprocessing.squarefree_aeval_root_iff p hp x).mp hx

lemma no_partitionPoint_mem_consecutive_open (B delta a b r : ℚ) (hdelta : 0 < delta)
    (hab : (a, b) ∈ consecutivePairs (partitionPoints B delta))
    (hr : r ∈ partitionPoints B delta) : (r : ℝ) ∉ Set.Ioo (a : ℝ) (b : ℝ) := by
  obtain ⟨i, hi, hai, hbi⟩ := partitionPoints_consecutive_form' B delta a b hab
  obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hr
  have hi0 : i < (partitionPoints B delta).length := Nat.lt_of_succ_lt hi
  have ha : a = -B + (i : ℚ) * delta := by
    rw [hai]
    exact partitionPoints_get B delta i hi0
  have hb : b = -B + ((i + 1 : ℕ) : ℚ) * delta := by
    rw [hbi]
    exact partitionPoints_get B delta (i + 1) hi
  have hrr : r = -B + (j : ℚ) * delta := by
    rw [← hjr]
    exact partitionPoints_get B delta j hj
  rw [ha, hb, hrr]
  intro hmem
  rcases lt_trichotomy i j with hij | hij | hij
  · have hcoef : (((i + 1 : ℕ) : ℚ)) ≤ (j : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt hij
    have hle : -B + ((i + 1 : ℕ) : ℚ) * delta ≤ -B + (j : ℚ) * delta := by
      gcongr
    exact (not_lt_of_ge (by exact_mod_cast hle)) hmem.2
  · subst j
    exact lt_irrefl _ hmem.1
  · have hcoef : (j : ℚ) ≤ (i : ℚ) := by exact_mod_cast hij.le
    have hle : -B + (j : ℚ) * delta ≤ -B + (i : ℚ) * delta := by
      gcongr
    exact (not_lt_of_ge (by exact_mod_cast hle)) hmem.1

lemma consecutivePairs_eq_of_open_overlap (B delta a b c d : ℚ) (hdelta : 0 < delta)
    (hab : (a, b) ∈ consecutivePairs (partitionPoints B delta))
    (hcd : (c, d) ∈ consecutivePairs (partitionPoints B delta))
    (x : ℝ) (hxab : x ∈ Set.Ioo (a : ℝ) (b : ℝ))
    (hxcd : x ∈ Set.Ioo (c : ℝ) (d : ℝ)) : a = c ∧ b = d := by
  obtain ⟨i, hi, hai, hbi⟩ := partitionPoints_consecutive_form' B delta a b hab
  obtain ⟨j, hj, hcj, hdj⟩ := partitionPoints_consecutive_form' B delta c d hcd
  have hi0 : i < (partitionPoints B delta).length := Nat.lt_of_succ_lt hi
  have hj0 : j < (partitionPoints B delta).length := Nat.lt_of_succ_lt hj
  have ha : a = -B + (i : ℚ) * delta := by rw [hai]; exact partitionPoints_get B delta i hi0
  have hb : b = -B + ((i + 1 : ℕ) : ℚ) * delta := by
    rw [hbi]; exact partitionPoints_get B delta (i + 1) hi
  have hc : c = -B + (j : ℚ) * delta := by rw [hcj]; exact partitionPoints_get B delta j hj0
  have hd : d = -B + ((j + 1 : ℕ) : ℚ) * delta := by
    rw [hdj]; exact partitionPoints_get B delta (j + 1) hj
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exfalso
      have hcoef : (((i + 1 : ℕ) : ℚ)) ≤ (j : ℚ) := by
        exact_mod_cast Nat.succ_le_of_lt hij
      have hleQ : -B + ((i + 1 : ℕ) : ℚ) * delta ≤ -B + (j : ℚ) * delta := by
        gcongr
      have hle : (b : ℝ) ≤ (c : ℝ) := by
        rw [hb, hc]
        exact_mod_cast hleQ
      linarith [hxab.2, hxcd.1]
    · exact hij
    · exfalso
      have hcoef : (((j + 1 : ℕ) : ℚ)) ≤ (i : ℚ) := by
        exact_mod_cast Nat.succ_le_of_lt hij
      have hleQ : -B + ((j + 1 : ℕ) : ℚ) * delta ≤ -B + (i : ℚ) * delta := by
        gcongr
      have hle : (d : ℝ) ≤ (a : ℝ) := by
        rw [hd, ha]
        exact_mod_cast hleQ
      linarith [hxcd.2, hxab.1]
  subst j
  exact ⟨hai.trans hcj.symm, hbi.trans hdj.symm⟩

theorem eq_of_mem_intervals_of_common_point (p : ℚ[X]) (hp : p ≠ 0)
    (I J : IsoInterval) (hI : I ∈ intervals p hp) (hJ : J ∈ intervals p hp)
    (x : ℝ) (hxI : x ∈ I.toSet) (hxJ : x ∈ J.toSet) : I = J := by
  rw [intervals, filteredIntervals, List.mem_append, List.mem_map, List.mem_map] at hI hJ
  rcases hI with ⟨r, hr, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩ <;>
    rcases hJ with ⟨s, hs, rfl⟩ | ⟨⟨c, d⟩, hcd, rfl⟩
  · change x = (r : ℝ) at hxI
    change x = (s : ℝ) at hxJ
    rw [hxI] at hxJ
    exact congrArg IsoInterval.point (by exact_mod_cast hxJ)
  · rw [pointRoots_mem_iff] at hr
    rw [signChangingIntervals_mem_iff] at hcd
    exact absurd hxJ (by
      change x = (r : ℝ) at hxI
      rw [hxI]
      exact no_partitionPoint_mem_consecutive_open _ _ _ _ _ (gridStep_pos p hp) hcd.1 hr.1)
  · rw [pointRoots_mem_iff] at hs
    rw [signChangingIntervals_mem_iff] at hab
    exact absurd hxI (by
      change x = (s : ℝ) at hxJ
      rw [hxJ]
      exact no_partitionPoint_mem_consecutive_open _ _ _ _ _ (gridStep_pos p hp) hab.1 hs.1)
  · rw [signChangingIntervals_mem_iff] at hab hcd
    obtain ⟨hac, hbd⟩ := consecutivePairs_eq_of_open_overlap _ _ _ _ _ _ (gridStep_pos p hp)
      hab.1 hcd.1 x hxI hxJ
    subst c
    subst d
    rfl

theorem disjoint_intervals_of_ne (p : ℚ[X]) (hp : p ≠ 0)
    (I J : IsoInterval) (hI : I ∈ intervals p hp) (hJ : J ∈ intervals p hp)
    (hne : I ≠ J) : Disjoint I.toSet J.toSet := by
  rw [Set.disjoint_left]
  intro x hxI hxJ
  exact hne (eq_of_mem_intervals_of_common_point p hp I J hI hJ x hxI hxJ)

end
end RootIsolation.Effective
