module
public import Continuation.RootIsolation.AlgebraicSign

/-!
# Rational representatives of every root-free sign region

The separating grid of the certified isolator contains a representative of every sign region
between roots. This module proves the statement for all real inputs, including the two unbounded
regions, and supplies an executable nonzero product for any finite polynomial family.
-/

@[expose] public section
open Polynomial RootIsolation.SimpleRoots
namespace RootIsolation.Executable

/-- The rational grid covers every real point in the bounded interval, whether or not it is a root. -/
theorem partition_cover_of_abs_le (B delta : ℚ) (hB : 0 < B) (hd : 0 < delta)
    (x : ℝ) (hx : |x| ≤ (B : ℝ)) :
    ∃ a b : ℚ, (a, b) ∈ RootIsolation.consecutivePairs (RootIsolation.partitionPoints B delta) ∧
      x ∈ Set.Icc (a : ℝ) (b : ℝ) := by
  let N := RootIsolation.numSteps B delta
  have hN : 0 < N := by
    simp only [N, RootIsolation.numSteps, not_le.mpr hd, ite_false]
    exact Nat.ceil_pos.mpr (by positivity)
  have hdR : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hd
  have hceil : (2 * B / delta : ℚ) ≤ (N : ℚ) := by
    simp only [N, RootIsolation.numSteps, not_le.mpr hd, ite_false]
    exact Nat.le_ceil _
  have hceilR : 2 * (B : ℝ) / (delta : ℝ) ≤ (N : ℝ) := by exact_mod_cast hceil
  let t : ℝ := (x + (B : ℝ)) / (delta : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (by linarith [(abs_le.mp hx).1]) hdR.le
  have htN : t ≤ (N : ℝ) := by
    apply le_trans _ hceilR
    apply div_le_div_of_nonneg_right _ hdR.le
    linarith [(abs_le.mp hx).2]
  let k := min ⌊t⌋₊ (N - 1)
  have hkN : k + 1 ≤ N := by
    have := Nat.min_le_right ⌊t⌋₊ (N - 1)
    dsimp only [k]
    omega
  have hkt : (k : ℝ) ≤ t := by
    apply le_trans _ (Nat.floor_le ht0)
    exact_mod_cast (Nat.min_le_left ⌊t⌋₊ (N - 1))
  have htk : t ≤ ((k + 1 : ℕ) : ℝ) := by
    by_cases hfloor : ⌊t⌋₊ ≤ N - 1
    · have hk : k = ⌊t⌋₊ := Nat.min_eq_left hfloor
      rw [hk]
      exact_mod_cast (Nat.lt_floor_add_one t).le
    · have hk : k = N - 1 := Nat.min_eq_right (by omega)
      rw [hk, Nat.sub_add_cancel (by omega : 1 ≤ N)]
      exact htN
  let a : ℚ := -B + (k : ℚ) * delta
  let b : ℚ := -B + ((k + 1 : ℕ) : ℚ) * delta
  have hklen : k + 1 < (RootIsolation.partitionPoints B delta).length := by
    rw [RootIsolation.partitionPoints_length]
    change k + 1 < N + 1
    omega
  have hmem := RootIsolation.consecutivePairs_mem (RootIsolation.partitionPoints B delta) k hklen
  simp only [RootIsolation.partitionPoints_get] at hmem
  refine ⟨a, b, hmem, ?_, ?_⟩
  · have hm : (k : ℝ) * (delta : ℝ) ≤ x + (B : ℝ) := (le_div_iff₀ hdR).mp hkt
    dsimp only [a]
    push_cast
    linarith
  · have hm : x + (B : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (delta : ℝ) :=
      (div_le_iff₀ hdR).mp htk
    dsimp only [b]
    push_cast at hm ⊢
    linarith

lemma grid_cell_roots_unique (f : Poly) (hf : denote f ≠ 0) (a b : ℚ)
    (hab : (a, b) ∈ RootIsolation.consecutivePairs
      (RootIsolation.partitionPoints (rootBound f) (gridStep f)))
    (x y : ℝ) (hx : (denote f).aeval x = 0) (hy : (denote f).aeval y = 0)
    (hxI : x ∈ Set.Icc (a : ℝ) (b : ℝ)) (hyI : y ∈ Set.Icc (a : ℝ) (b : ℝ)) : x = y := by
  by_contra hxy
  have hxq := (squarefreePart_aeval_iff f hf x).mpr hx
  have hyq := (squarefreePart_aeval_iff f hf y).mpr hy
  rw [squarefreePart_refines] at hxq hyq
  have hsep : (epsilon f : ℝ) ≤ |x - y| := by
    rw [epsilon_refines f hf]
    exact RootIsolation.Effective.roots_separated (denote f) hf x y hxq hyq hxy
  have hwidth := partition_interval_length' (rootBound f) (gridStep f) a b hab
  have hwidthR : (b : ℝ) - (a : ℝ) = (gridStep f : ℝ) := by
    rw [hwidth]
    push_cast
    ring
  have hdist : |x - y| ≤ (b : ℝ) - (a : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hxI.1, hxI.2, hyI.1, hyI.2]
  have heps : (0 : ℝ) < (epsilon f : ℝ) := by
    exact_mod_cast (by rw [epsilon_refines f hf]; exact RootIsolation.Effective.epsilon_pos _ hf :
      0 < epsilon f)
  have hstep : (gridStep f : ℝ) < (epsilon f : ℝ) := by
    unfold gridStep
    push_cast
    linarith
  rw [hwidthR] at hdist
  linarith

lemma rootfree_endpoint_of_unique (g : ℝ → ℝ) (a x b : ℝ)
    (hax : a ≤ x) (hxb : x ≤ b) (hx : g x ≠ 0)
    (huniq : ∀ y z, g y = 0 → g z = 0 → y ∈ Set.Icc a b → z ∈ Set.Icc a b → y = z) :
    (∀ y ∈ Set.Icc a x, g y ≠ 0) ∨ (∀ y ∈ Set.Icc x b, g y ≠ 0) := by
  classical
  by_cases hleft : ∀ y ∈ Set.Icc a x, g y ≠ 0
  · exact Or.inl hleft
  · right
    push Not at hleft
    obtain ⟨y, hyI, hy⟩ := hleft
    intro z hzI hz
    have heq := huniq y z hy hz ⟨hyI.1, le_trans hyI.2 hxb⟩
      ⟨le_trans hax hzI.1, hzI.2⟩
    have hyx : y = x := le_antisymm hyI.2 (by simpa only [heq] using hzI.1)
    exact hx (hyx ▸ hy)

/-- Finite exact rational representatives, including both unbounded sign regions. -/
def signSamples (f : Poly) : List ℚ :=
  [-rootBound f, rootBound f] ++ RootIsolation.partitionPoints (rootBound f) (gridStep f)

/-- Every nonroot is joined to one computed sample by a root-free closed segment. -/
theorem exists_rootfree_sample (f : Poly) (hf : denote f ≠ 0) (x : ℝ)
    (hx : (denote f).aeval x ≠ 0) :
    ∃ r ∈ signSamples f, ∀ y ∈ Set.uIcc x (r : ℝ), (denote f).aeval y ≠ 0 := by
  have hbound (y : ℝ) (hy : (denote f).aeval y = 0) : |y| < (rootBound f : ℝ) := by
    rw [rootBound_refines]
    simpa only [RootIsolation.Effective.rootBound, Real.norm_eq_abs] using
      RootIsolation.root_norm_lt_rationalRootBound (denote f) hf y hy
  by_cases hleft : x ≤ -(rootBound f : ℝ)
  · refine ⟨-rootBound f, by simp [signSamples], ?_⟩
    intro y hy hzero
    have hy' : y ∈ Set.Icc x (-(rootBound f : ℝ)) := by
      simpa only [Rat.cast_neg, Set.uIcc_of_le hleft] using hy
    linarith [(abs_lt.mp (hbound y hzero)).1, hy'.2]
  · by_cases hright : (rootBound f : ℝ) ≤ x
    · refine ⟨rootBound f, by simp [signSamples], ?_⟩
      intro y hy hzero
      rw [Set.uIcc_of_ge hright] at hy
      linarith [(abs_lt.mp (hbound y hzero)).2, hy.1]
    · have hxB : |x| ≤ (rootBound f : ℝ) := abs_le.mpr
        ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩
      have hB : 0 < rootBound f := by
        rw [rootBound_refines]
        exact lt_of_lt_of_le zero_lt_one (RootIsolation.Effective.one_le_rootBound _)
      have hd : 0 < gridStep f := by
        rw [gridStep_refines f hf]
        exact RootIsolation.Effective.gridStep_pos _ hf
      obtain ⟨a, b, hab, hxI⟩ := partition_cover_of_abs_le (rootBound f) (gridStep f) hB hd x hxB
      have huniq := grid_cell_roots_unique f hf a b hab
      have hside := rootfree_endpoint_of_unique (fun y => (denote f).aeval y)
        (a : ℝ) x (b : ℝ) hxI.1 hxI.2 hx huniq
      obtain ⟨i, hi, hai, hbi⟩ := partitionPoints_consecutive_form' (rootBound f) (gridStep f) a b hab
      have haMem : a ∈ signSamples f := by
        apply List.mem_append.mpr
        right
        rw [hai]
        exact List.getElem_mem _
      have hbMem : b ∈ signSamples f := by
        apply List.mem_append.mpr
        right
        rw [hbi]
        exact List.getElem_mem _
      rcases hside with ha | hb
      · refine ⟨a, haMem, ?_⟩
        simpa only [Set.uIcc_of_ge hxI.1] using ha
      · refine ⟨b, hbMem, ?_⟩
        simpa only [Set.uIcc_of_le hxI.2] using hb

lemma realSign_eq_of_no_root_uIcc (p : ℚ[X]) (a b : ℝ)
    (hno : ∀ x ∈ Set.uIcc a b, p.aeval x ≠ 0) : realSign (p.aeval a) = realSign (p.aeval b) := by
  rcases le_total a b with hab | hba
  · apply realSign_eq_of_no_root p a b hab
    simpa only [Set.uIcc_of_le hab] using hno
  · apply (realSign_eq_of_no_root p b a hba _).symm
    simpa only [Set.uIcc_of_ge hba] using hno

/-- All factors have the same signs at a point and at its common rational representative. -/
theorem exists_sample_same_signs (f : Poly) (hf : denote f ≠ 0) (x : ℝ)
    (hx : (denote f).aeval x ≠ 0) :
    ∃ r ∈ signSamples f, ∀ p : Poly, (denote p = 0 ∨ denote p ∣ denote f) →
      realSign ((denote p).aeval x) = rationalSign (eval p r) := by
  obtain ⟨r, hr, hno⟩ := exists_rootfree_sample f hf x hx
  refine ⟨r, hr, ?_⟩
  intro p hp
  rcases hp with hp0 | hpf
  · simp [hp0, eval_refines, rationalSign]
  · have hnp : ∀ y ∈ Set.uIcc x (r : ℝ), (denote p).aeval y ≠ 0 := by
      intro y hy hyp
      apply hno y hy
      obtain ⟨q, hq⟩ := hpf
      rw [hq, Polynomial.aeval_mul, hyp, zero_mul]
    have hs := realSign_eq_of_no_root_uIcc (denote p) x (r : ℝ) hnp
    simpa only [aeval_coe_eq_coe_eval, realSign_cast, eval_refines] using hs

/-- Multiply all nonzero family members; the empty or all-zero family produces `1`. -/
def familyProduct : List Poly → Poly
  | [] => [1]
  | p :: ps => if trim p = [] then familyProduct ps else mul p (familyProduct ps)

@[simp] theorem familyProduct_ne_zero (ps : List Poly) : denote (familyProduct ps) ≠ 0 := by
  induction ps with
  | nil => simp [familyProduct]
  | cons p ps ih =>
    by_cases hp : trim p = []
    · simpa [familyProduct, hp] using ih
    · simp only [familyProduct, hp, ite_false, denote_mul]
      exact mul_ne_zero (mt (trim_eq_nil_iff p).mpr hp) ih

theorem familyProduct_covers (ps : List Poly) (p : Poly) (hp : p ∈ ps) :
    denote p = 0 ∨ denote p ∣ denote (familyProduct ps) := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    by_cases hq : trim q = []
    · simp only [familyProduct, hq, ite_true]
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        exact Or.inl ((trim_eq_nil_iff q).mp hq)
      · exact ih hp
    · simp only [familyProduct, hq, ite_false, denote_mul]
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        exact Or.inr (dvd_mul_right _ _)
      · rcases ih hp with hp0 | hpdvd
        · exact Or.inl hp0
        · exact Or.inr (dvd_mul_of_dvd_right hpdvd _)

end RootIsolation.Executable
