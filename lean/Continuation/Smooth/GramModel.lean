module
public import Continuation.Smooth.ActualInterpolation
public import Continuation.Support.SmoothGramCore
public import Continuation.OracleTrajectory
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section

open Matrix
open scoped InnerProductSpace

namespace SmoothGramModel
variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def gram (B : ι → V) : Matrix ι ι ℝ := fun i j => ⟪B i,B j⟫_ℝ

theorem combination_inner (B : ι → V) (u v : ι → ℝ) :
    ⟪Fintype.linearCombination ℝ B u,Fintype.linearCombination ℝ B v⟫_ℝ =
      u ⬝ᵥ (gram B *ᵥ v) := by
  simp only [Fintype.linearCombination_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, dotProduct, mulVec, gram]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem combination_norm (B : ι → V) (u : ι → ℝ) :
    ‖Fintype.linearCombination ℝ B u‖^2 = u ⬝ᵥ (gram B *ᵥ u) := by
  rw [← real_inner_self_eq_norm_sq, combination_inner]

theorem gram_psd (B : ι → V) : (gram B).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    simp [gram, Matrix.conjTranspose_apply, real_inner_comm]
  · intro u
    simpa only [star_trivial, ← combination_norm] using
      sq_nonneg ‖Fintype.linearCombination ℝ B u‖

abbrev Index (N : ℕ) := Option (Fin (N+1))

theorem index_card (N : ℕ) : Fintype.card (Index N) = N+2 := by
  simp [Index]

noncomputable def v {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Index N → (Index N → ℝ)
  | none => 0
  | some i => Pi.single none 1 + ∑ j : Fin i.val,
      W i ⟨j.val, by omega⟩ • Pi.single (some ⟨j.val, by omega⟩) 1

noncomputable def w {N : ℕ} : Index N → (Index N → ℝ)
  | none => 0
  | some i => Pi.single (some i) 1

def value {N : ℕ} (φ : Fin (N+1) → ℝ) : Index N → ℝ
  | none => 0
  | some i => φ i

/-- The paper's finite Gram feasibility inequalities, with `none` the minimizer datum. -/
def Feasible {N : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (L R : ℝ) (M : Matrix (Index N) (Index N) ℝ) (φ : Fin (N+1) → ℝ) : Prop :=
  M.PosSemidef ∧ M none none ≤ R^2 ∧ ∀ i j : Index N,
    0 ≤ value φ i - value φ j - w j ⬝ᵥ (M *ᵥ (v W i-v W j)) -
      1/(2*L) * ((w i-w j) ⬝ᵥ (M *ᵥ (w i-w j)))

variable {N n : ℕ} {L R : ℝ}

noncomputable def site (I : SmoothAttain.Instance n L R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : Index N → EuclideanSpace ℝ (Fin n)
  | none => I.xStar
  | some i => OracleTrajectory.run W I.G I.x0 i

noncomputable def physical (I : SmoothAttain.Instance n L R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : Index N → EuclideanSpace ℝ (Fin n)
  | none => I.x0 - I.xStar
  | some i => I.G (OracleTrajectory.run W I.G I.x0 i)

noncomputable def values (I : SmoothAttain.Instance n L R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Fin (N+1)) : ℝ :=
  I.f (OracleTrajectory.run W I.G I.x0 i) - I.f I.xStar

theorem combine_v (I : SmoothAttain.Instance n L R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Index N) :
    Fintype.linearCombination ℝ (physical I W) (v W i) = site I W i-I.xStar := by
  cases i with
  | none => simp [v,site]
  | some i =>
    simp only [v, map_add, map_sum, map_smul, Fintype.linearCombination_apply_single,
      one_smul, physical, site]
    rw [OracleTrajectory.run_eq]
    abel

theorem combine_w (I : SmoothAttain.Instance n L R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Index N) :
    Fintype.linearCombination ℝ (physical I W) (w i) = I.G (site I W i) := by
  cases i with
  | none => simp [w,site,I.gradient_at_minimizer]
  | some i => simp [w,site,physical,Fintype.linearCombination_apply_single]

theorem value_values (I : SmoothAttain.Instance n L R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Index N) :
    value (values I W) i = I.f (site I W i) - I.f I.xStar := by
  cases i <;> simp [value,values,site]

theorem actual_feasible (I : SmoothAttain.Instance n L R) (hL : 0 < L)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    Feasible W L R (gram (physical I W)) (values I W) := by
  refine ⟨gram_psd _, ?_, ?_⟩
  · change ⟪I.x0-I.xStar,I.x0-I.xStar⟫_ℝ ≤ R^2
    rw [real_inner_self_eq_norm_sq]
    have hn := norm_nonneg (I.x0-I.xStar)
    have hr := I.near
    nlinarith
  · intro i j
    have hi := I.interpolation_necessary hL (site I W i) (site I W j)
    have hv : Fintype.linearCombination ℝ (physical I W) (v W i-v W j) =
        site I W i - site I W j := by
      rw [map_sub, combine_v, combine_v]
      abel
    have hw : Fintype.linearCombination ℝ (physical I W) (w i-w j) =
        I.G (site I W i) - I.G (site I W j) := by
      rw [map_sub, combine_w, combine_w]
    rw [value_values, value_values, ← combination_inner, ← combination_norm,
      combine_w, hv, hw]
    linarith

noncomputable def terminalLoss (I : SmoothAttain.Instance n L R)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : ℝ :=
  I.f (OracleTrajectory.run W I.G I.x0 (Fin.last N)) - I.f I.xStar

/-- Losses on actual functions in every positive finite dimension. -/
def actualLossSet (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R : ℝ) : Set ℝ :=
  {z | ∃ n : ℕ, ∃ I : SmoothAttain.Instance (n+1) L R, z = terminalLoss I W}

def modelLossSet (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R : ℝ) : Set ℝ :=
  {z | ∃ M : Matrix (Index N) (Index N) ℝ, ∃ φ : Fin (N+1) → ℝ,
    Feasible W L R M φ ∧ z = φ (Fin.last N)}

theorem actualLossSet_subset_modelLossSet (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R : ℝ) (hL : 0 < L) :
    actualLossSet N W L R ⊆ modelLossSet N W L R := by
  rintro z ⟨n,I,rfl⟩
  exact ⟨gram (physical I W),values I W,actual_feasible I hL W,rfl⟩

theorem actual_uniform_bound_of_model_bound (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R b : ℝ) (hL : 0 < L)
    (hb : ∀ M φ, Feasible W L R M φ → φ (Fin.last N) ≤ b) :
    ∀ z ∈ actualLossSet N W L R, z ≤ b := by
  intro z hz
  obtain ⟨M,φ,hF,rfl⟩ := actualLossSet_subset_modelLossSet N W L R hL hz
  exact hb M φ hF

end SmoothGramModel
