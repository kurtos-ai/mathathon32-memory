module
public import Continuation.GJP.OptimalFactors
public import Mathlib.Topology.Instances.Matrix

@[expose] public section
noncomputable section
open Matrix Filter Topology
namespace GJP
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma isClosed_posSemidef : IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  have hherm : IsClosed {M : Matrix n n ℝ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hquad : IsClosed {M : Matrix n n ℝ | ∀ x : n → ℝ, 0 ≤ star x ⬝ᵥ M *ᵥ x} := by
    have heq : {M : Matrix n n ℝ | ∀ x : n → ℝ, 0 ≤ star x ⬝ᵥ M *ᵥ x} =
        ⋂ x : n → ℝ, {M : Matrix n n ℝ | 0 ≤ star x ⬝ᵥ M *ᵥ x} := by ext; simp
    rw [heq]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (continuous_const.dotProduct
      (continuous_id.matrix_mulVec continuous_const))
  have heq : {M : Matrix n n ℝ | M.PosSemidef} =
      {M : Matrix n n ℝ | M.IsHermitian} ∩
      {M : Matrix n n ℝ | ∀ x : n → ℝ, 0 ≤ star x ⬝ᵥ M *ᵥ x} := by
    ext M
    exact Matrix.posSemidef_iff_dotProduct_mulVec
  rw [heq]
  exact hherm.inter hquad

lemma matrix_entry_tendsto {Ms : ℕ → Matrix n n ℝ} {M : Matrix n n ℝ}
    (hM : Tendsto Ms atTop (𝓝 M)) (i j : n) : Tendsto (fun k => Ms k i j) atTop (𝓝 (M i j)) :=
  (continuous_apply_apply i j).tendsto M |>.comp hM

lemma limit_eq_of_forall {xs : ℕ → ℝ} {x c : ℝ} (hx : Tendsto xs atTop (𝓝 x))
    (hc : ∀ k, xs k = c) : x = c := by
  have hconst : xs = (fun _ => c) := funext hc
  rw [hconst] at hx
  exact tendsto_nhds_unique hx tendsto_const_nhds

variable [LinearOrder n]

lemma UnitLower.of_tendsto {Cs : ℕ → Matrix n n ℝ} {C : Matrix n n ℝ}
    (hC : Tendsto Cs atTop (𝓝 C)) (hs : ∀ k, UnitLower (Cs k)) : UnitLower C := by
  constructor
  · intro i j hij
    exact limit_eq_of_forall (matrix_entry_tendsto hC i j) (fun k => (hs k).1 hij)
  · intro i
    exact limit_eq_of_forall (matrix_entry_tendsto hC i i) (fun k => (hs k).2 i)

/-- All original triangular-factor constraints are closed under entrywise limits. -/
theorem TCAdmissible.of_tendsto (last : n) {Ts Cs : ℕ → Matrix n n ℝ}
    {T C : Matrix n n ℝ} (hT : Tendsto Ts atTop (𝓝 T)) (hC : Tendsto Cs atTop (𝓝 C))
    (hs : ∀ k, TCAdmissible last (Ts k) (Cs k)) : TCAdmissible last T C := by
  have hprod : Tendsto (fun k => Ts k*Cs k) atTop (𝓝 (T*C)) := hT.mul hC
  have hrows : Tendsto (fun k => (Ts k*Cs k)*ᵥ(fun _ => (1:ℝ))) atTop
      (𝓝 ((T*C)*ᵥ(fun _ => (1:ℝ)))) :=
    (continuous_id.matrix_mulVec continuous_const).tendsto (T*C) |>.comp hprod
  have hcols : Tendsto (fun k => (Ts k*Cs k)ᵀ*ᵥ(fun _ => (1:ℝ))) atTop
      (𝓝 ((T*C)ᵀ*ᵥ(fun _ => (1:ℝ)))) :=
    (continuous_id.matrix_transpose.matrix_mulVec continuous_const).tendsto (T*C) |>.comp hprod
  constructor
  · intro i j hij
    exact limit_eq_of_forall (matrix_entry_tendsto hT i j) (fun k => (hs k).upper hij)
  · intro i
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (matrix_entry_tendsto hT i i)
      (Eventually.of_forall (fun k => (hs k).diagNonneg i))
  · intro i j hij
    exact le_of_tendsto_of_tendsto (matrix_entry_tendsto hT i j) tendsto_const_nhds
      (Eventually.of_forall (fun k => (hs k).upperNonpos i j hij))
  · exact UnitLower.of_tendsto hC (fun k => (hs k).unitLower)
  · intro i j hij
    exact le_of_tendsto_of_tendsto (matrix_entry_tendsto hC i j) tendsto_const_nhds
      (Eventually.of_forall (fun k => (hs k).lowerNonpos i j hij))
  · intro i j hij
    exact le_of_tendsto_of_tendsto (matrix_entry_tendsto hprod i j) tendsto_const_nhds
      (Eventually.of_forall (fun k => (hs k).productOffdiag i j hij))
  · intro i
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ((tendsto_pi_nhds.mp hrows) i)
      (Eventually.of_forall (fun k => (hs k).rowBound i))
  · intro i
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ((tendsto_pi_nhds.mp hcols) i)
      (Eventually.of_forall (fun k => (hs k).columnBound i))

/-- The actual bordered matrix is polynomial in the factors and the rate. -/
lemma continuous_equation15Matrix (last : n) (W : Matrix n n ℝ) :
    Continuous (fun p : (Matrix n n ℝ × Matrix n n ℝ) × ℝ =>
      equation15Matrix last W p.1.1 p.1.2 p.2) := by
  unfold equation15Matrix borderedMatrix matrixSymm
  fun_prop

/-- Passage to a limit preserves the actual PSD condition in (15). -/
theorem equation15_psd_of_tendsto (last : n) (W : Matrix n n ℝ)
    {Ts Cs : ℕ → Matrix n n ℝ} {rs : ℕ → ℝ} {T C : Matrix n n ℝ} {r : ℝ}
    (hT : Tendsto Ts atTop (𝓝 T)) (hC : Tendsto Cs atTop (𝓝 C))
    (hr : Tendsto rs atTop (𝓝 r))
    (hPSD : ∀ k, (equation15Matrix last W (Ts k) (Cs k) (rs k)).PosSemidef) :
    (equation15Matrix last W T C r).PosSemidef := by
  apply isClosed_posSemidef.mem_of_tendsto
    ((continuous_equation15Matrix last W).tendsto ((T,C),r) |>.comp
      ((hT.prodMk_nhds hC).prodMk_nhds hr))
  exact Eventually.of_forall hPSD

end GJP
