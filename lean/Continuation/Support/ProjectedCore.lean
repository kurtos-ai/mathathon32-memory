module
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Matrix.Basic
/-!
# Checked projected-method support lemmas

Coverage: projection existence and the variational/norm-minimizer equivalence,
plus normalization algebra for correction registers. This module does not
claim the projected rank theorem, exact projected loss model, or decision
procedure.
-/
@[expose] public section
open InnerProductSpace
namespace Continuation.ProjectedSupport

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]

def ProjRelation (K : Set E) (u x : E) : Prop :=
  x ∈ K ∧ ∀ v ∈ K, @inner ℝ E _ (u - x) (v - x) ≤ 0

theorem proj_iff_variational' {K : Set E} (hKconv : Convex ℝ K) {u x : E} (hx : x ∈ K) :
    (‖u - x‖ = ⨅ w : K, ‖u - w‖) ↔ (∀ v ∈ K, @inner ℝ E _ (u - x) (v - x) ≤ 0) :=
  norm_eq_iInf_iff_real_inner_le_zero hKconv hx

theorem proj_iff_variational {K : Set E} (hKconv : Convex ℝ K) {u x : E} (hx : x ∈ K) :
    (‖u - x‖ = ⨅ w : K, ‖u - w‖) ↔ ProjRelation K u x := by
  rw [proj_iff_variational' hKconv hx]
  constructor
  · intro h; exact ⟨hx, h⟩
  · intro h; exact h.2

theorem proj_unique {K : Set E} (hKconv : Convex ℝ K) {u x1 x2 : E}
    (h1 : ProjRelation K u x1) (h2 : ProjRelation K u x2) :
    x1 = x2 := by
  have h1i : ∀ v ∈ K, @inner ℝ E _ (u - x1) (v - x1) ≤ (0 : ℝ) := h1.2
  have h2i : ∀ v ∈ K, @inner ℝ E _ (u - x2) (v - x2) ≤ (0 : ℝ) := h2.2
  have h12 : @inner ℝ E _ (u - x1) (x2 - x1) ≤ (0 : ℝ) := h1i x2 h2.1
  have h21 : @inner ℝ E _ (u - x2) (x1 - x2) ≤ (0 : ℝ) := h2i x1 h1.1
  have hsum : @inner ℝ E _ (x1 - x2) (x1 - x2) ≤ (0 : ℝ) := by
    have hle : @inner ℝ E _ (u - x1) (x2 - x1) + @inner ℝ E _ (u - x2) (x1 - x2) ≤ (0 : ℝ) := add_nonpos h12 h21
    have heq : @inner ℝ E _ (u - x1) (x2 - x1) + @inner ℝ E _ (u - x2) (x1 - x2) = @inner ℝ E _ (x1 - x2) (x1 - x2) := by
      have h1' : @inner ℝ E _ (u - x2) (x1 - x2) = @inner ℝ E _ ((u - x1) + (x1 - x2)) (x1 - x2) := by congr 1; abel
      rw [h1']
      rw [inner_add_left]
      have hsym : @inner ℝ E _ (u - x1) (x2 - x1) = - @inner ℝ E _ (u - x1) (x1 - x2) := by
        have : (x2 - x1 : E) = - (x1 - x2) := by abel
        rw [this, inner_neg_right]
      rw [hsym]
      ring
    linarith
  have hnorm : ‖x1 - x2‖ ^ 2 ≤ (0 : ℝ) := by rw [← real_inner_self_eq_norm_sq]; exact hsum
  have hnorm0 : ‖x1 - x2‖ = 0 := by
    have hsq_nn : (0 : ℝ) ≤ ‖x1 - x2‖ ^ 2 := sq_nonneg _
    have heq : ‖x1 - x2‖ ^ 2 = 0 := le_antisymm hnorm hsq_nn
    exact pow_eq_zero_iff (by norm_num) |>.mp heq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

noncomputable def piK {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (u : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hKne hKclosed.isComplete hKconv u)

theorem piK_spec {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (u : E) :
    piK hKconv hKclosed hKne u ∈ K ∧ ‖u - piK hKconv hKclosed hKne u‖ = ⨅ w : K, ‖u - w‖ :=
  Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hKne hKclosed.isComplete hKconv u)

theorem piK_mem {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (u : E) : piK hKconv hKclosed hKne u ∈ K :=
  (piK_spec hKconv hKclosed hKne u).1

theorem piK_norm_eq {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) (u : E) : ‖u - piK hKconv hKclosed hKne u‖ = ⨅ w : K, ‖u - w‖ :=
  (piK_spec hKconv hKclosed hKne u).2

theorem proj_graph_correct {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) {u x : E} :
    ProjRelation K u x ↔ x = piK hKconv hKclosed hKne u := by
  constructor
  · intro h
    have hnorm : ‖u - x‖ = ⨅ w : K, ‖u - w‖ := (proj_iff_variational hKconv h.1).mpr h
    have hpi_norm := piK_norm_eq hKconv hKclosed hKne u
    have hpi_mem := piK_mem hKconv hKclosed hKne u
    have hpi_proj : ProjRelation K u (piK hKconv hKclosed hKne u) :=
      (proj_iff_variational hKconv hpi_mem).mp hpi_norm
    exact proj_unique hKconv h hpi_proj
  · intro heq
    rw [heq]
    have hpi_mem := piK_mem hKconv hKclosed hKne u
    have hpi_norm := piK_norm_eq hKconv hKclosed hKne u
    exact (proj_iff_variational hKconv hpi_mem).mp hpi_norm

theorem piK_of_mem {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) {x : E} (hx : x ∈ K) : piK hKconv hKclosed hKne x = x := by
  have hproj : ProjRelation K x x := by
    constructor
    · exact hx
    · intro v _
      simp [sub_self, inner_zero_left]
  exact (proj_graph_correct hKconv hKclosed hKne).mp hproj |>.symm

theorem piK_singleton {a : E} (u : E) :
    piK (K := ({a} : Set E)) (by simp [convex_singleton]) isClosed_singleton ⟨a, rfl⟩ u = a := by
  have hKconv : Convex ℝ ({a} : Set E) := convex_singleton a
  have hKclosed : IsClosed ({a} : Set E) := isClosed_singleton
  have hKne : ({a} : Set E).Nonempty := ⟨a, rfl⟩
  have hmem : (a : E) ∈ ({a} : Set E) := rfl
  have hproj : ProjRelation ({a} : Set E) u a := by
    constructor
    · exact hmem
    · intro v hv
      have hv_eq : v = a := by simpa using hv
      rw [hv_eq]
      simp [sub_self, inner_zero_right]
  have hnorm : ‖u - a‖ = ⨅ w : ({a} : Set E), ‖u - w‖ := (proj_iff_variational hKconv hmem).mpr hproj
  have hpi_mem := piK_mem hKconv hKclosed hKne u
  have hpi_norm := piK_norm_eq hKconv hKclosed hKne u
  have hpi_proj : ProjRelation ({a} : Set E) u (piK hKconv hKclosed hKne u) :=
    (proj_iff_variational hKconv hpi_mem).mp hpi_norm
  have huniq : a = piK hKconv hKclosed hKne u := by
    have h1i : ∀ v ∈ ({a} : Set E), @inner ℝ E _ (u - a) (v - a) ≤ 0 := hproj.2
    have h2i : ∀ v ∈ ({a} : Set E), @inner ℝ E _ (u - piK hKconv hKclosed hKne u) (v - piK hKconv hKclosed hKne u) ≤ 0 := hpi_proj.2
    have h12 : @inner ℝ E _ (u - a) (piK hKconv hKclosed hKne u - a) ≤ 0 := h1i _ hpi_mem
    have h21 : @inner ℝ E _ (u - piK hKconv hKclosed hKne u) (a - piK hKconv hKclosed hKne u) ≤ 0 := h2i _ hmem
    have hsum : @inner ℝ E _ (a - piK hKconv hKclosed hKne u) (a - piK hKconv hKclosed hKne u) ≤ 0 := by
      have hle : @inner ℝ E _ (u - a) (piK hKconv hKclosed hKne u - a) + @inner ℝ E _ (u - piK hKconv hKclosed hKne u) (a - piK hKconv hKclosed hKne u) ≤ 0 := add_nonpos h12 h21
      have heq : @inner ℝ E _ (u - a) (piK hKconv hKclosed hKne u - a) + @inner ℝ E _ (u - piK hKconv hKclosed hKne u) (a - piK hKconv hKclosed hKne u) = @inner ℝ E _ (a - piK hKconv hKclosed hKne u) (a - piK hKconv hKclosed hKne u) := by
        have h1' : @inner ℝ E _ (u - piK hKconv hKclosed hKne u) (a - piK hKconv hKclosed hKne u) = @inner ℝ E _ ((u - a) + (a - piK hKconv hKclosed hKne u)) (a - piK hKconv hKclosed hKne u) := by congr 1; abel
        rw [h1', inner_add_left]
        have hsym : @inner ℝ E _ (u - a) (piK hKconv hKclosed hKne u - a) = - @inner ℝ E _ (u - a) (a - piK hKconv hKclosed hKne u) := by
          have : (piK hKconv hKclosed hKne u - a : E) = - (a - piK hKconv hKclosed hKne u) := by abel
          rw [this, inner_neg_right]
        rw [hsym]; ring
      linarith
    have hnorm2 : ‖a - piK hKconv hKclosed hKne u‖ ^ 2 ≤ 0 := by rw [← real_inner_self_eq_norm_sq]; exact hsum
    have h0 : ‖a - piK hKconv hKclosed hKne u‖ = 0 := by
      have hnn : 0 ≤ ‖a - piK hKconv hKclosed hKne u‖ ^ 2 := sq_nonneg _
      have heq : ‖a - piK hKconv hKclosed hKne u‖ ^ 2 = 0 := le_antisymm hnorm2 hnn
      exact pow_eq_zero_iff (by norm_num) |>.mp heq
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  exact huniq.symm


structure ProjectedMachine (K : Set E) (N s : ℕ) where
  F : Fin N → Matrix (Fin s) (Fin s) ℝ
  b : Fin N → (Fin s → ℝ)
  p : Fin N → (Fin s → ℝ)
  c : Fin (N+1) → (Fin s → ℝ)
  c0_e1 : (∑ i : Fin s, c ⟨0, by omega⟩ i * (if i.val = 0 then (1 : ℝ) else 0)) = 1
  cp_one : ∀ k : Fin N, (∑ i : Fin s, c ⟨k.val+1, by omega⟩ i * p k i) = 1

/-- Initial register state `e1 ⊗ x0`. -/
def e1Vec (s : ℕ) : Fin s → ℝ := fun i => if i.val = 0 then 1 else 0
def weightedSum {E} [AddCommGroup E] [Module ℝ E] {s : ℕ} (coeff : Fin s → ℝ) (state : Fin s → E) : E :=
  ∑ i : Fin s, coeff i • state i
def initState {E} [AddCommGroup E] [Module ℝ E] (s : ℕ) (x0 : E) : Fin s → E :=
  fun i => (e1Vec s i) • x0
noncomputable def projStateAux {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (g : Fin N → E) : ℕ → (Fin s → E)
  | 0 => initState s x0
  | n+1 =>
    if h : n < N then
      let Zk := projStateAux hKconv hKclosed hKne M x0 g n
      let hatZ : Fin s → E := fun r => (∑ j : Fin s, M.F ⟨n, h⟩ r j • Zk j) + M.b ⟨n, h⟩ r • g ⟨n, h⟩
      let hatU : E := weightedSum (M.c ⟨n+1, by omega⟩) hatZ
      let delta : E := piK hKconv hKclosed hKne hatU - hatU
      fun r => hatZ r + M.p ⟨n, h⟩ r • delta
    else projStateAux hKconv hKclosed hKne M x0 g n
noncomputable def projQuery {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (M : ProjectedMachine K N s) (x0 : E) (g : Fin N → E) (k : Fin (N+1)) : E :=
  weightedSum (M.c k) (projStateAux hKconv hKclosed hKne M x0 g k.val)
noncomputable def directStateAux {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (x0 : E) (g : Fin N → E) : ℕ → E
  | 0 => x0
  | n+1 =>
    if h : n < N then
      let xk := directStateAux hKconv hKclosed hKne W x0 g n
      let d_k : ℝ := W ⟨n+1, by omega⟩ ⟨n, by omega⟩
      let inc : E := d_k • g ⟨n, by omega⟩ + ∑ j : Fin n, (W ⟨n+1, by omega⟩ ⟨j.val, by omega⟩ - W ⟨n, by omega⟩ ⟨j.val, by omega⟩) • g ⟨j.val, by omega⟩
      let u : E := xk + inc
      piK hKconv hKclosed hKne u
    else directStateAux hKconv hKclosed hKne W x0 g n
theorem weightedSum_initState {s : ℕ} {x0 : E} (c0 : Fin s → ℝ) (h : (∑ i : Fin s, c0 i * e1Vec s i) = 1) :
    weightedSum c0 (initState s (E:=E) x0) = x0 := by
  unfold weightedSum initState
  have hsum : (∑ i : Fin s, c0 i • ((e1Vec s i) • x0)) = (∑ i : Fin s, (c0 i * e1Vec s i) • x0) := by
    apply Finset.sum_congr rfl; intro i _; rw [mul_smul]
  rw [hsum, ← Finset.sum_smul, h]; simp
theorem correction_algebra {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) (hKne : K.Nonempty) (M : ProjectedMachine K N s) (k : Fin N) (hatZ : Fin s → E) :
    weightedSum (M.c ⟨k.val+1, by omega⟩) (fun r => hatZ r + M.p k r • (piK hKconv hKclosed hKne (weightedSum (M.c ⟨k.val+1, by omega⟩) hatZ) - weightedSum (M.c ⟨k.val+1, by omega⟩) hatZ)) = piK hKconv hKclosed hKne (weightedSum (M.c ⟨k.val+1, by omega⟩) hatZ) := by
  set hatU := weightedSum (M.c ⟨k.val+1, by omega⟩) hatZ
  set delta := piK hKconv hKclosed hKne hatU - hatU
  have h1 : (∑ i : Fin s, M.c ⟨k.val+1, by omega⟩ i • (hatZ i + M.p k i • delta)) = (∑ i : Fin s, (M.c ⟨k.val+1, by omega⟩ i • hatZ i + M.c ⟨k.val+1, by omega⟩ i • (M.p k i • delta))) := by
    apply Finset.sum_congr rfl; intro i _; rw [smul_add]
  have h2 : (∑ i : Fin s, M.c ⟨k.val+1, by omega⟩ i • hatZ i) = hatU := rfl
  have h3 : (∑ i : Fin s, M.c ⟨k.val+1, by omega⟩ i • (M.p k i • delta)) = (∑ i : Fin s, (M.c ⟨k.val+1, by omega⟩ i * M.p k i) • delta) := by
    apply Finset.sum_congr rfl; intro i _; rw [mul_smul]
  calc weightedSum (M.c ⟨k.val+1, by omega⟩) (fun r => hatZ r + M.p k r • delta)
      = ∑ i : Fin s, M.c ⟨k.val+1, by omega⟩ i • (hatZ i + M.p k i • delta) := rfl
    _ = (∑ i : Fin s, M.c ⟨k.val+1, by omega⟩ i • hatZ i) + (∑ i : Fin s, M.c ⟨k.val+1, by omega⟩ i • (M.p k i • delta)) := by rw [h1, Finset.sum_add_distrib]
    _ = hatU + (∑ i : Fin s, (M.c ⟨k.val+1, by omega⟩ i * M.p k i) • delta) := by rw [h2, h3]
    _ = hatU + (1 : ℝ) • delta := by rw [← Finset.sum_smul, M.cp_one k]
    _ = piK hKconv hKclosed hKne hatU := by simp only [delta, one_smul]; abel

end Continuation.ProjectedSupport
