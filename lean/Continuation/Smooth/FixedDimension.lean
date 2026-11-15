module
public import Continuation.Smooth.GramExact
@[expose] public section
noncomputable section
open Matrix
open scoped InnerProductSpace
namespace SmoothGramModel

/-- Extend a Euclidean vector by zero coordinates. -/
def padVector {k n : ℕ} (h : k ≤ n) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if hj : j.val < k then x ⟨j.val,hj⟩ else 0)

lemma sum_padded {k n : ℕ} (h : k ≤ n) (f : Fin k → ℝ) :
    (∑ j : Fin n, if hj : j.val < k then f ⟨j.val,hj⟩ else 0) = ∑ i,f i := by
  apply Eq.symm
  apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) f
  · intro j hj
    have hnot : ¬j.val < k := by
      intro hlt
      apply hj
      exact ⟨⟨j.val,hlt⟩,by ext; rfl⟩
    simp [hnot]
  · intro i
    simp

lemma padVector_inner {k n : ℕ} (h : k ≤ n) (x y : EuclideanSpace ℝ (Fin k)) :
    ⟪padVector h x,padVector h y⟫_ℝ = ⟪x,y⟫_ℝ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change (∑ j : Fin n, (if hj : j.val < k then y ⟨j.val,hj⟩ else 0) *
    (if hj : j.val < k then x ⟨j.val,hj⟩ else 0)) = ∑ i,y i*x i
  rw [← sum_padded h (fun i => y i*x i)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

/-- Every feasible Gram matrix is realized in every dimension at least N+2. -/
theorem exists_gram_in_larger_dimension (N n : ℕ) (hn : N+2 ≤ n)
    (M : Matrix (Index N) (Index N) ℝ) (hM : M.PosSemidef) :
    ∃ B : Index N → EuclideanSpace ℝ (Fin n), gram B = M := by
  obtain ⟨B,hB⟩ := exists_gram_in_dimension N M hM
  refine ⟨fun i => padVector hn (B i),?_⟩
  ext i j
  change ⟪padVector hn (B i),padVector hn (B j)⟫_ℝ = M i j
  rw [padVector_inner]
  exact congrFun (congrFun hB i) j

/-- Actual interpolation in every sufficiently large fixed dimension. -/
theorem realize_feasible_in_dimension {N n : ℕ} {L R : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hn : N+2 ≤ n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Matrix (Index N) (Index N) ℝ) (φ : Fin (N+1) → ℝ)
    (hF : Feasible W L R M φ) :
    ∃ I : SmoothAttain.Instance n L R, terminalLoss I W = φ (Fin.last N) := by
  obtain ⟨B,hB⟩ := exists_gram_in_larger_dimension N n hn M hF.1
  obtain ⟨F,G,hGrad,hConv,hLip,hData⟩ := SmoothInterpolation.sufficient hL
    (fun i => Fintype.linearCombination ℝ B (v W i))
    (fun i => Fintype.linearCombination ℝ B (w i)) (value φ)
    (model_data_inequalities W M φ hF B hB)
  have hK : Real.toNNReal L = (⟨L,hL.le⟩ : NNReal) := by
    apply NNReal.coe_injective
    exact Real.coe_toNNReal _ hL.le
  rw [hK] at hLip
  exact realize_of_interpolant hL hR W M φ hF B hB F G hGrad hConv hLip
    (fun i => (hData i).1) (fun i => (hData i).2)

/-- The all-dimensional loss set already equals the loss set in any n≥N+2. -/
theorem actualLossSet_eq_fixed_dimension {N n : ℕ} (hn : N+2 ≤ n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) :
    actualLossSet N W L R = {z | ∃ I : SmoothAttain.Instance n L R, terminalLoss I W = z} := by
  ext z
  constructor
  · intro hz
    rw [actualLossSet_eq_modelLossSet N W L R hL hR] at hz
    rcases hz with ⟨M,φ,hF,rfl⟩
    exact realize_feasible_in_dimension hL hR hn W M φ hF
  · rintro ⟨I,rfl⟩
    have hn0 : 0 < n := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn0)
    exact ⟨k,I,rfl⟩

theorem uniform_bound_iff_fixed_dimension {N n : ℕ} (hn : N+2 ≤ n)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (L R γ : ℝ) (hL : 0 < L) (hR : 0 ≤ R) :
    (∀ z ∈ actualLossSet N W L R, z ≤ γ) ↔
      ∀ I : SmoothAttain.Instance n L R, terminalLoss I W ≤ γ := by
  rw [actualLossSet_eq_fixed_dimension hn W L R hL hR]
  constructor
  · intro h I
    exact h _ ⟨I,rfl⟩
  · rintro h z ⟨I,rfl⟩
    exact h I

end SmoothGramModel
