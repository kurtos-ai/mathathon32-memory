module
public import RealizationCore.RegisterMachine
@[expose] public section

/-!
# From a compatible family of canonical state spaces to an `s`-register machine

`chain_realizes` is the machine construction only. The sufficiency theorem must additionally
construct a `CompatibleChain` from the coefficient matrix W; that is not assumed away here.
-/

namespace RegisterMachine

noncomputable section
open Matrix Finset BigOperators

structure CompatibleChain (N s : ℕ) where
  E : Fin (N+1) → Type*
  [toAddCommGroup : ∀ k, AddCommGroup (E k)]
  [toModule : ∀ k, Module ℝ (E k)]
  J : ∀ k, E k →ₗ[ℝ] (Fin s → ℝ)
  L : ∀ k, (Fin s → ℝ) →ₗ[ℝ] E k
  D : ∀ (k : Fin N), E ⟨k.val, by omega⟩ →ₗ[ℝ] E ⟨k.val+1, by omega⟩
  h : ∀ (k : Fin N), E ⟨k.val+1, by omega⟩
  obs : ∀ k, E k →ₗ[ℝ] ℝ

attribute [instance] CompatibleChain.toAddCommGroup CompatibleChain.toModule

/-- The explicit matrix of `J_{k+1} D_k L_k`, so `mulVec` has a library formula. -/
def chainF {N s : ℕ} (C : CompatibleChain N s) (k : Fin N) : Matrix (Fin s) (Fin s) ℝ :=
  LinearMap.toMatrix' ((C.J ⟨k.val+1, by omega⟩).comp ((C.D k).comp (C.L ⟨k.val, by omega⟩)))

def chainMachine {N s : ℕ} (C : CompatibleChain N s) : Machine N s where
  F := chainF C
  b k := C.J ⟨k.val+1, by omega⟩ (C.h k)
  c k := fun i => C.obs ⟨k.val, by omega⟩ (C.L ⟨k.val, by omega⟩ (Pi.single i 1))
  o := fun i => C.obs ⟨N, by omega⟩ (C.L ⟨N, by omega⟩ (Pi.single i 1))

def ChainStateCorrect {N s : ℕ} (C : CompatibleChain N s)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (v : ∀ (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)), C.E k)
    (x0 : ℝ) (g : Fin N → ℝ) : Prop :=
  C.J (0 : Fin (N+1)) (v x0 g 0) = (fun i => e1 s i * x0) ∧
  (∀ (k : Fin N), v x0 g ⟨k.val+1, by omega⟩ =
    C.D k (v x0 g ⟨k.val, by omega⟩) + g k • C.h k) ∧
  (∀ k : Fin (N+1), C.obs k (v x0 g k) =
    x0 + ∑ j : Fin k.val, W k ⟨j.val, by omega⟩ * g ⟨j.val, by omega⟩)

lemma dot_single_linearMap {s : ℕ} (f : (Fin s → ℝ) →ₗ[ℝ] ℝ) (z : Fin s → ℝ) :
    dot (fun i => f (Pi.single i 1)) z = f z := by
  let b := Pi.basisFun ℝ (Fin s)
  have hz : ∑ i : Fin s, z i • Pi.single i (1:ℝ) = z := by
    simpa [b] using b.sum_repr z
  calc
    dot (fun i => f (Pi.single i 1)) z = ∑ i : Fin s, f (Pi.single i 1) * z i := rfl
    _ = f (∑ i : Fin s, z i • Pi.single i (1:ℝ)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [f.map_smul, smul_eq_mul, mul_comm]
    _ = f z := by rw [hz]

lemma chainF_apply {N s : ℕ} (C : CompatibleChain N s) (k : Fin N)
    (z : C.E ⟨k.val, by omega⟩)
    (hL : ∀ k z, C.L k (C.J k z) = z) :
    chainF C k *ᵥ C.J ⟨k.val, by omega⟩ z = C.J ⟨k.val+1, by omega⟩ (C.D k z) := by
  let J0 := C.J ⟨k.val, by omega⟩
  have hL0 : J0 = C.J ⟨k.val, by omega⟩ := rfl
  simp only [chainF, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, hL]

lemma chain_update {N s : ℕ} (C : CompatibleChain N s)
    (v : ∀ (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)), C.E k)
    (hL : ∀ k z, C.L k (C.J k z) = z) (x0 : ℝ) (g : Fin N → ℝ)
    (hrec : ∀ (k : Fin N), v x0 g ⟨k.val+1, by omega⟩ =
      C.D k (v x0 g ⟨k.val, by omega⟩) + g k • C.h k) (k : Fin N) :
    (fun i => (∑ j : Fin s, chainF C k i j *
      C.J ⟨k.val, by omega⟩ (v x0 g ⟨k.val, by omega⟩) j)
      + C.J ⟨k.val+1, by omega⟩ (C.h k) i * g k) =
      C.J ⟨k.val+1, by omega⟩ (v x0 g ⟨k.val+1, by omega⟩) := by
  have hF := chainF_apply C k (v x0 g ⟨k.val, by omega⟩) hL
  rw [hrec k]
  change (fun i => (∑ j : Fin s, chainF C k i j * (C.J _ (v x0 g ⟨k.val, by omega⟩)) j)
    + (C.J _ (C.h k)) i * g k) = C.J _ (C.D k (v x0 g ⟨k.val, by omega⟩) + g k • C.h k)
  rw [LinearMap.map_add, LinearMap.map_smul, ← hF]
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma chain_state {N s : ℕ} (C : CompatibleChain N s)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (v : ∀ (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)), C.E k)
    (hL : ∀ k z, C.L k (C.J k z) = z)
    (hv : ∀ x0 g, ChainStateCorrect C W v x0 g) (x0 : ℝ) (g : Fin N → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ N), stateNat N s (chainMachine C) x0 g k =
      C.J ⟨k, by omega⟩ (v x0 g ⟨k, by omega⟩) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hi : (⟨0, by omega⟩ : Fin (N+1)) = 0 := Fin.ext rfl
    rw [hi]
    simpa only [stateNat_zero] using (hv x0 g).1.symm
  | succ k ih =>
    intro hk
    have hk0 : k < N := by omega
    rw [stateNat_succ N s (chainMachine C) x0 g k hk0, ih (by omega)]
    exact chain_update C v hL x0 g (hv x0 g).2.1 ⟨k, hk0⟩

theorem chain_realizes {N s : ℕ} (C : CompatibleChain N s)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (v : ∀ (x0 : ℝ) (g : Fin N → ℝ) (k : Fin (N+1)), C.E k)
    (hL : ∀ k z, C.L k (C.J k z) = z)
    (hs : 0 < s) (hv : ∀ x0 g, ChainStateCorrect C W v x0 g) :
    Realizes N s W (chainMachine C) := by
  have hstate := chain_state C W v hL hv
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro x0 g k
    have hk : k.val ≤ N := by omega
    rw [stateFin, hstate x0 g k.val hk]
    have hread : dot ((chainMachine C).c k) (C.J ⟨k.val, by omega⟩ (v x0 g ⟨k.val, by omega⟩)) =
        C.obs ⟨k.val, by omega⟩ (C.L ⟨k.val, by omega⟩ (C.J ⟨k.val, by omega⟩ (v x0 g ⟨k.val, by omega⟩))) := by
      simpa only [chainMachine, LinearMap.coe_comp, Function.comp_apply] using
        (dot_single_linearMap ((C.obs ⟨k.val, by omega⟩).comp (C.L ⟨k.val, by omega⟩))
          (C.J ⟨k.val, by omega⟩ (v x0 g ⟨k.val, by omega⟩)))
    rw [hread, hL]
    exact (hv x0 g).2.2 ⟨k.val, by omega⟩
  · intro x0 g
    rw [stateFin, hstate x0 g N (Nat.le_refl N)]
    have hread : dot (chainMachine C).o (C.J ⟨N, by omega⟩ (v x0 g ⟨N, by omega⟩)) =
        C.obs ⟨N, by omega⟩ (C.L ⟨N, by omega⟩ (C.J ⟨N, by omega⟩ (v x0 g ⟨N, by omega⟩))) := by
      simpa only [chainMachine, LinearMap.coe_comp, Function.comp_apply] using
        (dot_single_linearMap ((C.obs ⟨N, by omega⟩).comp (C.L ⟨N, by omega⟩))
          (C.J ⟨N, by omega⟩ (v x0 g ⟨N, by omega⟩)))
    rw [hread, hL]
    exact (hv x0 g).2.2 ⟨N, by omega⟩
  · intro x0 g
    rw [stateFin, hstate x0 g 0 (Nat.zero_le N)]
    exact (hv x0 g).1

#print axioms RegisterMachine.chainF_apply
#print axioms RegisterMachine.chain_state
#print axioms RegisterMachine.chain_realizes

end
end RegisterMachine
