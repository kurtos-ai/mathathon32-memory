module
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Tactic
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open Set
namespace ConicDuality
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def imageCone (K : ProperCone ℝ E) (A : Y →L[ℝ] E) (cost : Y →L[ℝ] ℝ) :
    Set (E × ℝ) := {p | ∃ y k, k ∈ K ∧ p.1 = A y-k ∧ cost y ≤ p.2}

theorem imageCone_zero (K : ProperCone ℝ E) (A : Y →L[ℝ] E) (cost : Y →L[ℝ] ℝ) :
    (0 : E × ℝ) ∈ imageCone K A cost := by
  refine ⟨0,0,K.zero_mem,?_,?_⟩ <;> simp

theorem imageCone_smul (K : ProperCone ℝ E) (A : Y →L[ℝ] E) (cost : Y →L[ℝ] ℝ)
    {p : E × ℝ} (hp : p ∈ imageCone K A cost) (a : ℝ) (ha : 0 ≤ a) :
    a • p ∈ imageCone K A cost := by
  rcases hp with ⟨y,k,hk,hp,hc⟩
  refine ⟨a • y,a • k,K.smul_mem hk ha,?_,?_⟩
  · simpa [map_smul,smul_sub] using congrArg (a • ·) hp
  · simpa [map_smul,smul_eq_mul] using mul_le_mul_of_nonneg_left hc ha

theorem imageCone_convex (K : ProperCone ℝ E) (A : Y →L[ℝ] E) (cost : Y →L[ℝ] ℝ) :
    Convex ℝ (imageCone K A cost) := by
  rintro p ⟨y,k,hk,hp,hcy⟩ q ⟨z,l,hl,hq,hcz⟩ a b ha hb hab
  refine ⟨a • y+b • z,a • k+b • l,K.convex hk hl ha hb hab,?_,?_⟩
  · change a • p.1+b • q.1 = _
    rw [hp,hq,map_add,map_smul,map_smul]
    module
  · change cost (a • y+b • z) ≤ a*p.2+b*q.2
    simp only [map_add,map_smul,smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hcy ha) (mul_le_mul_of_nonneg_left hcz hb)

theorem imageCone_interior_of_positive_annihilator [FiniteDimensional ℝ E]
    (K : ProperCone ℝ E) (A : Y →L[ℝ] E) (cost : Y →L[ℝ] ℝ)
    (hkernel : ∀ F : E →L[ℝ] ℝ, (∀ k ∈ K, 0 ≤ F k) → F.comp A = 0 → F = 0) :
    (interior (imageCone K A cost)).Nonempty := by
  have hspan : Submodule.span ℝ (imageCone K A cost) = ⊤ := by
    by_contra hn
    obtain ⟨f,hf,hm⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr hn) inferInstance
    have hvan (p : E × ℝ) (hp : p ∈ imageCone K A cost) : f p = 0 := by
      have hmem := Submodule.mem_map_of_mem (f := f) (Submodule.subset_span hp)
      rw [hm] at hmem
      exact hmem
    have hv : f (0,(1:ℝ)) = 0 := hvan _ ⟨0,0,K.zero_mem,by simp,by simp⟩
    let F : E →L[ℝ] ℝ := (f.comp (LinearMap.inl ℝ E ℝ)).toContinuousLinearMap
    have hsplit (x : E) (s : ℝ) : f (x,s) = F x := by
      have he : (x,s) = (x,0)+s • (0,(1:ℝ)) := by ext <;> simp
      rw [he,map_add,map_smul,hv]
      simp [F]
    have hF : ∀ k ∈ K, 0 ≤ F k := by
      intro k hk
      have hz := hvan (-k,0) ⟨0,k,hk,by simp,by simp⟩
      rw [hsplit,map_neg] at hz
      linarith
    have hFA : F.comp A = 0 := by
      ext y
      have hz := hvan (A y,cost y) ⟨y,0,K.zero_mem,by simp,le_rfl⟩
      simpa [hsplit] using hz
    have hF0 := hkernel F hF hFA
    apply hf
    apply LinearMap.ext
    rintro ⟨x,s⟩
    change f (x,s) = 0
    rw [hsplit,hF0]
    rfl
  apply (imageCone_convex K A cost).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ (imageCone_zero K A cost)),hspan]
  rfl

theorem approximate_dual [FiniteDimensional ℝ E] (K : ProperCone ℝ E)
    (A : Y →L[ℝ] E) (cost : Y →L[ℝ] ℝ) (c : E)
    (hkernel : ∀ F : E →L[ℝ] ℝ, (∀ k ∈ K, 0 ≤ F k) → F.comp A = 0 → F = 0)
    (v γ : ℝ) (hγ : v < γ)
    (hbound : ∀ F : E →L[ℝ] ℝ, (∀ k ∈ K, 0 ≤ F k) →
      F.comp A = cost → F c ≤ v) :
    ∃ y : Y, A y-c ∈ K ∧ cost y ≤ γ := by
  classical
  by_contra hn
  have hp : (c,γ) ∉ imageCone K A cost := by
    rintro ⟨y,k,hk,hc,hcost⟩
    apply hn
    refine ⟨y,?_,hcost⟩
    have he : A y-c = k := by
      change c = A y-k at hc
      rw [hc]; abel
    simpa only [he] using hk
  obtain ⟨f,hfne,hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (imageCone_convex K A cost) (fun h => hp (interior_subset h))
    (imageCone_interior_of_positive_annihilator K A cost hkernel)
  have hp0 : 0 ≤ f (c,γ) := by
    simpa using hsep 0 (imageCone_zero K A cost)
  have hcone : ∀ p ∈ imageCone K A cost, f p ≤ 0 := by
    intro p hp
    by_contra! hpos
    let a := (f (c,γ)+1)/f p
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have h := hsep (a • p) (imageCone_smul K A cost hp a ha)
    rw [map_smul] at h
    have he : a*f p = f (c,γ)+1 := div_mul_cancel₀ _ (ne_of_gt hpos)
    change a*f p ≤ f (c,γ) at h
    linarith
  let F : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let τ : ℝ := -f (0,1)
  have hsplit (x : E) (s : ℝ) : f (x,s) = F x-τ*s := by
    have he : (x,s) = (x,0)+s • (0,(1:ℝ)) := by ext <;> simp
    rw [he,map_add,map_smul]
    change f (x,0)+s*f (0,1) = f (x,0)-(-f (0,1))*s
    ring
  have hF : ∀ k ∈ K, 0 ≤ F k := by
    intro k hk
    have h := hcone (-k,0) ⟨0,k,hk,by simp,by simp⟩
    rw [hsplit,map_neg] at h
    linarith
  have hτ : 0 ≤ τ := by
    have h := hcone (0,1) ⟨0,0,K.zero_mem,by simp,by simp⟩
    dsimp [τ]
    linarith
  have hA (y : Y) : F (A y) = τ*cost y := by
    have h₁ := hcone (A y,cost y) ⟨y,0,K.zero_mem,by simp,le_rfl⟩
    have h₂ := hcone (A (-y),cost (-y)) ⟨-y,0,K.zero_mem,by simp,le_rfl⟩
    rw [hsplit] at h₁ h₂
    simp only [map_neg] at h₂
    linarith
  have hτpos : 0 < τ := by
    by_contra! hle
    have hτ0 : τ = 0 := le_antisymm hle hτ
    have hFA : F.comp A = 0 := by
      ext y
      change F (A y) = 0
      simp [hA,hτ0]
    have hF0 := hkernel F hF hFA
    apply hfne
    apply ContinuousLinearMap.ext
    rintro ⟨x,s⟩
    change f (x,s) = 0
    rw [hsplit]
    simp [hF0,hτ0]
  let G : E →L[ℝ] ℝ := τ⁻¹ • F
  have hG : ∀ k ∈ K, 0 ≤ G k := by
    intro k hk
    exact mul_nonneg (inv_nonneg.mpr hτ) (hF k hk)
  have hGA : G.comp A = cost := by
    ext y
    change τ⁻¹*F (A y) = cost y
    rw [hA,←mul_assoc,inv_mul_cancel₀ (ne_of_gt hτpos),one_mul]
  have hb := hbound G hG hGA
  have hGc : γ ≤ G c := by
    have hc : τ*γ ≤ F c := by rw [hsplit] at hp0; linarith
    change γ ≤ τ⁻¹*F c
    rw [←div_eq_inv_mul]
    exact (le_div_iff₀ hτpos).mpr (by simpa [mul_comm] using hc)
  linarith

end ConicDuality
