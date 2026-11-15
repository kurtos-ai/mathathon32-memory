module
public import Continuation.RootIsolation.CertifiedSeparation
public import Continuation.RootIsolation.SquarefreePreprocessing
@[expose] public section
open Polynomial Filter Topology RootIsolation
namespace RootIsolation.SimpleRoots

lemma sign_change_has_root (p : ℚ[X]) (a b : ℝ) (hab : a < b)
    (hsign : p.aeval a * p.aeval b < 0) :
    ∃ x ∈ Set.Ioo a b, p.aeval x = 0 := by
  have hc := (poly_aeval_continuous p).continuousOn (s := Set.Icc a b)
  have hca : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hcb : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  rcases mul_neg_iff.mp hsign with h | h
  · obtain ⟨x, hx, he⟩ := IsPreconnected.intermediate_value₂ isPreconnected_Icc
      hca hcb (continuousOn_const (c := (0:ℝ))) hc h.1.le h.2.le
    refine ⟨x, ⟨?_, ?_⟩, he.symm⟩
    · exact lt_of_le_of_ne hx.1 (by intro e; subst x; linarith)
    · exact lt_of_le_of_ne hx.2 (by intro e; subst x; linarith)
  · obtain ⟨x, hx, he⟩ := IsPreconnected.intermediate_value₂ isPreconnected_Icc
      hca hcb hc (continuousOn_const (c := (0:ℝ))) h.1.le h.2.le
    refine ⟨x, ⟨?_, ?_⟩, he⟩
    · exact lt_of_le_of_ne hx.1 (by intro e; subst x; linarith)
    · exact lt_of_le_of_ne hx.2 (by intro e; subst x; linarith)

theorem filteredIntervals_unique_root (p : ℚ[X]) (B eps delta : ℚ)
    (hdelta : 0 < delta) (hsmall : delta < eps)
    (hsep : ∀ x y:ℝ, p.aeval x = 0 → p.aeval y = 0 → x ≠ y → (eps:ℝ) ≤ |x-y|)
    (I : IsoInterval) (hI : I ∈ filteredIntervals p B delta) :
    ∃! x : ℝ, x ∈ I.toSet ∧ p.aeval x = 0 := by
  rcases List.mem_append.mp hI with hp | hi
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq0 := (pointRoots_mem_iff p B delta q).mp hq
    refine ⟨(q:ℝ), ⟨by simp [IsoInterval.toSet], ?_⟩, ?_⟩
    · rw [aeval_coe_eq_coe_eval, hq0.2]; simp
    · intro y hy
      exact Set.mem_singleton_iff.mp hy.1
  · obtain ⟨⟨a,b⟩, hab, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hcell, hsign⟩ := (signChangingIntervals_mem_iff p B delta a b).mp hab
    have hlen := partition_interval_length' B delta a b hcell
    have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast (show a < b by linarith)
    have hsign' : p.aeval (a:ℝ) * p.aeval (b:ℝ) < 0 := by
      rw [aeval_coe_eq_coe_eval, aeval_coe_eq_coe_eval]
      exact_mod_cast hsign
    obtain ⟨x, hx, hx0⟩ := sign_change_has_root p a b hab' hsign'
    refine ⟨x, ⟨hx,hx0⟩, ?_⟩
    intro y hy
    by_contra hne
    have h := hsep x y hx0 hy.2 (Ne.symm hne)
    have hy' : (a:ℝ) < y ∧ y < (b:ℝ) := hy.1
    have hd : |x-y| < (delta:ℝ) := by
      have hlen' : (b:ℝ) = (a:ℝ) + (delta:ℝ) := by exact_mod_cast hlen
      apply abs_lt.mpr
      constructor <;> linarith [hx.1,hx.2,hy'.1,hy'.2]
    have hs : (delta:ℝ) < (eps:ℝ) := by exact_mod_cast hsmall
    linarith

noncomputable def isolateWithCertificate (p : ℚ[X]) (B eps : ℚ) : List IsoInterval :=
  filteredIntervals (SquarefreePreprocessing.squarefreePart p) B (eps/2)

theorem isolateWithCertificate_correct (p : ℚ[X]) (hp : p ≠ 0)
    (B eps : ℚ) (hB : 0 < B) (heps : 0 < eps)
    (hBspec : ∀ x:ℝ, p.aeval x = 0 → ‖x‖ ≤ (B:ℝ))
    (hsep : ∀ x y:ℝ, p.aeval x = 0 → p.aeval y = 0 → x ≠ y → (eps:ℝ) ≤ |x-y|) :
    (∀ I ∈ isolateWithCertificate p B eps,
      ∃! x : ℝ, x ∈ I.toSet ∧ p.aeval x = 0) ∧
    (∀ x : ℝ, p.aeval x = 0 → ∃ I ∈ isolateWithCertificate p B eps, x ∈ I.toSet) := by
  let q := SquarefreePreprocessing.squarefreePart p
  have hroot (x:ℝ) : p.aeval x = 0 ↔ q.aeval x = 0 :=
    SquarefreePreprocessing.squarefree_aeval_root_iff p hp x
  have hqsep : ∀ x y:ℝ, q.aeval x = 0 → q.aeval y = 0 → x ≠ y → (eps:ℝ) ≤ |x-y| := by
    intro x y hx hy hne
    exact hsep x y ((hroot x).mpr hx) ((hroot y).mpr hy) hne
  constructor
  · intro I hI
    obtain ⟨x, hx, huniq⟩ := filteredIntervals_unique_root q B eps (eps/2)
      (by linarith) (by linarith) hqsep I hI
    refine ⟨x, ⟨hx.1,(hroot x).mpr hx.2⟩, ?_⟩
    intro y hy
    exact huniq y ⟨hy.1,(hroot y).mp hy.2⟩
  · intro x hx
    exact simple_root_mem_half_separation q eps heps hqsep B hB
      (fun y hy => hBspec y ((hroot y).mpr hy))
      (fun y hy => SquarefreePreprocessing.squarefree_deriv_ne_zero p hp y hy)
      x ((hroot x).mp hx)

end RootIsolation.SimpleRoots
