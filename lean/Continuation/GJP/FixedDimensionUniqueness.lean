module
public import Continuation.GJP.ActualUniqueness
public import Continuation.Smooth.FixedDimension
@[expose] public section
noncomputable section
namespace GJP

/-- The fixed-dimension version of GJP Theorem 1.1, for every n≥N+2. -/
theorem actual_method_unique_fixed_dimension {N n : ℕ} (hn : N+2 ≤ n)
    (W : RealizationCore.StrictHistory N) (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hW : ∀ I : SmoothAttain.Instance n L R,
      SmoothGramModel.terminalLoss I W.val ≤ L*R^2/(2*SmoothBenchmark.theta N N^2)) :
    W.val = SmoothOGM.ogmW N L := by
  apply actual_method_unique W L R hL hR
  exact (SmoothGramModel.uniform_bound_iff_fixed_dimension hn W.val L R _ hL hR.le).mpr hW

/-- Fixed- and all-dimensional uniform bounds have the same unique optimal coefficients. -/
theorem sharp_methods_equal_fixed_dimension {N n : ℕ} (hn : N+2 ≤ n)
    (W V : RealizationCore.StrictHistory N) (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hW : ∀ I : SmoothAttain.Instance n L R,
      SmoothGramModel.terminalLoss I W.val ≤ L*R^2/(2*SmoothBenchmark.theta N N^2))
    (hV : ∀ I : SmoothAttain.Instance n L R,
      SmoothGramModel.terminalLoss I V.val ≤ L*R^2/(2*SmoothBenchmark.theta N N^2)) :
    W.val = V.val := by
  rw [actual_method_unique_fixed_dimension hn W L R hL hR hW,
    actual_method_unique_fixed_dimension hn V L R hL hR hV]

end GJP
