module
public import Continuation.Smooth.OGMUpperBound
public import Continuation.Smooth.Operational
public import Continuation.Smooth.OGMInstalledMemory

@[expose] public section
noncomputable section
namespace OGMVerified
open SmoothOGM

def coordinates (N:ℕ) (L:ℝ) := RealizationCore.coordinateEquiv N
  (⟨ogmW N L,ogmW_strict N L⟩ : RealizationCore.StrictHistory N)

lemma coordinates_recover (N:ℕ) (L:ℝ) :
    RealizationCore.W_of N (coordinates N L).1 (coordinates N L).2.val = ogmW N L :=
  RealizationCore.W_of_dT_of N ⟨ogmW N L,ogmW_strict N L⟩

lemma lossSet_upper (N:ℕ) (L R:ℝ) (hL:0<L) :
    ∀ z ∈ SmoothGramModel.actualLossSet N (ogmW N L) L R,
      z ≤ L*R^2/(2*SmoothBenchmark.theta N N^2) := by
  rintro z ⟨n,I,rfl⟩
  exact actual_upper_bound I hL

lemma risk_upper (N:ℕ) (L R:ℝ) (hL:0<L) :
    MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (coordinates N L).1 (coordinates N L).2 ≤
      ((L*R^2/(2*SmoothBenchmark.theta N N^2):ℝ):EReal) := by
  apply (MemoryDecision.risk_le_iff _ _ _ _ _).mpr
  intro z hz
  change z ∈ SmoothGramModel.actualLossSet N
    (RealizationCore.W_of N (coordinates N L).1 (coordinates N L).2.val) L R at hz
  rw [coordinates_recover] at hz
  exact lossSet_upper N L R hL z hz

lemma coordinates_mem_memory (N m:ℕ) (L:ℝ) (hm : 1 ≤ m) :
    (coordinates N L).2 ∈ SmoothOperational.memory N m := by
  apply (SmoothOperational.mem_memory_iff_realization N m _ (coordinates N L).1).mpr
  rw [coordinates_recover]
  apply (RegisterMachine.realization_iff_maxCutRank N _ (m+1)).mpr
  have h := (RegisterMachine.realization_iff_maxCutRank N _ 2).mp (ogmHasRealization N L)
  exact le_trans h (by omega)

lemma value_upper (N m:ℕ) (L R:ℝ) (hL:0<L) (hm : 1 ≤ m) :
    MemoryDecision.value (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
      (SmoothOperational.memory N) m ≤ ((L*R^2/(2*SmoothBenchmark.theta N N^2):ℝ):EReal) := by
  let T : SmoothOperational.memory N m := ⟨(coordinates N L).2,coordinates_mem_memory N m L hm⟩
  calc _ ≤ MemoryDecision.risk (SmoothOperational.feasible N L R) (SmoothOperational.loss N)
        (coordinates N L).1 T.val := iInf_le_of_le T (iInf_le _ _)
    _ ≤ _ := risk_upper N L R hL

lemma coordinates_mem_memory_one_query (L:ℝ) (hL:0<L) :
    (coordinates 1 L).2 ∈ SmoothOperational.memory 1 0 := by
  apply (SmoothOperational.mem_memory_iff_realization 1 0 _ (coordinates 1 L).1).mpr
  rw [coordinates_recover]
  exact (InstalledOGM.memory_conclusion_N1_unconditional L (ne_of_gt hL)).1

lemma value_upper_one_query (L R:ℝ) (hL:0<L) :
    MemoryDecision.value (SmoothOperational.feasible 1 L R) (SmoothOperational.loss 1)
      (SmoothOperational.memory 1) 0 ≤ ((L*R^2/8:ℝ):EReal) := by
  let T : SmoothOperational.memory 1 0 := ⟨(coordinates 1 L).2,coordinates_mem_memory_one_query L hL⟩
  have hv : MemoryDecision.value (SmoothOperational.feasible 1 L R) (SmoothOperational.loss 1)
      (SmoothOperational.memory 1) 0 ≤
      ((L*R^2/(2*SmoothBenchmark.theta 1 1^2):ℝ):EReal) :=
    le_trans (iInf_le_of_le T (iInf_le _ (coordinates 1 L).1)) (risk_upper 1 L R hL)
  norm_num [InstalledOGM.theta_one_one] at hv ⊢
  exact hv

end OGMVerified
