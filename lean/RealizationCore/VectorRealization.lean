module
public import RealizationCore.MemoryCharacterization
@[expose] public section
noncomputable section

namespace RegisterMachine

/-- Actual vector-register recursion. The scalar coefficient machine is fixed
independently of the ambient dimension `d`. -/
def vectorStateNat {N s d : ℕ} (M : Machine N s)
    (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ) : ℕ → (Fin s → Fin d → ℝ)
  | 0 => fun r a => e1 s r * x0 a
  | k+1 => if h : k < N then
      fun r a => (∑ j : Fin s, M.F ⟨k,h⟩ r j * vectorStateNat M x0 g k j a)
        + M.b ⟨k,h⟩ r * g ⟨k,h⟩ a
    else vectorStateNat M x0 g k

def vectorReadout {s d : ℕ} (c : Fin s → ℝ) (z : Fin s → Fin d → ℝ) : Fin d → ℝ :=
  fun a => ∑ r : Fin s, c r * z r a

def vectorTarget {N d : ℕ} (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ) (k : Fin (N+1)) : Fin d → ℝ :=
  fun a => x0 a + ∑ j : Fin k.val, W k ⟨j.val, by omega⟩ * g ⟨j.val, by omega⟩ a

theorem vectorState_coordinate {N s d : ℕ} (M : Machine N s)
    (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ) (a : Fin d) (k : ℕ) :
    (fun r => vectorStateNat M x0 g k r a) =
      stateNat N s M (x0 a) (fun j => g j a) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext r
    by_cases h : k < N
    · simp only [vectorStateNat, stateNat, h, dite_true]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [congrFun ih j]
    · simp only [vectorStateNat, stateNat, h, dite_false]
      exact congrFun ih r

theorem vectorReadout_coordinate {N s d : ℕ} (M : Machine N s)
    (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ)
    (c : Fin s → ℝ) (a : Fin d) (k : ℕ) :
    vectorReadout c (vectorStateNat M x0 g k) a =
      dot c (stateNat N s M (x0 a) (fun j => g j a) k) := by
  unfold vectorReadout dot
  apply Finset.sum_congr rfl
  intro r _
  rw [congrFun (vectorState_coordinate M x0 g a k) r]

/-- A single predetermined coefficient machine must reproduce all queries and
the terminal output in every finite dimension and for all formal vector inputs. -/
def VectorRealizes (N s : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (M : Machine N s) : Prop :=
  0 < s ∧ ∀ (d : ℕ) (x0 : Fin d → ℝ) (g : Fin N → Fin d → ℝ),
    (∀ k : Fin N, vectorReadout (M.c k) (vectorStateNat M x0 g k.val) =
      vectorTarget W x0 g ⟨k.val, by omega⟩) ∧
    vectorReadout M.o (vectorStateNat M x0 g N) =
      vectorTarget W x0 g ⟨N, by omega⟩

theorem vectorRealizes_iff_scalar (N s : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (M : Machine N s) :
    VectorRealizes N s W M ↔ Realizes N s W M := by
  constructor
  · intro h
    refine ⟨h.1, ?_, ?_, ?_⟩
    · intro x0 g k
      have hv := congrFun ((h.2 1 (fun _ => x0) (fun j _ => g j)).1 k) (0 : Fin 1)
      simpa only [vectorReadout_coordinate, vectorTarget, target, stateFin] using hv
    · intro x0 g
      have hv := congrFun (h.2 1 (fun _ => x0) (fun j _ => g j)).2 (0 : Fin 1)
      simpa only [vectorReadout_coordinate, vectorTarget, target, stateFin] using hv
    · intro x0 g
      rfl
  · intro h
    refine ⟨h.1, ?_⟩
    intro d x0 g
    constructor
    · intro k
      funext a
      rw [vectorReadout_coordinate]
      exact h.2.1 (x0 a) (fun j => g j a) k
    · funext a
      rw [vectorReadout_coordinate]
      exact h.2.2.1 (x0 a) (fun j => g j a)

def HasVectorRealization (N : ℕ) (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (s : ℕ) : Prop := ∃ M : Machine N s, VectorRealizes N s W M

theorem hasVectorRealization_iff_scalar (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) :
    HasVectorRealization N W s ↔ HasRealization N W s := by
  exact exists_congr (fun M => vectorRealizes_iff_scalar N s W M)

/-- Dimension-independent register realization is equivalent to the cut-rank
condition, with the same coefficient machine for all dimensions. -/
theorem vectorRealization_iff_maxCutRank (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (s : ℕ) :
    HasVectorRealization N W s ↔ MemoryRank.CutRank.memRank N W ≤ s :=
  (hasVectorRealization_iff_scalar N W s).trans (realization_iff_maxCutRank N W s)

theorem isLeast_vectorRegisterCount (N : ℕ)
    (W : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    IsLeast {s : ℕ | HasVectorRealization N W s} (MemoryRank.CutRank.memRank N W) := by
  constructor
  · exact (vectorRealization_iff_maxCutRank N W _).mpr le_rfl
  · intro s hs
    exact (vectorRealization_iff_maxCutRank N W s).mp hs

end RegisterMachine
