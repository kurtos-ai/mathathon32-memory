module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic
@[expose] public section

namespace RootIsolation

def numSteps (B delta : ℚ) : ℕ :=
  if delta ≤ 0 then 0 else ⌈2 * B / delta⌉₊

def partitionPoints (B delta : ℚ) : List ℚ :=
  (List.range (numSteps B delta + 1)).map (fun j : ℕ => -B + (j : ℚ) * delta)

lemma partitionPoints_length (B delta : ℚ) :
    (partitionPoints B delta).length = numSteps B delta + 1 := by
  simp [partitionPoints]

def consecutivePairs (l : List ℚ) : List (ℚ × ℚ) := l.zip l.tail

end RootIsolation
