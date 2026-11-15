import Lake
open Lake DSL

package Mathathon32Memory where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib Mathathon32Memory where
  srcDir := "lean"
  roots := #[`MemoryRank, `Decision, `Benchmarks, `RealizationCore, `Continuation, `Submission2026]

lean_lib TauCeti where
  srcDir := "lean"
  roots := #[`TauCeti]
