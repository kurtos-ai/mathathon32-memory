# Verification records

Verified locally on macOS arm64 with Lean 4.35.0, Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and Python 3.12.8.

- `lake-build.log`: successful build of every default library target.
- `axioms-lake.log`: `lake env lean lean/CheckAxioms.lean` output.
- `source-scan.txt`: absence of proof holes, custom axioms and native_decide in
  retained Lean sources. This supplements the dependency audit.

The mathematical scope is in `lean/DECLARATION_MAP.md`. Linter warnings in the
build output do not indicate proof holes; proof types and axiom dependencies
were checked separately. Computation logs are in `computations/logs/`.
