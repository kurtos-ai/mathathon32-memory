# Lean formalization

This library is partial; see `DECLARATION_MAP.md` and `STATUS.md`.

From the repository root, with elan installed:

```sh
lake exe cache get
lake build
lake env lean lean/CheckAxioms.lean
```

`lean-toolchain` pins Lean 4.35.0. `lakefile.lean` pins Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679`; `lake-manifest.json` pins its dependencies.
The local build and axiom audit are recorded under `verification/`.

The default library imports the actual register-machine construction and lower
bound, their dimension-independent vector extension, the increment-rank
characterization, the exact extended-risk decision theorem, and benchmark
algebraic helpers. No unfinished proof file
is included in the library. The report remains the authoritative mathematical
submission, with written proofs and explicit literature citations.
