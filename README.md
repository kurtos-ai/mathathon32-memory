# Lean formalization of memory-constrained first-order methods

This repository contains Lean source, pinned build dependencies, third-party
license/provenance information, and documentation of the formalization.

The checked library includes exact register realizations and memory-rank criteria,
a complete executable real-algebraic decision procedure, concrete quadratic and
smooth-convex loss compilers, the classical objective-error benchmarks, and projected
subgradient models. These results concern predetermined scalar-coefficient methods.

**The revised 69-page paper is not yet fully formalized.** Its new weak-convexity,
second-auxiliary-register separation, and some method-replacement results require
further proofs. Both quadratic-replacement assertions are now checked: an actual
two-register machine reproduces every terminal point, and a one-register machine
pointwise dominates objective error on every convex quadratic instance. See `lean/CURRENT_PAPER_COVERAGE.md` for the current claim-by-claim audit.
`lean/DECLARATION_MAP.md` gives principal checked declarations and explicitly retains
finite loss-model hypotheses where applicable. A conditional theorem is not treated
as a proof of its unproved premises.

## Build and audit

The pinned `lean-toolchain` selects Lean 4.35.0. With elan installed:

```sh
lake exe cache get
lake build
lake env lean lean/CheckAxioms.lean
```

Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Retained declarations must have no `sorry`, `admit`, custom axioms, or `native_decide`.
The public axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

The 39 attributed TauCeti source files are pinned at
`1c497c347f615b3087cb605f8cf743e591376105`; see `third_party/TauCeti/` for
Apache-2.0 licensing and file hashes. Their pre-existing contribution is distinguished
from the project-specific symbolic elimination and optimization formalization.

Paper sources, slides, Python experiments, and historical verification logs are
outside this Lean-only repository. They were preserved during submission preparation,
not used as Lean axioms or substituted for kernel-checked proofs. Large QE benchmark
runs are not claimed practical; the program's correctness is proved symbolically.
