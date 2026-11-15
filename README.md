# Memory-constrained minimax first-order optimization

Submission materials for Mathathon problem 32, by Francisco Hernández Iglesias
and Jack Mayo (kurtos.ai).

- `paper/report.tex` and `paper/report.pdf`: the self-contained research report.
- `slides/memory-slides.pdf`: 16 main slides and one OGM appendix for a 20-minute talk.
- `lean/`: the Lean formalization of the report’s stated results, with a precise declaration map.
- `computations/`: exact and numerical checks, with fixed ranges and logs.
- `verification/`: build and axiom-audit records.
- `inputs/`: the preserved starting paper and supplied exact-arithmetic script.

The Lean library verifies actual register realizations, normalized coordinates,
rank/minor memory constraints, exact threshold and gain criteria, both benchmark
minimax calculations, smooth coefficient uniqueness, and a complete executable
real-algebraic decision procedure. The algorithms take finite loss formulas and
specified algebraic coefficients; they do not take unknown minimax values or
assumed elimination oracles. General nonlinear QE is proved but has no claimed
practical complexity bound. Concrete rational/algebraic benchmark inputs and projected-domain inputs are
compiled and proved exact. `lean/STATUS.md` records the completed programme;
`lean/DECLARATION_MAP.md` gives exact theorem scope and retained input assumptions.

## Reproduce

With elan installed, the pinned `lean-toolchain` selects Lean 4.35.0:

```sh
lake exe cache get
lake build
lake env lean lean/CheckAxioms.lean
python3 computations/rerun_quadratic_certificates.py
python3 computations/rank_checks.py
python3 computations/ogm_checks.py
python3 computations/projected_recurrence_checks.py
```

The Python checks use the standard library. Build the report with
`tectonic paper/report.tex`. Build slides from their directory with
`tectonic memory-slides.tex`; keep `assets/` beside the source. The supplied
SVG is the original Mathathon logo, and its PDF is a vector conversion.

All current paper development occurred during the event, as confirmed by the
authors. AI assistance and the distinction between written proof, literature,
computation, and Lean coverage are disclosed in the report. Final human author
review is not asserted by these files.

The repository remains private at the authors' request. No competition
submission has been made. Organizer access must be arranged before a submission
that relies on this private repository.
