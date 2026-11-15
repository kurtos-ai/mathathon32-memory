# Axiom audit

Run `lake env lean lean/CheckAxioms.lean` after `lake build`.
Historical and current run logs are preserved outside this Lean-only repository
in the submission archive/checks directory.
Every audited declaration must use only `propext`, `Classical.choice`, and
`Quot.sound`. Source scanning is an additional check, not a replacement for
checking dependencies or whether a theorem's type matches the report.

Principal declarations are listed in `DECLARATION_MAP.md`; remaining mathematical
claims are listed in `CURRENT_PAPER_COVERAGE.md`.
