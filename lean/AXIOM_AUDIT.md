# Axiom audit

Run `lake env lean lean/CheckAxioms.lean` after `lake build`.
The recorded output is in `verification/axioms-lake.log`.
Every audited declaration must use only `propext`, `Classical.choice`, and
`Quot.sound`. Source scanning is an additional check, not a replacement for
checking dependencies or whether a theorem's type matches the report.

The exact scope and unformalized claims are listed in `DECLARATION_MAP.md`.
