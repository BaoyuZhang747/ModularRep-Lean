# Package changes

## r34 — checked companion release

The release scope is stated consistently in the README, SCOPE.md, status records
and export manifest: a checked Lean companion under its stated external
assumptions. Release checks enforce this scope and retain the source, document,
dependency and computation identity checks. Internal preparation records are
kept separately from the source distribution.

All 2,003 Lean source and audit files, the nine Lake/toolchain files, the three
PDFs and the historical verification records are unchanged from r33. The
mathematical assumptions and the scope of the recorded checks are unchanged.

## r33 — documentation and checking corrections

Report Appendix C describes auxiliary constructions without claiming that three
unused Type B modules implement the manuscript arguments. The index-two
extension paragraph states its finite-group and finite-dimensional hypotheses.
The unsupported statement connecting the final primitive-block equality to the
selected Jordan construction was removed. The introduction lists Appendix C.
The report was rebuilt and all 63 pages visually reviewed; the library manual
and reference manuscript were unchanged.

Mocked launcher tests no longer print a message suggesting that Lean ran.
Documented test commands suppress Python bytecode caches. Build instructions
state the audit flags and distinguish them from the historical compilation
options. File checks are described as consistency checks against recorded
identities. Lean sources and Lake configuration were unchanged.

## r32 — audit launcher and build instructions

The configured audit launcher builds each audit's imports before elaborating the
audit, including dependencies outside the default application import closure.
Instructions distinguish the application build, the five configured audits and
the historical all-module compilation. The self-hosted workflow is restricted to
a private repository and documents runner isolation. The original Apache
licence remains in `packages/ModularRep`; the accidental root-level copy was
removed. Lean sources, Lake configuration and PDFs were unchanged.

## r31 — documentation and repository organisation

The maintained documents are the 63-page formalisation report and 68-page
library manual, with one shared bibliography. The report includes Appendix C on
auxiliary source constructions. The earlier supporting exposition is preserved
in historical source archives. The source ZIP has one enclosing `ModularRep`
directory and a deterministic export from a recorded Git commit. All 2,003 Lean
source and audit files and the nine Lake/toolchain files were unchanged from r30.
