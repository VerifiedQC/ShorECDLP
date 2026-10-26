# Explicit axiom disclosures

Each `.txt` file lists declarations from the Lean module named by the filename.
The initial split uses Lean's environment module ownership, not namespace guesses.
Add a declaration to its defining module's file. Do not edit a global count.

`axiom-manifests.py commands` validates the files and emits the explicit commands.
`check-output` derives the total from the same files and requires every expected
declaration exactly once in Lean's output. Missing, duplicate, or substituted
outputs fail even when the total count happens to match. Blank lines and comments
are allowed. Empty files, duplicate names, and nonexistent source modules fail.

`verify.sh` still checks the printed axiom allowlist and then exhaustively audits
all project declarations with the pinned axiom-audit tool. These manifests do not
replace or narrow that exhaustive audit.
