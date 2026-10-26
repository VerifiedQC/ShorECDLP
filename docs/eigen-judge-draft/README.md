# Eigen-style judge shell (draft, Dirac, 2026-10-26)

Files (to land in the repo once the format is confirmed with Eigen):
- `Official.lean` → `ShorECDLP/Challenge/Official.lean` (PROTECTED): organizer `officialLimits`, imported by judge and entrants. Values TBD (candidate budget 48 vs 55; gate slots must cover Naive's 4e15 bound; measurements must cover Naive 5,385,536 and the 2607 total).
- `Judge.lean` → `scripts/Judge.lean` (PROTECTED): binds `ShorECDLP.Entrant.{entry,layout,bounds,certificate}` to fully `_root_`-qualified protected types; one acceptance theorem `check_certificate`; prints axioms, score (= declared whole-program tModel) and qubits.
- `benchmark.sh` → `scripts/benchmark.sh` (PROTECTED): editable-path check, source policy, warning-fatal build, kernel replay of Challenge + Entrant, judge, axiom allowlist, sorry rejection. (`check-editable.py` still to write.)
- `Entrant-Naive-example.lean` → `ShorECDLP/Submission/Entrant/Main.lean` (EDITABLE): the Naive baseline wrapped as an entrant; its certificate is the Naive numeric certificate lifted to `officialLimits`.

Smoke test (bd5c438 + these files, local): judge elaborates; `check_certificate` depends only on [propext, Classical.choice, Quot.sound]; score 8918039383771648; qubits 206624. Judge run 4 s.
