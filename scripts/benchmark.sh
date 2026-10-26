#!/usr/bin/env bash
# PROTECTED challenge benchmark (Eigen-style). Run from the evaluator's TRUSTED copy,
# inside an isolated worker with no credentials. The runner supplies:
#   CANDIDATE      absolute path of the frozen candidate source snapshot
#   TRUSTED_REPO   evaluator-owned checkout (outside CANDIDATE)
#   TRUSTED_TREE   full Git tree hash of the protected tree
# Only ShorECDLP/Submission/Entrant/ may differ from TRUSTED_TREE.
set -euo pipefail
: "${CANDIDATE:?runner must set CANDIDATE}"
: "${TRUSTED_REPO:?runner must set TRUSTED_REPO}"
: "${TRUSTED_TREE:?runner must set TRUSTED_TREE}"
trusted_scripts="$(cd "$(dirname "$0")" && pwd)"

# 1. Editable boundary, BEFORE any build cache is restored.
python3 "$trusted_scripts/challenge/check-editable.py" --repo "$CANDIDATE" \
  --trusted-repo "$TRUSTED_REPO" --trusted-tree "$TRUSTED_TREE" \
  --allow ShorECDLP/Submission/Entrant

cd "$CANDIDATE"
# 2. Full protected verification: source policy, layering, warning-fatal build,
#    kernel replay, cheat regressions, explicit + exhaustive axiom audits.
"$trusted_scripts/verify.sh"
python3 "$trusted_scripts/challenge/gate.py" --replay ShorECDLP.Submission.Entrant
python3 "$trusted_scripts/challenge/gate.py" --replay ShorECDLP.Judge

# 3. Report. The acceptance theorem is ShorECDLP.Judge.check_certificate.
report="$(lake env lean --stdin <<'LEAN' 2>&1
import ShorECDLP.Judge.Main
#print axioms ShorECDLP.Judge.check_certificate
#eval ShorECDLP.Judge.score
#eval ShorECDLP.Judge.qubits
#eval ShorECDLP.Judge.measurements
LEAN
)"
printf '%s\n' "$report"
python3 - "$report" <<'PY'
import json, re, sys
report = sys.argv[1]
allowed = {"propext", "Classical.choice", "Quot.sound"}
m = re.search(r"^'ShorECDLP\.Judge\.check_certificate' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)$", report, re.M)
if not m:
    sys.exit("REJECT: no axiom report for the acceptance theorem")
used = {a.strip() for a in (m.group(1) or "").split(",") if a.strip()}
if not used <= allowed:
    sys.exit(f"REJECT: acceptance theorem uses {sorted(used - allowed)}")
values = [int(v) for v in re.findall(r"^([0-9]+)$", report, re.M)]
if len(values) != 3:
    sys.exit("REJECT: could not read metrics")
print(json.dumps({"accepted": True, "score_tModel": values[0], "qubits": values[1], "measurements": values[2]}))
PY
