#!/usr/bin/env bash
# PROTECTED. Run inside an isolated worker with no credentials and a read-only trusted checkout.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
# 1. Only the editable path may differ from the pinned trusted tree (checker runs from the TRUSTED copy, before any cache restore).
: "${TRUSTED_REPO:?runner must set TRUSTED_REPO (evaluator-owned checkout)}"
: "${TRUSTED_TREE:?runner must set TRUSTED_TREE (full tree hash)}"
python3 "$TRUSTED_REPO/scripts/challenge/check-editable.py" --repo "$root" \
  --trusted-repo "$TRUSTED_REPO" --trusted-tree "$TRUSTED_TREE" \
  --allow ShorECDLP/Submission/Entrant
# 2. Source policy (no kernel-disable option) and layer rules.
python3 scripts/challenge/gate.py --source-only
SHORECDLP_ROOT="$root" python3 scripts/check-source.py
# 3. Build everything warning-fatal, then replay the protected Challenge and the entrant with the kernel.
lake --wfail build
python3 scripts/challenge/gate.py --replay ShorECDLP.Challenge
python3 scripts/challenge/gate.py --replay ShorECDLP.Submission.Entrant
# 4. Judge: acceptance theorem, axioms, score.
out="$(lake env lean scripts/Judge.lean 2>&1)"; printf '%s\n' "$out"
grep -q "'ShorECDLP.Judge.check_certificate' depends on axioms: \[propext, Classical.choice, Quot.sound\]\|'ShorECDLP.Judge.check_certificate' depends on axioms: \[propext\]\|does not depend on any axioms" <<<"$out" \
  || { echo "REJECT: certificate uses non-allowlisted axioms" >&2; exit 1; }
if grep -q "sorryAx" <<<"$out"; then echo "REJECT: sorry" >&2; exit 1; fi
echo "ACCEPT"
