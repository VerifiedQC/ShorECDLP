#!/usr/bin/env bash
# PROTECTED controller. Never run this controller inside the entrant build worker.
# CANDIDATE_BUILDER is an evaluator-owned adapter: restore trusted caches AFTER
# the boundary check, run verify.sh in an isolated worker, then terminate ALL
# worker processes and freeze its outputs before returning success.
set -euo pipefail
: "${CANDIDATE:?runner must set CANDIDATE}"
: "${TRUSTED_REPO:?runner must set TRUSTED_REPO}"
: "${TRUSTED_TREE:?runner must set TRUSTED_TREE}"
: "${CANDIDATE_BUILDER:?runner must supply an isolated build adapter}"
trusted_scripts="$(cd "$(dirname "$0")" && pwd)"

python3 "$trusted_scripts/challenge/check-editable.py" --repo "$CANDIDATE" \
  --trusted-repo "$TRUSTED_REPO" --trusted-tree "$TRUSTED_TREE" \
  --allow ShorECDLP/Submission/Entrant
python3 "$trusted_scripts/challenge/gate.py" --root "$CANDIDATE" --source-only

# The adapter receives paths as separate arguments, not shell text to evaluate.
# It must set SHORECDLP_ROOT=CANDIDATE for the protected verification tools.
"$CANDIDATE_BUILDER" "$CANDIDATE" "$TRUSTED_REPO" "$trusted_scripts/verify.sh"

# Final checks run outside the stopped worker. Only entrant artifacts are copied;
# candidate-produced Framework/Challenge/Judge artifacts are never imported here.
overlay="$(mktemp -d "${RUNNER_TEMP:-/tmp}/shorecdlp-entrant.XXXXXX")"
trap 'rm -rf "$overlay"' EXIT
python3 "$trusted_scripts/challenge/stage-entrant.py" \
  --candidate "$CANDIDATE" --overlay "$overlay" \
  --trusted-lib "$TRUSTED_REPO/.lake/build/lib/lean"
cd "$TRUSTED_REPO"
export SHORECDLP_ROOT="$TRUSTED_REPO"
# Do not inherit a candidate search path into the controller.
unset LEAN_PATH LEAN_SRC_PATH
python3 "$trusted_scripts/challenge/gate.py" --root "$TRUSTED_REPO" \
  --replay ShorECDLP.Submission.Entrant --artifact-path "$overlay"
# This trusted script imports only Lean at elaboration time. Runtime import does
# not load entrant extensions; acceptance and metrics use direct kernel Expr APIs.
lake env lean --run "$trusted_scripts/challenge/judge.lean" "$overlay"
