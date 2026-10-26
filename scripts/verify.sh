#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"
export SHORECDLP_ROOT="$repo_root"

bash -n "$script_dir/verify.sh"
python3 "$script_dir/test-axiom-manifests.py"

if [[ -n "${CI_BASE_SHA:-}" ]] && git cat-file -e "${CI_BASE_SHA}^{commit}" 2>/dev/null; then
  git diff --check "${CI_BASE_SHA}...HEAD"
else
  git diff --check HEAD^...HEAD
fi

# Lean reports `sorry`/`admit` as warnings, so make the compiler's own parser
# authoritative instead of attempting to duplicate Lean's extensible syntax in a hand lexer.
python3 scripts/challenge/test-editable.py
python3 scripts/challenge/test-runner-boundary.py
python3 scripts/challenge/gate.py --source-only
lake --wfail build
lake env lean ShorECDLP/Challenge/Smoke.lean
lake env lean ShorECDLP/Challenge/StraightSmoke.lean
lake env lean ShorECDLP/Challenge/DecoderSmoke.lean

python3 scripts/challenge/gate.py --replay ShorECDLP.Challenge
python3 scripts/challenge/regressions.py
python3 scripts/challenge/judge_regressions.py

# Ask Lean itself for every module's imports, then reject out-of-tree sources and
# anything not reachable from the root aggregator.
SHORECDLP_ROOT="$repo_root" python3 "$script_dir/check-source.py"

# Each explicit disclosure lives beside the other entries from its defining module.
# Count and exact output coverage are derived from these files, never a hand-edited total.
axiom_output="$({ python3 "$script_dir/axiom-manifests.py" commands |
  python3 "$script_dir/print-axioms.py"; } 2>&1)"
printf '%s\n' "$axiom_output"
printf '%s\n' "$axiom_output" | python3 "$script_dir/axiom-manifests.py" check-output

allowed_axioms=$'Classical.choice\nQuot.sound\npropext'
seen_axioms="$({
  printf '%s\n' "$axiom_output" \
    | sed -n 's/^.*depends on axioms: \[\(.*\)\]$/\1/p' \
    | tr ',' '\n' \
    | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' \
    | sed '/^$/d' \
    | sort -u
} )"
unexpected_axioms="$(comm -23 \
  <(printf '%s\n' "$seen_axioms" | sed '/^$/d' | sort -u) \
  <(printf '%s\n' "$allowed_axioms" | sort -u))"
if [[ -n "$unexpected_axioms" ]]; then
  printf 'unexpected axiom(s) in #print axioms output:\n%s\n' "$unexpected_axioms" >&2
  exit 1
fi

# Exhaustively audit every declaration defined by a project module. This is the
# authoritative gate for `axiom`, `constant`, `native_decide`, and other non-allowlisted
# trust dependencies; the targeted prints retain the human-readable M1/QFT disclosure.
axiom_audit_sha=46024e005996495c65ef609368e11ab39c4222e3
audit_dir="$(mktemp -d "${RUNNER_TEMP:-/tmp}/shorecdlp-axiom-audit.XXXXXX")"
cleanup() { rm -rf "$audit_dir"; }
trap cleanup EXIT

git -C "$audit_dir" init --quiet
git -C "$audit_dir" fetch --quiet --depth 1 \
  https://github.com/leanprover-community/axiom-audit.git "$axiom_audit_sha"
git -C "$audit_dir" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$audit_dir" rev-parse HEAD)" = "$axiom_audit_sha"
cp lean-toolchain "$audit_dir/lean-toolchain"
(cd "$audit_dir" && lake build)

lake env "$audit_dir/.lake/build/bin/axiom-audit" \
  --root ShorECDLP \
  --allow propext,Classical.choice,Quot.sound
