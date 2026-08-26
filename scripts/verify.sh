#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

if [[ -n "${CI_BASE_SHA:-}" ]] && git cat-file -e "${CI_BASE_SHA}^{commit}" 2>/dev/null; then
  git diff --check "${CI_BASE_SHA}...HEAD"
else
  git diff --check HEAD^...HEAD
fi

# Lean reports `sorry`/`admit` as warnings, so make the compiler's own parser
# authoritative instead of attempting to duplicate Lean's extensible syntax in a hand lexer.
lake --wfail build

# Ask Lean itself for every module's imports, then reject out-of-tree sources and
# anything not reachable from the root aggregator.
SHORECDLP_ROOT="$repo_root" python3 "$script_dir/check-source.py"

axiom_output="$({ lake env lean /dev/stdin <<'LEAN'
import ShorECDLP
#print axioms ShorECDLP.modAdd_contract
#print axioms ShorECDLP.ModAddSupport.modAdd_usesOnly
#print axioms ShorECDLP.ModAddSupport.modAddCompute_usesOnly
#print axioms ShorECDLP.ModMul.Plan.modMul_contract
#print axioms ShorECDLP.ModExp.Plan.modExp_contract
#print axioms ShorECDLP.ModExp.Plan.modExp_contract_uniform
#print axioms ShorECDLP.ModExp.Schedule.forward_correct
#print axioms ShorECDLP.ModExp.Plan.program_tCount_eq_of_uniform
#print axioms ShorECDLP.FermatInv.correct
#print axioms ShorECDLP.Arithmetic.zeroFlag_correct
#print axioms ShorECDLP.Arithmetic.zeroFlag_tCount
#print axioms ShorECDLP.Arithmetic.equalFlag_correct
#print axioms ShorECDLP.Arithmetic.equalFlag_tCount
#print axioms ShorECDLP.Precompute.doublingTable_getElem
#print axioms ShorECDLP.Precompute.doublingTable_adjacent
#print axioms ShorECDLP.Secp256k1.encode_injective
#print axioms ShorECDLP.Secp256k1.validCode_iff_exists_point
#print axioms ShorECDLP.Secp256k1.PointRegister.slices_write_some
#print axioms ShorECDLP.Secp256k1.PointRegister.regValue_padCoordinate_of_clean
#print axioms ShorECDLP.Secp256k1.curve_discriminant_ne_zero
#print axioms ShorECDLP.Secp256k1.generator_equation
#print axioms ShorECDLP.Secp256k1.G_ne_zero
#print axioms ShorECDLP.Reduction.oracleExponent_shiftBy
#print axioms ShorECDLP.Reduction.annihilatesPeriod_iff
#print axioms ShorECDLP.Reduction.recoverShift_correct
#print axioms ShorECDLP.Quantum.qft_correct
#print axioms ShorECDLP.Quantum.tCount_qft
#print axioms ShorECDLP.Quantum.qft_wellFormed
#print axioms ShorECDLP.Quantum.normSq_run_qft_ket
#print axioms ShorECDLP.Quantum.run_adjoint_run
#print axioms ShorECDLP.Quantum.run_run_adjoint
#print axioms ShorECDLP.Quantum.iqft_correct
#print axioms ShorECDLP.Quantum.tCount_iqft
#print axioms ShorECDLP.Quantum.iqft_wellFormed
#print axioms ShorECDLP.Quantum.PhaseEstimation.phaseEstimation_correct_exact
#print axioms ShorECDLP.Quantum.PhaseEstimation.phaseEstimation_correct_approx
#print axioms ShorECDLP.ECDLPOracleSpec.ofCircuit
#print axioms ShorECDLP.Quantum.OrderFinding.orderFinding_correct
LEAN
} 2>&1)"
printf '%s\n' "$axiom_output"
if [[ "$(printf '%s\n' "$axiom_output" | awk '/^\047/ { n++ } END { print n + 0 }')" -ne 38 ]]; then
  printf 'expected thirty-eight #print axioms results\n' >&2
  exit 1
fi

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
