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
#print axioms ShorECDLP.modAdd_program_correct
#print axioms ShorECDLP.modAdd_tCount
#print axioms ShorECDLP.ModAddSupport.modAdd_usesOnly
#print axioms ShorECDLP.ModAddSupport.modAddCompute_usesOnly
#print axioms ShorECDLP.modSub_contract
#print axioms ShorECDLP.modSub_program_correct
#print axioms ShorECDLP.modSub_tCount
#print axioms ShorECDLP.modSub_usesOnly
#print axioms ShorECDLP.modSubCompute_usesOnly
#print axioms ShorECDLP.ModMul.Plan.modMul_contract
#print axioms ShorECDLP.ModMul.Plan.program_correct
#print axioms ShorECDLP.ModMul.Plan.program_tCount
#print axioms ShorECDLP.ModExp.Plan.modExp_contract
#print axioms ShorECDLP.ModExp.Plan.program_correct
#print axioms ShorECDLP.ModExp.Plan.program_tCount
#print axioms ShorECDLP.ModExp.Plan.modExp_contract_uniform
#print axioms ShorECDLP.ModExp.Schedule.forward_correct
#print axioms ShorECDLP.ModExp.Plan.program_tCount_eq_of_uniform
#print axioms ShorECDLP.FermatInv.correct
#print axioms ShorECDLP.Secp256k1Instance.addProgram_correct
#print axioms ShorECDLP.Secp256k1Instance.addProgram_tCount
#print axioms ShorECDLP.Secp256k1Instance.placedMulPlan_program_correct
#print axioms ShorECDLP.Secp256k1Instance.placedMulPlan_program_tCount
#print axioms ShorECDLP.Secp256k1Instance.secp_modAdd_contract
#print axioms ShorECDLP.Secp256k1Instance.secpAddProgram_correct
#print axioms ShorECDLP.Secp256k1Instance.secpAddProgram_tCount
#print axioms ShorECDLP.Secp256k1Instance.secp_modMul_contract
#print axioms ShorECDLP.Secp256k1Instance.secpMulProgram_correct
#print axioms ShorECDLP.Secp256k1Instance.secpMulProgram_tCount
#print axioms ShorECDLP.Secp256k1Instance.secp_modExp_contract
#print axioms ShorECDLP.Secp256k1Instance.secpProgram_correct
#print axioms ShorECDLP.Secp256k1Instance.secpProgram_tCount
#print axioms ShorECDLP.Secp256k1Instance.secp_fermat_inverse
#print axioms ShorECDLP.Secp256k1.pointAddFiniteCompute_tCount
#print axioms ShorECDLP.Secp256k1.pointAdd_zero_tCount
#print axioms ShorECDLP.Secp256k1.pointAdd_finite_tCount
#print axioms ShorECDLP.Secp256k1.pointAdd_correct
#print axioms ShorECDLP.Secp256k1.controlledPointAdd_correct
#print axioms ShorECDLP.Secp256k1.controlledPointAdd_zero_tCount
#print axioms ShorECDLP.Secp256k1.controlledPointAdd_tCount_of_ne_zero
#print axioms ShorECDLP.Secp256k1.controlledPointAdd_HPFree
#print axioms ShorECDLP.Secp256k1.controlledPointAdd_wellFormed
#print axioms ShorECDLP.Secp256k1.scalarMul_correct
#print axioms ShorECDLP.Secp256k1.scalarMul_tCount_of_table_ne_zero
#print axioms ShorECDLP.Secp256k1.scalarMul_HPFree
#print axioms ShorECDLP.Secp256k1.scalarMul_wellFormed
#print axioms ShorECDLP.Secp256k1.ecdlpOracle_correct
#print axioms ShorECDLP.Secp256k1.ecdlpOracle_tCount_of_tables_ne_zero
#print axioms ShorECDLP.Secp256k1.ecdlpOracle_HPFree
#print axioms ShorECDLP.Secp256k1.ecdlpOracle_wellFormed
#print axioms ShorECDLP.Secp256k1.ecdlpOracle_spec
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
#print axioms ShorECDLP.Secp256k1.p_prime
#print axioms ShorECDLP.Secp256k1.order_prime
#print axioms ShorECDLP.Secp256k1.generator_nsmul_eq_zero
#print axioms ShorECDLP.Secp256k1.generator_order
#print axioms ShorECDLP.Reduction.oracleExponent_shiftBy
#print axioms ShorECDLP.Reduction.annihilatesPeriod_iff
#print axioms ShorECDLP.Reduction.recoverShift_correct
#print axioms ShorECDLP.Quantum.OrderFinding.jointRegisterProbability_nonneg
#print axioms ShorECDLP.Quantum.OrderFinding.jointRegisterProbability_sum_eq_normSq
#print axioms ShorECDLP.Quantum.OrderFinding.orderFindingSuccessProbability_le_normSq
#print axioms ShorECDLP.Quantum.projectZ_ket
#print axioms ShorECDLP.Quantum.xResetKraus_ket
#print axioms ShorECDLP.Quantum.xResetKraus_clean
#print axioms ShorECDLP.Quantum.normSq_xResetKraus_ket
#print axioms ShorECDLP.Quantum.normSq_xResetKraus_false_add_true
#print axioms ShorECDLP.Quantum.AdaptiveCircuit.run_xMeasureReset_done_clean
#print axioms ShorECDLP.Quantum.AdaptiveCircuit.run_seq
#print axioms ShorECDLP.Quantum.AdaptiveCircuit.WellFormed.seq
#print axioms ShorECDLP.Quantum.AdaptiveCircuit.run_preservesBornMass
#print axioms ShorECDLP.Quantum.AdaptiveCircuit.run_bornMass_eq_one
#print axioms ShorECDLP.Quantum.CoherentlyImplementsOn
#print axioms ShorECDLP.Quantum.CoherentlyImplementsOn.unitary
#print axioms ShorECDLP.Quantum.CoherentlyImplementsOn.seq
#print axioms ShorECDLP.Quantum.CoherentlyImplementsOn.tensor_or_disjoint
#print axioms ShorECDLP.Quantum.coherent_on_supported_state
#print axioms ShorECDLP.Quantum.eventProbability_smul
#print axioms ShorECDLP.Quantum.coherent_final_probability_eq
#print axioms ShorECDLP.Quantum.run_controlledZ_ket
#print axioms ShorECDLP.Quantum.clearRegister_clean
#print axioms ShorECDLP.Quantum.registerXResetCoeff_eq_magnitude_mul_phase
#print axioms ShorECDLP.Quantum.xResetRegisterKraus_ket
#print axioms ShorECDLP.Quantum.xResetRegisterKraus_clean
#print axioms ShorECDLP.Quantum.run_measureResetWithCorrection
#print axioms ShorECDLP.Quantum.measureResetWithCorrection_coherent
#print axioms ShorECDLP.Quantum.measureResetWithCorrection_wellFormed
#print axioms ShorECDLP.Quantum.measureResetWithCorrection_measurementCount
#print axioms ShorECDLP.Quantum.run_registerZCorrection_ket
#print axioms ShorECDLP.Quantum.recomputeZCorrection_phase
#print axioms ShorECDLP.Quantum.recomputeMeasurementUncompute_coherent
#print axioms ShorECDLP.Quantum.recomputeMeasurementUncompute_coherent_of_classical
#print axioms ShorECDLP.Paper2607_13816.run_idealCPhase_ket
#print axioms ShorECDLP.Paper2607_13816.andCorrection_phase
#print axioms ShorECDLP.Paper2607_13816.andErase_coherent
#print axioms ShorECDLP.Paper2607_13816.adaptiveCPhase_coherent
#print axioms ShorECDLP.Paper2607_13816.adaptiveCPhase_wellFormed
#print axioms ShorECDLP.Paper2607_13816.adaptiveCPhase_measurementCount
#print axioms ShorECDLP.Paper2607_13816.adaptiveCPhase_tCount
#print axioms ShorECDLP.Paper2607_13816.andCorrection_toffoliCount
#print axioms ShorECDLP.Paper2607_13816.adaptiveCPhase_toffoliCount
#print axioms ShorECDLP.Paper2607_13816.adaptiveCPhase_qubitCount
#print axioms ShorECDLP.Paper2607_13816.adaptiveCPhase_preservesBornMass
#print axioms ShorECDLP.Paper2607_13816.paperInitial_correction
#print axioms ShorECDLP.Paper2607_13816.paperStep_remainders
#print axioms ShorECDLP.Paper2607_13816.paperPhaseTrace_nonterminal
#print axioms ShorECDLP.Paper2607_13816.packedFields_nonoverlap
#print axioms ShorECDLP.Paper2607_13816.paperStep_preservesInvariant
#print axioms ShorECDLP.Paper2607_13816.paperStep_reversible_onInvariant
#print axioms ShorECDLP.Paper2607_13816.paperRun_terminal
#print axioms ShorECDLP.Paper2607_13816.paperRun_inverse_mod_prime
#print axioms ShorECDLP.Paper2607_13816.paperRun_padding_is_id
#print axioms ShorECDLP.Paper2607_13816.eeaPotential_step
#print axioms ShorECDLP.Paper2607_13816.PaperBoundaryReachable.spent_lt_size
#print axioms ShorECDLP.Paper2607_13816.PaperBoundaryReachable.spent_add_remaining
#print axioms ShorECDLP.Paper2607_13816.paperQuotientWeight_le_405
#print axioms ShorECDLP.Paper2607_13816.secp256k1_paperMicrosteps_le_1620
#print axioms ShorECDLP.Paper2607_13816.paperIndexedFrame_exists
#print axioms ShorECDLP.Paper2607_13816.secp256k1_paperPadding_le_596
#print axioms ShorECDLP.Paper2607_13816.compress_terminalShiftEpoch_fst
#print axioms ShorECDLP.Paper2607_13816.compress_terminalShiftEpoch_restore
#print axioms ShorECDLP.Paper2607_13816.secp256k1_terminalPadding_certificate
#print axioms ShorECDLP.Paper2607_13816.certifiedRemainderWindow_start_le_reference
#print axioms ShorECDLP.Paper2607_13816.PaperActiveFrame.windowCertificate
#print axioms ShorECDLP.Paper2607_13816.secp256k1_activeWindowCertificate_of_le
#print axioms ShorECDLP.Paper2607_13816.paperPhaseTrace_fieldsNonoverlap
#print axioms ShorECDLP.Paper2607_13816.run_controlledSwap
#print axioms ShorECDLP.Paper2607_13816.run_dirtyC3X
#print axioms ShorECDLP.Paper2607_13816.run_cleanC3X
#print axioms ShorECDLP.Paper2607_13816.run_controlledRotateLeftOne_values
#print axioms ShorECDLP.Paper2607_13816.controlledIncrement_correct
#print axioms ShorECDLP.Paper2607_13816.controlledIncrement_wellFormed
#print axioms ShorECDLP.Paper2607_13816.controlledIncrement_tCount
#print axioms ShorECDLP.Paper2607_13816.measuredAndCorrection_phase
#print axioms ShorECDLP.Paper2607_13816.eraseZeroAnd_coherent
#print axioms ShorECDLP.Paper2607_13816.eraseZeroAnd_wellFormed
#print axioms ShorECDLP.Paper2607_13816.run_unaryIterationUnitary
#print axioms ShorECDLP.Paper2607_13816.unaryIteration_coherent
#print axioms ShorECDLP.Paper2607_13816.unaryIteration_wellFormed
#print axioms ShorECDLP.Paper2607_13816.unaryIteration_measurementCount
#print axioms ShorECDLP.Paper2607_13816.unaryIteration_tCount
#print axioms ShorECDLP.Paper2607_13816.run_controlledMaj
#print axioms ShorECDLP.Paper2607_13816.run_controlledUma
#print axioms ShorECDLP.Paper2607_13816.run_controlledMajInv
#print axioms ShorECDLP.Paper2607_13816.run_controlledUmaInv
#print axioms ShorECDLP.Paper2607_13816.run_controlledMaj_state
#print axioms ShorECDLP.Paper2607_13816.run_controlledUma_state
#print axioms ShorECDLP.Paper2607_13816.run_controlledMajInv_state
#print axioms ShorECDLP.Paper2607_13816.run_controlledUmaInv_state
#print axioms ShorECDLP.Paper2607_13816.run_controlledWindowRipple
#print axioms ShorECDLP.Paper2607_13816.controlledWindowRipple_wellFormed
#print axioms ShorECDLP.Paper2607_13816.controlledWindowRipple_usesOnly
#print axioms ShorECDLP.Paper2607_13816.controlledWindowRipple_protected
#print axioms ShorECDLP.Paper2607_13816.controlledWindowRipple_toffoliCount
#print axioms ShorECDLP.Paper2607_13816.controlledWindowRipple_cnotCount
#print axioms ShorECDLP.Paper2607_13816.controlledWindowRipple_tCount
#print axioms ShorECDLP.Paper2607_13816.run_borrowedXorBit
#print axioms ShorECDLP.Paper2607_13816.run_borrowedXorWriter_state
#print axioms ShorECDLP.Paper2607_13816.borrowedXorWriter_wellFormed
#print axioms ShorECDLP.Paper2607_13816.borrowedXorWriter_usesOnly
#print axioms ShorECDLP.Paper2607_13816.borrowedXorWriter_restoresDirty
#print axioms ShorECDLP.Paper2607_13816.borrowedXorWriter_cnotCount
#print axioms ShorECDLP.independentRetrySuccessProbability_succ
#print axioms ShorECDLP.independentRetrySuccessProbability_mono
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
#print axioms ShorECDLP.Secp256k1.ecdlpTrial_run
#print axioms ShorECDLP.Secp256k1.ecdlpTrial_tCount
#print axioms ShorECDLP.Secp256k1.ecdlpTrial_wellFormed
#print axioms ShorECDLP.Secp256k1.orderFinding_correct
#print axioms ShorECDLP.Quantum.OrderFinding.nearestNumerator
#print axioms ShorECDLP.Quantum.OrderFinding.orderFindingPostprocess
#print axioms ShorECDLP.BitcoinECDLPSubmission
#print axioms ShorECDLP.Secp256k1.bitcoinECDLPTrial_correct
#print axioms ShorECDLP.Secp256k1.bitcoinECDLP_correct
#print axioms ShorECDLP.Secp256k1.bitcoinECDLPSubmission
#print axioms ShorECDLP.Secp256k1.bitcoinECDLPTotalGateCount_correct
#print axioms ShorECDLP.qubitCount
#print axioms ShorECDLP.Secp256k1.bitcoinECDLPTrial_qubitCount
LEAN
} 2>&1)"
printf '%s\n' "$axiom_output"
if [[ "$(printf '%s\n' "$axiom_output" | awk '/^\047/ { n++ } END { print n + 0 }')" -ne 203 ]]; then
  printf 'expected two hundred three #print axioms results\n' >&2
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
