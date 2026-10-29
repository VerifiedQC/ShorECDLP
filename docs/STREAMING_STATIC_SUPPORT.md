# Streaming static support (work in progress)

The existing `batchedResetWires` list has 3,931 entries. It is **not** a complete
static allocation for the current coordinate program: the zero-divisor wrapper
uses wire 837, including `CX 837 263`. The earlier claim that 837 was unused was
incorrect. A complete candidate allocation must include this port, giving 3,932
entries before any further proof of deduplication or tighter actual usage.
Wire 838 is the infinity flag. Address/sign wires 839–854 are relocated to 855–870.
The full compiler-support proof must check every excluded wire; list length alone
is not an actual-program qubit bound.

`BatchSupport.lean` proves that every static correction-block wire, after both
actual permutations, lies in this allocation. Disabled constant-controlled gates,
measurement targets, record-controlled gates, and both corrections are included.
The temporary sixth component word is moved onto actual accumulator ports.

`ArithmeticSupport.lean` proves support transfer for compiled adders, comparisons,
negation and the actual shared Y-negation stage. `ControlSupport.lean` additionally
proves removal of the comparator's virtual control, then covers modular addition
and the actual constant-field lookup stages.

`WindowSupport.lean` provides explicitly conditional composition lemmas. Its
`batchedOuter_qubits_le_of_coordinate` bounds the cardinality of the actual
program's deduplicated wire set for any repetition count, **assuming** concrete
coordinate-compiler support. The coordinate-support premise is false for the current full program because
837 is absent from that list, so this conditional 3,931 bound cannot be used.
It is not a completed Streaming resource certificate.

`WrapperSupport.lean` discharges the layouts for every production step using
`secp256k1ScheduleLayout_production`. Both measured 1,620-step schedules, their
complete wrappers, and exchanged data banks have compiler-support proofs.
`InPlaceSupport.lean` covers both in-place operations, including resets and
retained-record corrections. `CoordinateSupport.lean` covers all nine actual
coordinate segments and proves that the zero-divisor wrapper touches wire 837.

`CompleteSupport.lean` uses `completeBatchedSupport = 837 :: batchedResetWires`.
It proves containment for every actual first/odd window and for the entire repeated
outer program, for arbitrary constant reads, initial record history and repetition
count (including the actual 56 rounds). Thus the **deduplicated actual wire set has
cardinality at most 3,932**. This is an upper bound, not a claim of exactly 3,932
used wires. All other excluded addresses are covered by these containment proofs;
none are declared unused merely from the allocation list. Reset behavior is not
changed by the larger static allocation.

Success semantics and the final challenge certificate remain separate obligations.
The frozen published challenge is unchanged.

## Resource certificate shell

`ResourceCertificate.lean` packages the actual 56-round program and its fixed
983040-row coefficient table as `streamingEntry`. Its protected evaluator bounds
are 3932 qubits and 806028979896 abstract T units; its measurement count is exactly
48194018992. These resource statements hold for every public point Q. `UniformT.lean`
removes the unnecessary group-order premise from the older T-count bridge by
counting actual lookup gates independently of their constant bits.

The gate-slot upper bound is 5000000000000. The shell proves the organizer's
admission fields: gate slots, records, coefficient rows, and candidate budget.
`officialLimits` does not impose qubit or T caps; those are declared resource
bounds. The record check uses the development cap 50000000000 introduced by PR518;
the older frozen cap 47471340504 does not admit this program.

`streamingEntry_certificate` takes only the actual protected success-probability
statement as a parameter. It is a conditional shell, not an unconditional
certificate, accepted judge result, or release approval. The decoder is the actual
outer plan's fixed 56-round layout, with wrappedShift and legacyDecoderParams.
