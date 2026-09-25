# Completed-work integration

The program entry is `Submission.lean`. The target reference remains
arXiv:2607.13816v2. This inventory separates implemented connections from missing
mathematical results; an import alone is not a proof of program equivalence.

| Completed work | Production connection |
|---|---|
| Measured forward/reverse EEA, exchanged-bank inverse, selected CZ corrections | `Arithmetic/InPlace`, `SourceInPlace`, point arithmetic and both submission constructors |
| Reduced 256+208 sampling, raw-domain coverage, public-point decoder, actual resets and repetition | `Submission.trial`, `algorithm`, `certificate`, `decoder_sound` |
| Completed 26-round corrected-program contract | `Submission.corrected_certificate` |
| Fourier continuation, disjoint schedule commutation, validity under Fourier reset | `Fourier/Continuation`, `Window/ScheduleFourier`, `Window/FourierSupport` |
| Prepared-call reversal and direct-load coherent tail | `Window/PreparedOrder`, `Window/DirectOrderedTail` |
| Clean-bank permutation and raw block relocation | `Window/RawBankReuse`, used by `RawStream.streamRawCall_bank_run` and `Submission.Streaming.block_bank_reuse` |
| Complete-point-add block relocation | `Window/WeightedBlock`: both former prototype theorems now compiled and audited |
| Single reusable bank, actual branch reset, support and measurement accounting | `Window/RawStream`, exported as `Submission.Streaming.trial`, `resources`, `address_reset` |

The current streaming constructor uses the current raw core (including measured
inversion), not the former exceptionally repaired call. It prepares each 16-bit
bank, executes the appropriate weighted call, and carries the Fourier history
classically to the next block. The two axes keep independent histories. Its
support bound is 855 wires and it retains 847,701,655 measurements.

## Prototype reconciliation

All theorem/definition names in the workspace's checked prototypes were compared
against production. The remaining unmatched names were:

- `measuredWeightedBlock_relabel`, `measuredWeightedBlock_run`: integrated here.
- `circuit_seq_done`: integrated into `Framework/Quantum/AdaptiveComposition`.
- `reducedOutcomePair_injective`: already present as `unequalOutcomePair_injective`,
  used directly by the production `Window/ReducedTotal` proof. No duplicate is added.
- `reducedSecpWindowContract`: integrated as `Window/ReducedContract` and exported
  through `Submission.corrected_certificate`. It retains its own 26-round corrected
  program and must not be confused with the current 56-round raw program.

The older `paper-copied-add`/`paper-square` branch uses the name
`copiedModularAdd`; the same copy/add/un-copy constructor is already integrated as
`Arithmetic/Square.squareAdd`, with ideal-state, branch, well-formedness and full
square contracts. The adaptive-foundation branch declarations are also already
present in Framework.

Debug experiments are not missing implementation features. Historical notes saying
these prototypes were unintegrated predate their subsequent production PRs.

## History-dependent block composition

`Window/StreamHistory.lean` decomposes an actual streaming axis into its first
measured block and the remaining adaptive execution. The next Fourier history is
recovered from exactly the last sixteen block outcomes; internal arithmetic
measurements remain in the complete transcript but never enter feed-forward.
The ordered list of histories and unnormalized states is preserved when a block
is relocated to a clean parked bank, even through an arbitrary remaining axis
and tail. `streamRawCall_continuation_reuse` specializes this to current raw
arithmetic. Both source and destination banks must be clean.

This extends local block reuse through a continuation. It does not reorder all
arithmetic/Fourier operations or prove the whole-stream sampling distribution.

## MSB-first exceptional-input fibers

`Window/StreamFibers.lean` records the actual MSB-first table order: direct load
with weight 2^240, then P14..P0 and Q12..Q0. A circuit-list equality checks those
indexed tables against the current raw streaming calls. The logical banks in the
counting model hold the window assignments separately; this does not allocate
additional physical wires to the streaming constructor.

For every fixed assignment of the other logical banks, at most 112 of 65,536
first-window values violate the 28 raw-addition path exclusions, giving a
conditional uniform fraction at most 7/4096. The proof establishes injectivity
of the weighted first point and independence of all later calls from that word.
This is a finite conditional count, **not yet a Born-weight bound** for the
adaptive streaming input, and it supplies no new success probability.

## Logical reference input weight

`Window/StreamWeight.lean` lifts the conditional MSB-first count to a Born-mass
bound of 7/4096 for the excluded subspace of `streamLogicalEntryState`. This
reference preparation contains all 464 logical window wires simultaneously,
with the root control enabled. A separate theorem gives the same conditional
bound after the actual 16-wire Hadamard block on a clean basis background whose
other logical windows remain fixed.

The generic clean-Hadamard event/count and disjoint-word counting proofs are
shared with the existing reduced-program proof. Neither new bound identifies
an adaptive-stream failure event. Transport through the whole reused-bank
execution is still required before claiming a streaming success probability.

## Whole-axis relocation

`Window/StreamAxisReuse.lean` composes block relocation across an entire axis,
preserving the ordered list of full histories and unnormalized branch states.
All assigned banks and the reusable bank must initially be clean; subsequent
cleanliness is proved for each branch. Fourier feed-forward uses only the final
sixteen records of each block, and an arbitrary adaptive tail is retained.

`Window/RawAxisReuse.lean` instantiates the actual left-axis sequence (direct
lookup and fifteen raw additions) on banks 1–16, and the thirteen right-axis
additions on banks 17–29. These are interleaved instruments with preparation,
arithmetic and Fourier measurement at each block. They are not the fully
prepared `streamLogicalEntryState`. The latter still requires preparation
commutation, arithmetic/Fourier identification and decoder composition before
its exceptional mass bound can imply a success theorem for the streaming trial.

## Moving unused-bank preparation

`Framework/Quantum/AdaptiveHadamard.lean` proves that Hadamards on wires outside
an adaptive prefix commute with every Kraus branch, including measurement/reset
and outcome-dependent continuations. The evaluated instrument identity retains
ordered histories, unnormalized states and an arbitrary adaptive tail. It holds
for arbitrary inputs without cleanliness or separability assumptions.

`Window/StreamPreparation.lean` proves that a relocated block on bank k does not
use any different bank j, and moves preparation of j before that complete block.
The branchwise rule also crosses an entire relocated axis if all its assigned
banks and its tail avoid j. This is not yet a reordering theorem for the entire
two-axis schedule or a transfer of the reference-state bound.

## Preparing an entire axis at entry

`Window/StreamHoist.lean` separates each logical block's Hadamards from its
arithmetic/Fourier body and proves that all preparations for an axis can move
to its entry. This equality retains ordered complete histories and branch states
for arbitrary inputs and adaptive tails. The assigned banks must be distinct;
repeated-bank reuse does not justify hoisting preparation.

`indexedStreamAxis_prepared` composes this reordering with physical bank reuse:
with the original clean-bank premises, the actual physical axis equals its
unprepared logical-body instrument on the fully prepared axis input. This is a
single-axis result with the same tail. Combining both axes, matching logical
bank numbering to `streamLogicalEntryState`, and identifying arithmetic/Fourier
sampling and decoder events remain necessary for the 855-wire success claim.

## Two-axis physical trial correspondence

`TwoAxisHoist` moves both disjoint logical preparations to entry with separate
Fourier histories. `TwoAxisReuse` composes physical bank reuse across the axis
boundary: the first axis resets the reusable address and frames all parked
banks needed by the second. `RawTwoAxis.streamRawTrial_prepared` includes the
initial root X and final root cleanup and directly identifies the ordered
histories and unnormalized states of the actual `streamRawTrial` from zero with
`streamRawPreparedBody` on its simultaneously prepared logical input.

The comparison instrument uses banks 1–29, whereas `streamLogicalEntryState`
uses banks 0–28. `PreparedWeight.streamPreparedWire` now identifies each reference
bit with the corresponding prepared bit, preserving arithmetic addresses below
855. `streamRawPreparation_eq` identifies the actual preparation with 464
Hadamards on wires 871–1334. `streamRawPrepared_excluded_mass` transports the
reference bound of 7/4096 to the excluded input predicate on this same preparation.
This is a bound on input mass, not a bound on a physical failure or decoder event.

## Deferred Fourier maps

`StreamFourierCommute` proves that each actual arithmetic branch commutes with
Fourier measurement on a disjoint bank, including phase feedback and reset.
`StreamDeferred.unpreparedStreamAxis_deferred` moves every Fourier map after
its remaining axis and disjoint tail, preserving the original ordered full
transcript and Kraus maps on arbitrary states. Distinct banks are required.
`RawDeferred.streamRawTrial_deferred` connects both actual axes, initial setup
and final cleanup to this algebraic instrument. Each axis keeps independent
feedback; this is not a new physical circuit or a resource reduction.

The deferred maps still need to be identified with the ideal Fourier sampling
kernel and the decoder event. No success bound is inferred from commutation alone.

## Mathematical Fourier rows after actual arithmetic

`StreamKernel` factors each axis into arithmetic paths and one contiguous
Fourier branch, with a separate tag for Fourier bits and the original full
chronological history. `StreamTwoKernel` moves the left Fourier row through
all right-axis arithmetic and cleanup. `RawKernel.streamRawTrial_kernel`
identifies the actual trial with all arithmetic followed by the mathematical
256- and 208-bit Fourier rows, preserving amplitudes and every internal outcome.

The arithmetic maps in this expression are still the actual raw maps. Their
identification with the ideal scalar oracle on the permitted input set, the
exceptional-input perturbation bound and actual decoder acceptance remain open.

## Remaining proof obligations

The 855-wire construction still needs ideal scalar-oracle identification and
identification of the complete sampling distribution with a verified decoder
acceptance event. The two-axis correspondence preserves all histories and states,
and the prepared input now has the excluded-mass bound, but the connection to
output success remains unproved. Thus the actual success theorem continues to
apply to the 1,303-wire program. The 835-wire goal, stronger success analysis and
efficient executable classical decoder remain unfinished work.

## Earlier alternative implementation

The open PR #53 is the earlier Fermat/checkpoint exponentiation implementation,
stacked on `proof/low-qubit-modmul`. It is not an implementation of this paper's
EEA algorithm. It remains separate from this integration, following the adopted
Naive/paper submission isolation in `docs/PLAN.md` §2. No arithmetic implementation
from that branch is imported into the paper submission.

`Window/PreparedArithmetic` transports the counted exclusions from reference
banks 0–28 to prepared banks 1–29, preserving each selected signed table point.
It identifies the 28 relocated raw addition calls and proves coherent semantics
for their group-walk endpoint, including the complete non-point frame. The
incoming point encoding and readiness remain hypotheses; first-lookup
initialization, scalar reconstruction of this endpoint, and connection to the
Fourier path enumeration are still required before a full streaming success
contract follows.

`Window/StreamRecords` parses the original chronological trial records by following
arithmetic measurement branches and extracting each subsequent 16-bit Fourier
block. It proves equality with the existing left/right Fourier path labels, with
256/208 bits in unchanged order, and rejects incomplete blocks and trailing data.
The public-point decoder consumes this parsed record. Its accepted event is the
actual history event, and its probability equals a nested path-list sum preserving
every occurrence and internal arithmetic branch. No path or history deduplication
is used. This is a noncomputable decoder specification; the numerical single-trial
success lower bound, retry count, and complete 855-wire success contract remain open.

`Window/PreparedLookup` connects the actual direct lookup relocated to bank 1
to the 28 prepared raw additions. From point-initialization readiness and the
original counted exclusions, `streamPreparedArithmetic_coherent` proves one
coherent complete point-write map for their composition. The lookup establishes
the initial point and preserves the exclusions. The resulting group-walk endpoint is reconstructed by `Window/StreamScalar`
as the two MSB-first scalar values multiplied by P and Q. The scalar convention
is proved equal to the reversed existing radix digit list, with 256/208-bit
bounds. `streamPreparedArithmetic_scalars_coherent` retains the original
initialization and exclusion premises and the complete point-write frame.
Fourier-path enumeration and root cleanup must still be connected before an
actual trial success bound. The preparation premise is discharged below.

`Window/PreparedEntry` proves that the actual 464-Hadamard preparation is
supported on the clean initialization predicate. Filtering this same state by
the previously counted path exclusions supplies the complete premise of the
prepared scalar arithmetic theorem. Every original arithmetic branch has its
aligned input-independent coefficient, with total squared mass one; any terminal
instrument therefore has exactly the corresponding ideal good-component mass.
This input filtering is a mathematical decomposition, not physical postselection.
The interleaved Fourier arithmetic paths and final root cleanup still need to be
identified with this composition before an actual streaming success bound follows.

`Window/StreamPathMass` rearranges the actual record-acceptance mass into
the complete relocated arithmetic instrument followed by the same selected
256+208 Fourier rows on each branch. All list occurrences remain separate
contributions. This closes the history-dependent path-sum interface; the arithmetic and
root-cleanup connection is provided by `StreamGoodFourier` below.
No positive streaming success bound follows from this rearrangement alone.

`Window/StreamGoodFourier` identifies that arithmetic fold with the actual
prepared lookup and raw scalar schedule, retaining final X 836 cleanup. It
constructs the common selected Fourier instrument and connects its mass to
the actual full-record acceptance event. On the original good input component,
all arithmetic histories sum to the scalar output's selected Fourier mass;
root cleanup leaves that mass unchanged. This does not turn input filtering
into physical postselection. The bad component and interference are bounded by `StreamInterference` below;
the ideal sampling lower bound, repetition and unified 855-wire success
contract remain open.

`Window/StreamInterference` proves the actual selected terminal is contractive
on every input, including excluded inputs. With the original 7/4096 excluded
input mass and two coherent interference comparisons, actual record acceptance
is at least 9/16 of the full ideal scalar output's Fourier event mass minus
147/16384. This is an event comparison, not a positive numerical success bound:
the full ideal event still needs its sampling lower bound connected.
