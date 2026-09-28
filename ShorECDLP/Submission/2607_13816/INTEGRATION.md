# Completed-work integration

`Submission.lean` exports both the original raw program and the streaming program.
The reference remains arXiv:2607.13816v2. All success statements retain their
nonzero public-point, subgroup and public-point relation premises; inputs start
in the all-zero state. The decoders are mathematical specifications.

| Entry | Program and proved contract |
|---|---|
| `Submission.trial`, `algorithm`, `certificate`, `decoder_sound` | Original raw program: ≤1,303 wires, ≥8% single-trial acceptance, ≥99% for 56 reset trials, and its existing gate-resource bounds |
| `Submission.Streaming.trial`, `trial_certificate` | Actual streaming program: ≤855 wires, 847,701,655 measurements, ≥8% public-decoder acceptance, and correctness of accepted scalars |
| `Submission.Streaming.algorithm`, `candidate`, `certificate`, `decoder_sound`, `algorithm_zero` | The same streaming trial reset and repeated 56 times: ≤855 wires, ≤47,471,340,560 measurements, ≥99% acceptance, accepted-scalar correctness and branchwise final zero state |
| `Submission.corrected_certificate` | Separate completed 26-round corrected-program contract |

`Streaming.trial_gate_resources`, `algorithm_gate_resources` and `gate_certificate`
now prove gate bounds directly for the streaming program, as detailed below.
T-model costs are not synthesized Clifford+T counts.

## Arithmetic and physical execution

Measured forward/reverse EEA, exchanged-bank inverse and selected CZ corrections
are used by `Arithmetic/InPlace`, `SourceInPlace` and the current raw point calls.
`Window/RawStream` uses these calls in a single reused address bank, with a direct
load followed by P14..P0 and Q12..Q0. Each axis carries its own Fourier history.

`RawBankReuse`, `RawAxisReuse`, `WeightedBlock`, `StreamHistory`, `StreamHoist`,
`TwoAxisHoist`, `TwoAxisReuse` and `RawTwoAxis` connect local relocation and the
actual two-axis circuit. Complete ordered arithmetic and Fourier histories,
unnormalized branch states and clean-bank premises are retained. `StreamKernel`,
`RawKernel` and `RawDeferred` defer the Fourier operations through disjoint future
arithmetic. These are physical correspondence theorems, not postselection.

## Sampling and success proof chain

1. `StreamFibers`, `StreamWeight`, `StreamPreparation` and `PreparedWeight` prove
   the excluded input mass is at most 7/4096 in the actual preparation. This
   input mass is not directly treated as an output failure probability.
2. `PreparedArithmetic`, `PreparedLookup`, `StreamScalar` and `PreparedEntry`
   connect the initial lookup and all 28 raw additions to aP+bQ on the original
   good input component, with the complete non-point frame.
3. `StreamRecords` parses the full chronological record into the two Fourier
   outputs, rejects incomplete/trailing trial records and connects the actual
   public decoder event. All measurement-list occurrences remain counted.
4. `StreamPathMass` and `StreamGoodFourier` combine every arithmetic branch with
   the same selected Fourier terminal and account for final root cleanup.
   `StreamInterference` bounds actual acceptance by 9/16 of the full ideal event
   mass minus 147/16384, including both coherent interference comparisons.
5. `StreamScalarWord`, `StreamUniform` and `StreamAssignedKernel` identify scalar
   words with the actual Fourier wire order, normalize the uniform preparation,
   and prove each assigned point-state amplitude. The retained root is true at
   this intermediate ideal boundary; root isometry removes its effect on mass.
6. `StreamSamplingSuccess` sums amplitudes at equal point states before taking
   norms, identifies the ideal selected event with the existing asymmetric
   sampling distribution, and proves ≥8% actual public-decoder acceptance.
   Total actual trial mass is one. Its joint certificate refers to the same
   855-wire trial for resources, acceptance and decoder correctness.
7. `StreamResetRepetition` resets every used wire after each trial. The parser
   consumes the trial prefix while all reset outcomes remain in the instrument.
   Every branch returns to zero, reset preserves acceptance, and the sequential
   instrument gives the 56-trial ≥99% contract exported by `Submission.Streaming`.

8. `StreamGateCounts` counts the actual interleaved streaming program. Fourier
   rotations add no Toffoli gates; their phase budgets are 32,640 and 21,528.
   One trial has 2,040,822,631 Toffoli gates and T-model ≤14,285,812,585.
   The 56-trial program has 114,286,067,336 Toffoli gates and T-model
   ≤800,005,504,760. `Streaming.gate_certificate` binds these bounds to
   the same 855-wire program and its ≥99% acceptance contract.

## Remaining scope

The 835-wire target, stronger
success analysis, phase-rotation synthesis/error budgets and an efficient
executable classical decoder remain separate work. The 855-wire sampling and
reset/repetition connection is covered by the contracts above.

The earlier Fermat/checkpoint implementation remains separate under the adopted
Naive/paper isolation; it is not imported into this EEA submission. Completed
square, adaptive-foundation, block-relocation and corrected-contract prototypes
are already integrated in their production modules. Historical prototype notes
are not evidence that an implementation connection is still missing.
