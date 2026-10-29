# Five-word exceptional correction and window assembly

The fixed exceptional-correction schedule retains four source words and reuses
one target word. Its seven target lifetimes are 3, 2, 1, 0, 1, 2, 3. The first
query also loads the sources; the last query unloads them after restoration.
There are fourteen 15-bit unary QROM queries and sixteen transpositions.
No endpoint-dependent branch, callback, or submitted classical computation is used.

`batchModel_data` and `batchModel_clean` prove the register-level schedule has
the original finite matching result and restores all five work words. These
model the same `batchSchedule` used by `batchOps`. `batchedEndpointProgram_run`
binds the protected straight program to its actual adaptive query/transposition
sequence. `placedBatchProgram_count` proves exactly 458,738 measurement records
per correction block, independent of constants and outcomes.

The physical placement uses words 1024–3588, the flag at 4102, and 511 auxiliary
wires at 4103–4613. The component data row is exchanged by a wire permutation
with the original accumulator at 263–518, 580–835, and 838; this adds no gates.
The final address-bank permutation moves 839–854 to 855–870.

`actualBatchedWindow` surrounds the correction by sign-controlled y negations,
follows the coordinate program, and wraps the body with signed-address
preparation and restoration. It contains neither outer Hadamards nor Fourier.
`actualFirstWindow` is a direct point lookup. `batchedOuterPlan` supplies one
first window, fifteen remaining left windows, thirteen right windows, and an
explicit 3,931-wire reset list to the existing outer implementation.

`shiftStraight` shifts every record reference by the same prefix length. Its
exact execution theorem proves the shifted program cannot inspect old records;
this provides fixed `OuterWindow.count` without expanding large arithmetic
compilers to prove cursor independence.

## Space and T tradeoff

The five-word T count and measurement count below are proved for the actual
correction block. The qubit-set bounds and eight-word comparison remain
analytical component estimates, **not complete resource certificates**.
They exclude coordinate arithmetic, sign processing, Fourier,
and reset. They use a conservative 855-wire original support set plus the
endpoint words and 512 comparator work wires. Wire-label maxima are not qubit
counts.

| Correction implementation | Qubit-set upper bound | T per correction | Measurements per correction |
|---|---:|---:|---:|
| Eight resident endpoint words | 5,471 | 1,031,954 | 65,534 |
| Four source words and one reused target | 3,932 | 3,784,382 | 458,738 |

The five-word schedule saves 1,539 wires. The T estimate uses 229,369 per unary
query and 573,216 for sixteen comparisons/transpositions. There are only 28
correction-bearing windows per round, not 29: the first is direct lookup.
Thus correction-only T estimates across 56 rounds are 1,618,103,872 and
5,933,910,976 respectively. They do not establish that the complete program
fits the official limits. In particular, the existing measurement bound is
an overall cap, not free headroom for these queries.

## Remaining obligations

`batchUnitary_schedule` now connects the actual classical gate sequence to
that register model: it proves the matching result, all five endpoint words
zero, path/scratch cleanliness, a zero flag, and preservation of the lower
address/control wires. `batchSource_coherent` proves the actual adaptive
query/transposition sequence coherently implements this same unitary sequence.
Both proofs compose over the submitted `batchSchedule`, without assuming a
successful classical execution as an external premise.

`batchUnitary_fullFrame` additionally restores every non-data wire.
`placedBatchSource_state` transports the coherent execution to the actual
accumulator ports, and `placedBatchState_finite` proves the finite-point result
on those ports. `placedBatchProgram_wellFormed` checks the submitted correction
template itself, including all conditional slots. `placedBatchSource_tCount`
proves exactly 3,784,382 T gates for that correction block.

Address relabeling and outer-loop semantic integration, physical validity of
the remaining window components, and complete support/resource bounds remain outstanding. The reset list
does not substitute for workspace restoration before reset. No final Streaming
certificate is claimed.

The accumulator encoding bridge now identifies the ordered 513 physical ports
with `pointLogicalWires` and the coordinate bit function with
`pointCoordinateWord`. `placedBatchState_pointWrite` therefore gives the complete
canonical point state and preserves every other wire, under the explicit batch
readiness and raw-coordinate input conditions. Its output is ready for the
existing arithmetic interfaces.

`windowYNegate_coherent` and `windowYNegateState_pointWrite` prove the actual
signed modular-negation component, including canonical output and external-wire
restoration. `fig14EncodedEquiv_negY` proves the coordinate permutation's
conjugacy under Y negation, and `signedCorrection_negY` obtains subtraction after
all exceptional corrections without assuming that conjugacy. The subsequent window composition proves readiness and selected-row consistency
through the entire signed window sequence.


`BatchedPointReady` now states the original arithmetic conditions together with
zero values on the five-word endpoint bank and the correction flag/scratch bank.
The coordinate stages and modular negation preserve this condition. The actual
QROM row agrees with the same address read by the coordinate stages.

`batchedWindowState_correct` proves full signed point addition for a nonzero
order-torsion public point, including exceptional inputs and every external wire.
`batchedWindowCore_coherent` binds the corresponding coherent execution to the
submitted four-stage Straight program for any existing record prefix. The
address preparation/unpreparation pair preserves the domain and cancels outside
the point update; `batchedWindowPrepared_coherent` binds that complete prepared
program as well. These proofs precede the address-bank relabeling and the outer
repeated-trial integration, which remain separate obligations.

### Actual window address and physical compiler bridges

`ActualWindow.lean` proves coherent execution of the instantiated submitted
window after the address bank is moved to wires 855–870. Its selected row is
`signedTableAddress 32768 (windowRawDigit 0 s)`; the point update restores every
other wire and preserves the workspace conditions needed by subsequent windows.
The actual first-window lookup has a separate coherent execution theorem for
arbitrary point-valued tables, including infinity. Only that first table mixes
G and Q; the following odd-multiple addition tables have nonzero rows under the
challenge's nonzero order-torsion public-point assumption.

`WindowPhysical.lean` proves well-formedness preservation for literal programs,
composition, table reindexing and deferred recorded corrections. It connects the
Gidney adder and comparator templates to their structural source well-formedness
proofs and establishes both actual modular-negation templates. This does not yet
establish well-formedness of the entire coordinate arithmetic program. Full outer
composition, support/resource bounds and the final Streaming certificate remain
outstanding.
