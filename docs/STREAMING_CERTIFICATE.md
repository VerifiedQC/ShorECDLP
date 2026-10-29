# Streaming certificate: scope, resources and success

The actual 56-round Streaming entry has an unconditional Lean certificate in
[PR551, commit `b46e3371587f2f947c833b665b2636a863b7d85f`][certificate].
This document describes that fixed development version. It does not change the
published challenge, approve a release, or claim that the certificate is already
on `main`. Source links below are pinned because this documentation can be
reviewed before the implementation is merged into `streaming-dev`.

## Certified object

Import `ShorECDLP.Submission.«2607_13816».Challenge.FinalCertificate` and open
`ShorECDLP.Paper2607_13816.ChallengeMigration`. The final declaration is:

```lean
streamingEntry_certificate_unconditional :
  Certificate officialLimits batchedOuterPlan.layout streamingEntry streamingBounds
```

It has no proof parameters. The entry is the fixed coefficient table and actual
56-round straight program; the layout is the same program's fixed record
positions, using `wrappedShift` with the original 256/208-bit decoder parameters.
For every nonzero public point `Q = d • G`, starting from the all-zero state, the
protected `verifiedCandidate` accepts with probability at least `99/100`.
`publicPoint_order` derives the required group-order fact from `Q = d • G`.
The candidate is checked against the public group relation by the protected
[contract][contract]; the certificate does not rely on a supplied decoder callback.

## Four resource quantities

The statements below refer to the same actual entry. Resource bounds hold for
**every public point Q**; the nonzero/public-key hypotheses belong to the success
statement. See [ResourceCertificate.lean][resources].

| Quantity | Certified value | Source theorem |
|---|---:|---|
| Distinct used qubits | **at most 3,932** | `streamingEntry_qubitCount` |
| Abstract T-model cost | **at most 806,028,979,896** | `streamingEntry_tModel` |
| Measurements / final record cursor | **exactly 48,194,018,992** | `streamingEntry_measurements`, `streamingEntry_finalCursor` |
| Fixed syntax gate slots | **at most 5,000,000,000,000** | `streamingEntry_gateSlots` |

These have different meanings:

- **Qubits** count the deduplicated set of wires used by the interpreted program,
  not its maximum wire label and not a sum over 56 rounds. The support proof uses
  `completeBatchedSupport = 837 :: batchedResetWires`; the reset list alone has
  3,931 entries and omits a genuinely used wire, 837. The extra wire is restored
  by the round-boundary proof. `actualCompiledRound_zero_branch` establishes
  return to the all-zero state, up to a branch scalar, including this wire.
  The value 3,932 is an upper bound, not an exact usage assertion.
- **T-model cost** uses the repository's [abstract primitive costs][cost-model]:
  X/H/CX cost zero, CCX costs seven, and each phase-rotation primitive costs one.
  It is not a fault-tolerant synthesis estimate at a specified rotation error.
  `batchedOuterPlan_total_t_uniform` in [UniformT.lean][uniform-t] removes the
  earlier unnecessary group-order premise from this resource bound.
- **Measurements** include arithmetic, query and Fourier measurements and each
  round's full reset. [WindowCounts.lean][counts] proves the exact per-round
  cursor increment `860,607,482`, then
  `batchedOuterPlan_finalCursor` proves `56 × 860,607,482 = 48,194,018,992`.
- **Gate slots** bound the fixed program's syntax, including record-controlled
  correction slots and conditional slots even when their condition is false.
  `batchedOuterPlan_slots` in [WindowSlots.lean][slots] composes conservative
  bounds rather than expanding the entire gate list. Slots are an admission
  bound, not an exact executed-gate count or the T score.

The certificate also proves well-formedness and the table/candidate admission
checks: 983,040 coefficient rows and at most `56 × (2^49 + 2)` candidate checks.
`officialLimits` has no qubit or T cap; those quantities are the entry's certified
resource bounds. The gate-slot cap is `4,000,000,000,000,000`.

## Why the success probability is at least 99 percent

The [final assembly][certificate] combines the following exact interfaces:

1. `actualRoundSource_fixedPair_mass` in [ActualPair.lean][pair] connects the
   actual round's selected measurement histories to its two-axis model, with
   the original final X gate and reset included.
2. `selectedIdealTwoAxes_event_eq` in [IdealDistribution.lean][distribution]
   identifies that event's probability with
   `reducedRawIdealFourierEventMass G Q` for **any** Boolean acceptance function.
   The proof retains coherent amplitudes, signed-window ordering, feedback
   phases and the evaluator's least-significant-bit-first word convention.
   This equality has no exceptional-case loss term or unproved layout premise.
3. `wrappedIdeal_mass_lower` in [DecoderBridge.lean][decoder] proves that the
   protected wrapped-shift acceptance event has ideal mass at least `163/1000`.
   Together these give `streamingRound_success` for the actual single round.
4. [RoundReset.lean][reset] proves every actual round branch returns to zero up
   to a scalar and that total round mass is one. [RepeatEvent.lean][repeat]
   proves `actualCompiledRepeat_verified_mass`: the final protected decoder's
   acceptance probability is exactly `1 - (1 - p)^56`, where `p` is the actual
   single-round accepted mass. Its “at least one accepted trial” event agrees
   with the evaluator returning the first candidate that passes its group check.
   Independence is derived from the actual reset-and-repeat execution, not
   assumed for an abstract list of trials.
5. `actualRoundAcceptedMass_le_one` supplies `p ≤ 1`. Monotonicity and a Lean
   `norm_num` proof of
   `99/100 ≤ 1 - (1 - 163/1000)^56` give `streamingEntry_success`.
   `streamingEntry_certificate_unconditional` fills the resource shell with
   this result.

**0.163 is a lower bound supplied by this proof route**, not a measured success
rate or a claim that the actual probability equals 0.163. Likewise, an earlier
0.08 bound and this 0.163 bound are bounds from different proof routes; comparing
them does not show that an implementation's actual probability increased.
The expression `1 - (1 - 0.163)^56` is approximately `0.999952942847`, while the
protected certificate promises the proved threshold `≥ 0.99`.

## Five-word correction: space versus T cost

Each exceptional endpoint word has 513 bits. The selected implementation keeps
four source endpoints resident and reuses one target slot in the order
`3 → 2 → 1 → 0 → 1 → 2 → 3`. Each of the seven stages loads and unloads its target;
the first/last query also loads/unloads the sources. This produces fourteen
15-bit-address QROM queries and sixteen transpositions. QROM selection is charged:
a constant table does not make quantum-address selection free.

The alternative loads all eight endpoint words together, using two queries and
the same sixteen transpositions. The comparison below is **for the exceptional
correction block**, excluding coordinate arithmetic, sign handling, Fourier and
reset. The eight-word column is an analytical alternative, not a second
whole-entry certificate.

| Correction design | Conservative wire-set bound | QROM queries | T-model cost per block | Measurements per block |
|---|---:|---:|---:|---:|
| Eight resident endpoint words | 5,471 | 2 | 1,031,954 | 65,534 |
| Four source words + one reused target | 3,932 | 14 | 3,784,382 | 458,738 |

The wire-set calculation is `855 + (words × 513) + 512`, where the final 512
comprises 511 comparison ancillas and one flag. Reuse saves 1,539 wires, about
28.1% of this conservative allocation, at about 3.67 times the correction block's
T cost. Retaining only one endpoint pair would require a new recomputation
schedule: intermediate steps modify source endpoints that later steps still
need. It is not justified by simply counting a few extra loads.

The actual five-word counts have source proofs:
[`batchSchedule_queries` and `batchedEndpointProgram_count`][batch] establish the
query/record accounting; `placedBatchProgram_count` in [BatchPlacement.lean][placed]
fixes 458,738 records. [BatchCost.lean][batch-cost] proves
`batchSchedule_cost = 98 × nodes + 573,216` and
`placedBatchSource_tCount = 3,784,382`. A 15-bit tree has 32,767 internal nodes:
each query costs `7 × 32,767 = 229,369` T units and 32,767 measurements; sixteen
transpositions cost `16 × 35,826 = 573,216` T units.

There are **28 correction-bearing windows per round**, not 29: the first window
is a direct point lookup, followed by fifteen left and thirteen right addition
windows. Across `28 × 56 = 1,568` correction blocks, the two T subtotals are
1,618,103,872 and 5,933,910,976, a difference of 4,315,807,104. These are correction
subtotals, not alternative total-program resource certificates. The adopted
five-word design's complete resources are the four certified quantities above.

## Frozen limit and development acceptance

The published frozen main commit is
`51cabe2575fdef2713e14dbaa1ba93cb4a51cc41`. Its measurement cap is
**47,471,340,504**, below the actual entry's **48,194,018,992** records by
**722,678,488**. The original cap is a total limit, not spare capacity for
additional correction queries. The proof cannot certify `recordBudget` against
that smaller cap.

The [development Official.lean][official] inherited from PR518 sets the cap to
**50,000,000,000**, leaving **1,805,981,008** records of headroom. Among protected
`Challenge`, `Judge`, `Framework`, `Math` sources and runner code, this
`Official.lean` change is the only difference between the frozen version and
PR551's fixed head. The certificate and judge acceptance described here use that
explicit development cap. Changing the published limit and merging/releasing the
implementation still require the owner's decision; this document does neither.

## Validation and reproduction evidence

[Full verification of the fixed certificate head][verification] passed: 3,693
build jobs, 699 source files, 6,383 exact axiom disclosures and 35,174 declarations
within the `propext`, `Classical.choice`, `Quot.sound` allowlist, plus evaluator
regressions and independent kernel replay.

The [actual Entrant judge report][judge-report] includes JSON and a reproduction
script. It uses independently built trusted sources from frozen main plus only
the PR518 `Official.lean` change, separate from the submitted proof artifacts.
Independent replay and the protected Expr-level checks accepted both `resources`
and `success`. The latter is the universally quantified probability theorem,
not an empirical trial result. Older incremental handoff documents describe
intermediate obligations; the pinned final declaration above is the completed
certificate interface.

[certificate]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/FinalCertificate.lean
[contract]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Challenge/Contract.lean
[resources]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/ResourceCertificate.lean
[cost-model]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Framework/CostModel.lean
[uniform-t]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/UniformT.lean
[counts]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/WindowCounts.lean
[slots]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/WindowSlots.lean
[pair]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/ActualPair.lean
[distribution]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/IdealDistribution.lean
[decoder]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/DecoderBridge.lean
[reset]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/RoundReset.lean
[repeat]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/RepeatEvent.lean
[batch]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/BatchedEndpoint.lean
[placed]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/BatchPlacement.lean
[batch-cost]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Submission/2607_13816/Challenge/BatchCost.lean
[official]: https://github.com/VerifiedQC/ShorECDLP/blob/b46e3371587f2f947c833b665b2636a863b7d85f/ShorECDLP/Challenge/Official.lean
[verification]: https://github.com/VerifiedQC/ShorECDLP/pull/551#issuecomment-6479465529
[judge-report]: https://github.com/VerifiedQC/ShorECDLP/pull/551#issuecomment-6478851588
