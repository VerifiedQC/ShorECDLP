# Streaming certificate handoff

This increment prepares the 2607 migration interface. It does **not** certify the
unfinished migrated program or reproduce the old paper resource counts.

## Producer exports

Planned final module:
`ShorECDLP.Submission.«2607_13816».Challenge.StreamingCertificate`.
Namespace: `ShorECDLP.Paper2607_13816.ChallengeMigration`.

- `streamingEntry : Challenge.StraightEntry`
- `streamingDecodeLayout : Challenge.DecodeLayout`
- `streamingBounds : Challenge.Bounds`
- `streamingCertificate : Challenge.Certificate Challenge.officialLimits
  streamingDecodeLayout streamingEntry streamingBounds`

The entry, decoder positions and resource bounds must describe the **same actual
migrated circuit**. Fixed-shape exceptional-point handling can add gates, workspace
and measurements. Execution equality alone does not transfer support, T counts,
measurement counts or syntax-slot counts. No current statement assigns 854 wires
or the legacy T count to the migrated entry.

`CertificateAssembly.lean` supplies `StreamingAssembly.certificate`. Its input
requires physical well-formedness, uniform resource bounds and the actual
protected decoder's 99% success event. Syntax slots, final record cursor and table
length are checked separately against organizer limits. These are explicit
parameters, not admitted proofs or an asserted producer instance.

## Independent candidate result

`streaming_candidate_budget` and `streaming_candidates_length` apply to every
wrappedShift layout with 256/208 bits and at most 56 trials, regardless of the
chosen record indices. They prove the bound `budget55 = 56 * (2^49 + 2)` using the
protected decoder. They do not prove that those indices select Fourier outputs.
The actual correspondence remains a producer obligation.

## Acceptance adapter

After building the final producer module, run:

```
python3 scripts/challenge/streaming_acceptance.py
```

This compiles a fresh Entrant in a temporary trusted overlay, independently
replays its kernel declarations and invokes the unchanged protected judge. It
reports the judge's actual values and does not assert legacy numeric constants.
Until the producer module exists it fails; no fallback is permitted.

`--self-test-naive` runs the same adapter on the shipped Naive example. Passing
that test verifies the adapter only, **not Streaming acceptance**. This organizer
script does not replace the production isolation or artifact-boundary workflow.
