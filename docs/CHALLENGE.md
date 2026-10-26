# Challenge: a verified quantum circuit for ECDLP on secp256k1

Tracker: #462. Licensed under Apache 2.0 (see `LICENSE`, `NOTICE`).

## Task

Give a quantum circuit that, for every public point `Q = d • G ≠ 0` on secp256k1,
recovers `d` with probability at least 99 % from the all-zero state. The circuit and its
proof are checked by Lean 4; the protected judge computes the metrics.

## What you submit

Edit only `ShorECDLP/Submission/Entrant/`. In namespace `ShorECDLP.Entrant` define:

| Name | Type |
|---|---|
| `entry` | `ShorECDLP.Challenge.StraightEntry` |
| `layout` | `ShorECDLP.Challenge.DecodeLayout` |
| `bounds` | `ShorECDLP.Challenge.Bounds` |
| `certificate` | `ShorECDLP.Challenge.Certificate officialLimits layout entry bounds` |

The shipped `Entrant/Main.lean` is the Naive baseline and is a complete working example.

A submission is **data that does not depend on `Q`**:

1. **Coefficient table** `[(a₀, b₀), …]`. The judge computes `Pᵢ = aᵢ • G + bᵢ • Q` and exposes
   the fields `x`, `y`, `infinity`, `−x`, `−y`, `3x` (mod p).
2. **Straight-line program** over `X`, `H`, `CX`, `CCX`, `P(dir, k)` and X-basis measure-and-reset.
   A gate may be optional only by being switched by one bit of one constant field (`whenBit`)
   or by one earlier measurement bit (`recordGate`). No branching, jumps or program generation.
3. **Decoder layout**: fixed record positions plus a protected decoder kind and parameters.
   The judge parses the record, generates candidates with its own algorithm and accepts the first
   `c` with `c • G = Q`.
   - `wrappedShift`: at most `2·(n / 2^rightBits + 2)` candidates per trial (2607.13816 baseline).
   - `nearestPair`: rounds both samples to nearest numerators; at most 1 candidate per trial (Naive).
4. **A Lean proof** of the protected `Certificate`: organizer limits, well-formedness, resource
   bounds for every `Q`, and success ≥ 99 % through the protected `verifiedCandidate`.

You cannot supply any function of `Q`, of constant values or of the measurement record: in Lean
such a function could compute `d` classically at no counted cost.

## Organizer limits (`ShorECDLP/Challenge/Official.lean`, protected)

| Limit | Value |
|---|---|
| Candidate checks (whole program) | `56·(2^49+2)` ≈ 2^55 |
| Gate slots (including untriggered optional slots) | 4·10^15 (provisional) |
| Measurements | 47,471,340,504 (provisional) |
| Coefficient rows | 983,040 |

## Metrics

All metrics are recorded. The judge prints the declared, proved bounds of the whole program
(all repetitions summed), worst case over measurement outcomes and over `Q`.

| Metric | Notes |
|---|---|
| T-model count | `CCX` = 7, every `P` = 1 (including k = 1, 2: write Z as H·X·H) |
| Logical qubits | distinct wires |
| Measurements | records written |
| Gate slots, coefficient rows, candidate checks | admission limits above |
| Toffoli and non-Clifford counts | to be added as proved bounds |

Cost-model limits: each rotation costs 1 regardless of angle; rotation synthesis and its error
are not modelled. Scores are formal results in this abstract cost model, not hardware estimates.

## Rules

- Locked: everything outside `ShorECDLP/Submission/Entrant/` (toolchain, lakefile, manifest,
  `scripts/`, Framework, Math, Challenge, Judge, baselines).
- The acceptance theorem `ShorECDLP.Judge.check_certificate` may depend only on `propext`,
  `Classical.choice` and `Quot.sound`. `sorry`, new axioms and `debug.skipKernelTC` are rejected;
  compiled modules are replayed by the kernel (`leanchecker`).

## Baselines

| Submission | Qubits | T-model | Measurements | Status |
|---|---|---|---|---|
| Naive | 206,624 | 8,918,039,383,771,648 | 5,385,536 | certified through the judge |
| arXiv:2607.13816 streaming | ≤ 854 (paper claim) | | ≤ 47,471,340,504 | migration in progress |

## Running the judge

```sh
CANDIDATE=/worker/source TRUSTED_REPO=/trusted/repository TRUSTED_TREE=<full tree hash> \
  /trusted/repository/scripts/benchmark.sh
```

It checks the editable boundary (`docs/CHALLENGE_EDITABLE_BOUNDARY.md`) before any build cache is
restored, runs `scripts/verify.sh`, replays the entrant and judge, and prints a JSON line with the
metrics. Locally, `lake build ShorECDLP.Judge.Main` checks the acceptance theorem.
