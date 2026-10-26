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
| Toffoli and non-Clifford counts | derived upper bounds via `Certificate.extend`; optionally tighter proved `ExtendedCertificate` |

Cost-model limits: each rotation costs 1 regardless of angle; rotation synthesis and its error
are not modelled. Scores are formal results in this abstract cost model, not hardware estimates.

## Rules

- Locked: everything outside `ShorECDLP/Submission/Entrant/` (toolchain, lakefile, manifest,
  `scripts/`, Framework, Math, Challenge, Judge, baselines).
- The submitted certificate and its data may depend only on `propext`,
  `Classical.choice` and `Quot.sound`. `sorry`, new axioms and `debug.skipKernelTC` are rejected;
  entrant compiled modules are replayed against trusted dependencies by the kernel (`leanchecker`).
- The trusted judge constructs the required `Judge.acceptance entry layout bounds` expression
  directly and checks its type with the kernel. It never elaborates acceptance syntax after
  importing entrant macros. Metrics are kernel-reduced; `#eval` and native replacements are not used.

## Baselines

| Submission | Qubits | T-model | Measurements | Status |
|---|---|---|---|---|
| Naive | 206,624 | 8,918,039,383,771,648 | 5,385,536 | certified through the judge |
| arXiv:2607.13816 streaming | ≤ 854 (paper claim) | | ≤ 47,471,340,504 | migration in progress |

## Running the judge

```sh
CANDIDATE=/worker/source TRUSTED_REPO=/trusted/repository TRUSTED_TREE=<full tree hash> \
  CANDIDATE_BUILDER=/runner/isolated-build \
  /trusted/repository/scripts/benchmark.sh
```

### Source boundary

It checks the editable boundary (`docs/CHALLENGE_EDITABLE_BOUNDARY.md`) before any build cache is
restored. The evaluator-owned `CANDIDATE_BUILDER` adapter receives the candidate root,
trusted root and protected verification-script path as separate arguments. It must restore
trusted dependencies, run verification with `SHORECDLP_ROOT` set to the candidate, and terminate
all worker processes before returning a frozen build output. The trusted repository must be
read-only to that worker. The adapter is deployment-specific and is not provided by this repo;
this script alone is not a sandbox.

### Build-artifact boundary

The controller copies trusted dependency artifacts and replaces only the Entrant subtree from
the stopped worker. It rejects symlinks in worker artifact paths. It then independently replays
that snapshot, imports declarations without loading entrant extensions, performs the kernel
acceptance check and reports JSON metrics. Candidate-produced protected artifacts are ignored.
The trusted dependency artifacts must be built and validated from the pinned `TRUSTED_TREE`
and pinned toolchain before serving submissions; an arbitrary pre-existing build cache is not
a trusted dependency set. The controller's environment, toolchain, trusted artifacts and snapshot must remain inaccessible
to candidate processes throughout this phase.

For the shipped, trusted example only, after building the root library:

```sh
lake env lean --run scripts/challenge/judge.lean
```

`lake build ShorECDLP.Judge.Main` alone does **not** admit a submission; that module contains
only protected predicates. The standalone controller performs admission.

Optional tighter diagnostics use `ShorECDLP.Entrant.extendedBounds : ExtendedBounds` and
`extendedCertificate : ExtendedCertificate officialLimits layout entry bounds extendedBounds`.
Both must be present and pass the same syntax-free kernel type and axiom checks. Otherwise the
judge derives Toffoli ≤ T-model/7 and non-Clifford ≤ the official gate-slot limit. JSON names
explicitly distinguish these derived upper bounds and organizer limits from exact counts.
