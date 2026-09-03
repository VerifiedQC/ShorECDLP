# ShorECDLP implementation plan

ShorECDLP is an ecdsa.fail-style Lean verification repository for quantum resource-estimate
submissions against secp256k1. It currently contains one complete, deliberately naive construction.
The next construction will implement the space-efficient algorithm from
[arXiv:2607.13816v2](https://arxiv.org/html/2607.13816v2) as an independent submission.

**Status snapshot.** The verified Naive result and merged Phase-0--5 unit-1 paper foundation below
are on `main@d1f94940917b1134571ca0006683b8b2b5633b57`. PR #56 → PR #57 → PR #58 → PR #59
→ PR #60 → PR #61 → PR #62 landed the source split, adaptive Kraus semantics,
coherent-refinement bridge, measurement-based uncomputation, pure EEA model, indexed EEA
bounds/windows, and the first concrete circuit unit; Phase 5 circuit unit 2 is the current
implementation/review unit. A `✓` means a
declaration is root-reachable and covered by the repository verifier on the stated baseline or
exact review head. “Target” is not a proved claim.

## 1. Current verified result

The current construction is a closed Bitcoin ECDLP submission, not merely an arithmetic library.
For every nonzero public key `Q = d • G`, `bitcoinECDLPSubmission` connects one concrete circuit
family to all of these checked fields:

| Property | Verified value |
|---|---:|
| exponent precision | two 256-bit registers |
| encoded affine point | 513 bits |
| one-run success lower bound | `41 / 250` |
| independent runs for at least 99% success | 26 |
| T count per run | `841,862,539,761,920` |
| T count for 26 sequential runs | `21,888,426,033,809,920` |
| static qubit-capacity upper bound per run | `1,394,478` |

The qubit value is an honest dense-allocation upper bound, not a claim that every label is used.
The 26 runs are sequential and reuse the same physical wires.

The proof chain is complete and standard-axiom-only:

- secp256k1 field and group certificates, including primality and `addOrderOf G = order`;
- primitive-gate classical and finite-support quantum semantics;
- reversible modular add/subtract/multiply/exponentiate and Fermat inversion;
- a total affine group-law specification and clean controlled point addition;
- binary doubling-table scalar multiplication and a two-call ECDLP oracle;
- coherent QFT/IQFT and two-dimensional order finding;
- exact oracle refinement, concrete end-to-end correctness, resource aggregation, and repetition;
- a nullary `BitcoinECDLPSubmission` record with correctness, T-count, qubit, and trial fields.

This construction will be called the **Naive** submission after the source split. “Naive” describes
its arithmetic and allocation strategy, not its proof status.

## 2. Source architecture

The adopted architecture contains two isolated implementations over one small semantic framework
and one pure mathematical layer:

```text
ShorECDLP/
  Math/                       # pure definitions and lemmas; transitively Mathlib-only
  Framework/                  # implementation-neutral classical/quantum machine semantics
  Submission/
    Naive/                    # the entire current construction
    2607_13816/               # arXiv:2607.13816v2 construction
```

The requested numeric directory is valid. Lean imports its module component with escaped syntax:

```lean
import ShorECDLP.Submission.«2607_13816».EEA.Model
```

New paper declarations use the readable namespace `ShorECDLP.Paper2607_13816`.

### 2.1 Import rules

The verifier will enforce this dependency policy using both textual import checks and Lean
`--src-deps` output:

- `Math/**` imports only Mathlib or other `Math/**` modules. Its transitive in-repository source
  closure contains no Framework or Submission path.
- `Framework/**` imports Mathlib, Math, or Framework, never either submission.
- `Submission/Naive/**` may import Mathlib, Math, Framework, and Naive, never `2607_13816`.
- `Submission/2607_13816/**` may import Mathlib, Math, Framework, and `2607_13816`, never Naive.
- Only the root/verification sentinel imports both submissions.

Thus no arithmetic circuit, QFT implementation, oracle contract, resource formula, or correctness
theorem is shared between the two submissions. Shared problem-specific material must be genuinely
pure mathematics. Generic notions such as primitive gates, basis states, linear semantics, Born
mass, and adaptive sequencing remain in Framework.

### 2.2 What belongs in `Math/`

Candidates include:

- the secp256k1 constants, curve, affine point type, and generator;
- primality and generator-order certificates;
- the mathematical total affine group law and field identities;
- pure ECDLP hidden-subgroup, rounding, recovery, and postprocessing lemmas;
- generic doubling-table and scalar identities; and
- pure independent-repetition probability lemmas.

A declaration moves only if its complete proof dependency closure is Mathlib/Math. Circuit types,
register encodings, quantum states, oracle specifications, phase-estimation programs, and resource
models are not pure mathematics.

### 2.3 Phase-0 relocation policy

The first implementation PR is a structural move:

1. audit current Framework and Submission declarations;
2. extract eligible pure declarations into Math;
3. move all remaining current algorithm modules under `Submission/Naive/`;
4. move the Bitcoin-specific unitary submission contract out of Framework and into Naive;
5. add the four import-direction gates above; and
6. make both submissions root-reachable without permitting cross-imports.

The recommended first move preserves current public declaration names. Parent/head `#print` and
`#print axioms` output must agree for every public declaration, apart from unavoidable qualified
source names. Renaming the whole existing API into `ShorECDLP.Naive` would be a separate
source-breaking migration and requires an explicit decision.

## 3. Semantic and resource boundaries

### 3.1 Unitary programs remain unitary

The current trusted program surface is:

```lean
Gate       := X | H | CX | CCX | P direction angle wire
Circuit    := List Gate
Quantum.run : Circuit -> State ->ₗ[ℂ] State
```

`Circuit.adjoint` and the inner-product theorems rely on every gate being unitary. Mid-circuit
measurement will therefore not be added as another `Gate`.

### 3.2 Adaptive programs use instruments

The paper path needs X-basis measurement, reset, wire reuse, and classical feed-forward. An
`AdaptiveCircuit` will alternate existing unitary Circuit blocks with measurement/reset nodes and
classical continuations. Its denotation is a finite list of unnormalized Kraus branches. A branch's
squared norm is its Born mass; summing all branches is trace preserving.

The critical integration relation is coherent, not merely pointwise classical correctness:

```text
for each transcript h, there is a coefficient c_h such that
K_h |s> = c_h U |s> for every valid basis state s,
and sum_h |c_h|^2 = 1.
```

`c_h` may depend on the internal measurement transcript but not on the input. By linearity, every
valid superposition is preserved up to the same branch coefficient, and final Born probabilities
agree with the ideal program after summing internal transcripts. This is required because Shor's
oracle is evaluated on a superposition.

### 3.3 Do not conflate T and Toffoli metrics

The Naive submission's existing `tCount` assigns 7 T gates to `CCX` and 1 T gate to each dyadic
phase rotation. The paper reports Toffoli and CNOT counts and uses measurement-assisted
uncomputation. The paper submission therefore gets a separate compositional resource vector with
at least:

```text
X, H, CNOT, Toffoli, dyadic phase, X-measure/reset,
classically controlled correction, table lookup, and maximum live qubits.
```

Sequential counts add; adaptive branches use a proved worst case unless a more precise statistic is
explicit. A conversion to a fault-tolerant T count is a separate theorem with a stated synthesis
model. No paper Toffoli number is copied into the existing T-count field.

## 4. The two submissions

### 4.1 Naive submission ✓

The current algorithm uses two 256-bit exponent registers, a 513-bit affine-point accumulator,
Fermat inversion, binary controlled double-and-add, and two coherent inverse QFTs. Its oracle is

```text
(a, b, R) |-> (a, b, R + a•G + b•Q).
```

Every arithmetic circuit restores its workspace. The oracle's whole-state equation preserves the
exponent registers and every outside wire, refines to the unitary oracle specification, and feeds
the proved Fourier-sampling/postprocessing theorem. This entire chain moves to
`Submission/Naive/`; it is not imported by the paper implementation.

### 4.2 arXiv:2607.13816v2 target

Pinned sources:

- paper: arXiv HTML v2, `2607.13816v2`;
- supplemental generator:
  [`ZeroWang030221/Space-Efficient-Quantum-Algorithm-for-Elliptic-Curve-Discrete-Logarithms-with-Resource-Estimation`](https://github.com/ZeroWang030221/Space-Efficient-Quantum-Algorithm-for-Elliptic-Curve-Discrete-Logarithms-with-Resource-Estimation/tree/e64aa3c1198d96aeb389e64bc7ae48edbb9712ec),
  commit `e64aa3c1198d96aeb389e64bc7ae48edbb9712ec`.

The supplement is a differential-test oracle, not a trusted proof source. At that pin it contains
detailed EEA and point-addition generators, but no complete signed-window plus semiclassical-QFT
implementation.

The paper path consists of:

1. fixed-step, register-sharing reversible EEA inversion;
2. step-dependent active windows and location-controlled arithmetic;
3. measurement-assisted uncomputation with input-independent phase correction;
4. three-register in-place division, multiplication, and total affine point addition;
5. semiclassical Fourier sampling;
6. signed-window double-scalar multiplication with five sequential table lookups; and
7. one adaptive end-to-end correctness and resource contract.

## 5. Completion criteria

A paper phase is complete only when all applicable conditions hold for the same executable term:

- the program is constructed from primitive unitary gates and the separately defined adaptive
  measure/reset operation; no trusted arithmetic or point-add gate is added;
- a direct theorem states the input/output map before any contract packages it;
- input registers are preserved, clean work is restored, borrowed qubits are restored for arbitrary
  initial values, and measured wires are proved reset before reuse;
- each adaptive branch has an input-independent coefficient times the ideal operation;
- well-formedness, disjointness, locality, and all clean/borrowed preconditions are explicit;
- exact resource formulas follow constructors by induction rather than expanding a multi-million-
  gate secp256k1 list;
- the fixed `n = 256` program is certified before optional generic asymptotics;
- no `sorry`, `admit`, `native_decide`, custom axiom, or trusted counting macro is used; and
- root closure, warning-fatal build, targeted and exhaustive axiom audits, hosted CI, and exact-head
  independent review pass.

## 6. Dependency-ordered roadmap

### Phase 0 — source split and specification reconciliation (merged)

Perform the relocation in Section 2.3 without changing current program or theorem meaning. Record
the exact paper schedule/layout, pin small differential tests, freeze the resource vocabulary, and
quarantine the unresolved paper claims in Section 7.

**Gate:** parent/head public declarations and axioms agree; Math, Framework, Naive, and
`2607_13816` import checks pass; both submissions are root-reachable.

**Status:** PR #56 merged the path-only relocation and paper-reference reconciliation. All 55
relocated code-bearing modules preserve their declaration/proof source modulo imports and comments;
the 8 retained Framework modules complete the 63-module baseline, and all 1,801 public declarations
have identical parent/head printed signatures and axiom dependencies. The warning-
fatal build, 67/67 source closure, four textual/compiler-resolved import-direction gates, 103
targeted disclosures, exhaustive 5,236-declaration standard-only audit, and hosted CI are green.

### Phase 1 — adaptive semantics and coherent refinement (merged)

Modules:

- `Framework/Quantum/Adaptive.lean`
- `Framework/Quantum/CoherentRefinement.lean`

Define X-basis projection/reset Kraus maps, adaptive sequencing, branch histories, Born mass,
well-formedness, and separate resources. Prove the exact basis-ket rule, reset cleanliness, total
Born-mass preservation, coherent composition, extension to supported superpositions, and final
probability equivalence.

**Gate:** coherent refinement—not basis-only behavior—composes across all later arithmetic.

**Status:** PR #57 added the separate adaptive Kraus-instrument semantics and PR #58 added
coefficient-aligned coherent refinement. The proved surface includes exact X-reset behavior and
cleanliness, arbitrary-state Born-mass preservation, chronological sequencing without transcript
deduplication, extension from valid basis inputs to supported superpositions, coherent
unitary/sequential composition, and equality of arbitrary final computational-basis event
probabilities after summing internal transcripts. Exact local and hosted gates are green (3,058 /
3,059 warning-fatal jobs, 68/69 source files, 109/120 disclosures, and 5,344/5,396 exhaustively
audited declarations with only the standard axiom allowlist).

### Phase 2 — measurement-based uncomputation

Modules:

- `Framework/Quantum/MeasurementUncompute.lean`
- `Submission/2607_13816/Canary/AdaptiveCPhase.lean`

Lift X measurement to an `m`-bit register. Before correction, transcript `b` and old value `y`
produce coefficient `2^(-m/2) (-1)^(b·y)`. Prove a generic recompute/Z-correct/uncompute theorem
whose final coefficient depends only on `b`. Validate it on a computed-AND/controlled-phase canary
and derive its measurement and Toffoli counts.

**Gate:** phase cancellation, reset, and resource claims are exact; the canary does not modify the
Naive QFT.

**Status:** PR #59 implements this phase. The framework now enumerates chronological
false-first register transcripts, proves the exact `2^(-m/2) (-1)^(b·y)` branch coefficient,
clears every measured wire, and proves coherent correction both from an abstract selected circuit
and from the concrete recompute/Z-correct/uncompute construction. The isolated paper canary uses a
direct Clifford controlled-Z correction: it coherently implements the local unitary reference with
one measurement, one rather than two Toffolis, naive T-count 8 rather than 15, and three wires. It
imports no Naive module and leaves the production Naive QFT unchanged. The local exact-tree gate is
green: 3,061 warning-fatal jobs, 71/71 source closure, 144 targeted disclosures, and all 5,617
reachable declarations within the standard axiom allowlist.

### Phase 3 — pure four-phase EEA model

Module: `Submission/2607_13816/EEA/Model.lean`.

Define the paper's remainder/coefficient recurrence, quotient bits, four phases, sign, iteration
parity, lengths, and circular shift. Relate it to packed Work1 `(t,q,r)` and shifted Work2
`(t',r')`. At canonical quotient boundaries, prove ordered in-range spans, actual value capacity,
and field non-overlap. Prove the `x > p/2` correction, invariant preservation, an active-step left
inverse, terminal inverse, and quotient-level terminal stuttering.

**Gate:** for every `1 <= x < p`, the extracted value is `x⁻¹ mod p`; small tests agree with the
pinned generator but are not used as proofs.

**Status:** the pure model is implemented. `paperStep` is explicitly one complete Euclidean
quotient iteration; `paperPhaseTrace` exposes the four logical frames, while Phase 4 retains
ownership of the 1,620-step bit-serial schedule and active windows. The state records quotient
bits, sign/parity, dynamic lengths, circular shift, and the logical values sharing each `(n+3)`-bit
work register. The proved invariant gives packed-field non-overlap, strict remainder/coefficient
progress, `r*t + r'*t' = p`, coprimality, and the two parity-dependent `ZMod p` identities. Its
packing theorem is boundary-only and additionally proves that every stored value fits its ordered,
in-range span. Initialization proves the `x > p/2` correction; each active nonterminal step
preserves the invariant and has a constructive left inverse; the terminating run reaches
`(r,r',t) = (1,0,p)`; its extracted coefficient multiplies every `1 <= x < p` to one modulo prime
`p`; and every post-terminal quotient-level slot stutters. This total stuttering abstraction is
not injective across the final active/terminal boundary. Phase 4/5 explicitly own intermediate
frame representability, indexed reachability, and the paper's borrowed padding epoch before any
reversible fixed-horizon circuit refinement is claimed. Kernel-reduced checks match all three
terminal vectors pinned in `REFERENCE.md`.
The exact local gate is green: 3,063 warning-fatal jobs, 72/72 source closure, 151 targeted
disclosures, and all 5,941 reachable declarations within the standard axiom allowlist.

### Phase 4 — exact step bound and active windows

Modules:

- `Submission/2607_13816/EEA/Bounds.lean`
- `Submission/2607_13816/EEA/Windows.lean`

Certify the 1,620-step secp256k1 schedule without trusting floating point. Use an exact rational
certificate for the algebraic growth bound, then prove every reachable location lies within the
paper's static window at each step. Define the indexed active/padding discriminator, prove the
noncanonical phase-frame values fit their physical spans when reached, and account for the paper's
borrowed epoch bit so terminal padding is a reversible identity at the exposed EEA boundary.

**Gate:** all nonzero 256-bit field inputs terminate in 1,620 steps and every pruned gate location
is proved unreachable.

**Status:** merged via PR #61. An exact four-row rational potential
certificate proves quotient-bit weight at most 405, hence at most 1,620 microsteps, uniformly over
every `1 <= x < p`; no floating-point evaluation or input enumeration appears in the theorem.
Every positive schedule index has a reachable active-or-padding witness. Padding is a multiple of
four, is at most 596 steps for secp256k1, and carries an explicit borrowed epoch/low-word pair whose
endpoint compression is involutive and clears the exposed epoch bit. All four noncanonical logical
phase frames prove actual-value capacity and field non-overlap in the two packed work registers.

The window audit preserves the 1,620-row generator table as `activeWindows`, but does not transfer
its post-increment lower bound across an ordering mismatch: the analytic phase-two remainder lower
endpoint uses `l_q` after increment, while the supplemental circuit executes remainder arithmetic
before that increment.
The implementation boundary is therefore `certifiedActiveWindows`, which retains one additional
lower remainder lane and leaves the other four generator intervals unchanged. Kernel-checked
containment covers every active remainder interval, quotient/sign selector, coefficient prefix,
and both endpoint length decoders under the exact indexed reachability witness. The coefficient
certificate follows the concrete selector exactly: Phase 3 ends at `ell_t + 1`, while Phase 4 ends
at `n + 3 - ell_r' - ell_s`. Phase 5 must use the certified window; no resource theorem may claim
the narrower remainder interval.
The exact local gate is green: 3,065 warning-fatal jobs, 74/74 source closure, 167 targeted
disclosures, and all 6,449 reachable declarations within the standard axiom allowlist.

### Phase 5 — one EEA step as a circuit

Area: `Submission/2607_13816/EEA/`.

Implement circular shifts, unary iteration, location-controlled sign/quotient swap,
location-controlled ripple add/subtract, borrowed-work length updates, and the optimized four-phase
step. Each block gets direct semantics, unaffected-wire and work-restoration theorems,
well-formedness, locality, and a closed resource formula. Its refinement domain is the indexed
reachable active/padding state from Phase 4, including the borrowed epoch discriminator; it must not
claim that the unindexed stuttering `paperStep` is injective on every invariant boundary.

**Gate:** the adaptive step coherently implements the indexed Phase-3 transition on every reachable
active/padding state; counts are symbolic over the active window.

**Status:** the first dependency-closed construction unit is merged. It contains standalone exact
Fredkin and dirty-`C³X` decompositions, controlled circular shifts,
the supplement's controlled increment, reusable measurement-assisted path-AND erasure, and the
pruned measured unary iteration. Each exported block has basis-state semantics, restoration or
named-wire locality, physical well-formedness, and constructor-derived resource equations. The
unary traversal coherently refines its full compute/uncompute reference and uses exactly one
measurement and seven T gates per internal decision node. The next dependency-closed unit now
implements the pinned production path's clean-v-chain MAJ/UMA cells and prepared-slice two-pass
ripple core, plus a per-bit borrowed-work XOR normal form for the later length decoders. The ripple
has direct whole-basis-state semantics, clean-scratch restoration, named locality, physical
well-formedness, and the paper's exact seven-Toffoli / 49-T formula per lane. The borrowed writer's
four-CNOT-per-set-bit count is local only and is not a production aggregate until the grouped
write/zero-map/write/zero-map composition is proved. Concrete dual-endpoint unary scans,
upper/lower zero-map production, complete length blocks, and the indexed four-phase step remain
open within Phase 5.

### Phase 6 — forward and reverse EEA programs

Modules:

- `Submission/2607_13816/EEA/Program.lean`
- `Submission/2607_13816/EEA/Secp256k1.lean`

Compose the exact 1,620-step schedule. Forward EEA produces the inverse and retained `Γ(x)`; a
separately proved reverse schedule restores `x` and clears `Γ(x)`. Measurement prevents using a
fictional `Circuit.adjoint` for the adaptive program.

Target space is `2n + 6 floor(log2 n) + 19`, or 579 wires at `n = 256`. This must follow the actual
wire lists and reuse proof.

**Gate:** forward then reverse is identity on every nonzero field input, branch coefficients are
input-independent, and the exact secp resource vector is derived.

### Phase 7 — Appendix-B multiplication and squaring

Modules:

- `Submission/2607_13816/Arithmetic/HornerMul.lean`
- `Submission/2607_13816/Arithmetic/Square.lean`

Implement the MSB-first Horner schedule with `n` controlled modular additions and `n - 1`
doublings. Prove arithmetic, cleanup, and locality, then derive the `17 n² + O(n)` leading Toffoli
term from lower-level formulas. Naive arithmetic is not imported.

**Gate:** exact 256-bit vectors and symbolic bounds are proved for multiplication and squaring.

### Phase 8 — in-place division and multiplication

Module: `Submission/2607_13816/Arithmetic/InPlace.lean`.

Implement Figure 15: forward EEA; compute `y/x`; X-measure/reset old `Y`; reverse EEA using released
`Y`; recompute `y`; apply transcript-controlled Z correction; uncompute; and place the quotient.
Prove each branch equals `2^(-n/2)` times the intended map, independent of `x,y`, and prove the
analogous in-place multiply.

**Gate:** all measured wires are reusable and `Γ(x)` plus arithmetic work are cleared on every
branch.

### Phase 9 — total controlled affine point addition

Module: `Submission/2607_13816/PointAdd.lean`.

Implement Figure 14 and prove

```text
R |-> R + (if control then C else 0)
```

for the total elliptic-curve group law, including infinity, inverse pairs, doubling, and zero
denominators. Generic nonzero-denominator correctness is not enough for a superposed oracle. The
target is `3n + 6 floor(log2 n) + 19 = 835` live wires at `n = 256`; if total exceptional handling
requires more, report the larger proved number.

**Gate:** coherent total correctness, complete cleanup, exact resource vector, and honest live-wire
bound.

### Phase 10 — semiclassical Fourier/order finding

Modules:

- `Submission/2607_13816/Fourier/Semiclassical.lean`
- `Submission/2607_13816/OrderFinding.lean`

Prove the Figure-3 bit-by-bit measurement/feed-forward schedule has the same outcome distribution as
the mathematical inverse Fourier transform, including bit ordering. Then prove the paper
submission's own two-dimensional sampling and postprocessing theorem. It may reuse only pure Math
lemmas; it may not import Naive QFT or order finding.

Choose the exponent precision explicitly and prove `order <= 2^precision`; do not mix the paper's
generic `n + 1` diagrams with the current 256-bit specialization.

**Gate:** an independent one-run lower bound with probability summed over internal histories and
final measurement outcomes.

### Phase 11 — signed windows and QROM

Modules:

- `Submission/2607_13816/Window/Recoding.lean`
- `Submission/2607_13816/Window/TableLookup.lean`
- `Submission/2607_13816/Window/Oracle.lean`
- `Submission/2607_13816/Window/Schedule.lean`

Prove signed recoding, five sequential table lookups, lookup cleanup, and double-scalar correctness.
For `w = 16`, derive `5 * 2^16` from the QROM constructor. Make the paper's reduction from 32 naive
windows to 28 (`2n/w - 4`) explicit and prove the four omitted windows are sound.

Also construct the missing lifetime schedule between a width-16 quantum address and the
semiclassical one-wire exponent processing. Either prove the complete maximum live allocation is
835 or report the true larger value.

**Gate:** exact oracle correctness, exact lookup/window count, and full-program live-qubit theorem
for one schedule.

### Phase 12 — adaptive end-to-end contract

Modules:

- `Submission/2607_13816/Oracle.lean`
- `Submission/2607_13816/EndToEnd.lean`
- `Submission/2607_13816/Resources.lean`
- `Submission/2607_13816/Contract.lean`

Define a paper-specific adaptive oracle specification and prove coherent refinement to the pure
mathematical ECDLP map. The Naive unitary `ECDLPOracleSpec.ofCircuit` is not imported. Connect the
paper oracle, semiclassical order finding, final sampling, secp certificates, and one resource
vector in a closed record.

Report one-run resources separately from the repository's at-least-99% repeated submission:
sequential repetition multiplies time but reuses qubits.

**Gate:** unconditional concrete secp256k1 correctness, success, cleanup, exact counts, and maximum
live qubits for one executable adaptive program. Only then is replacing the default submission a
separate reviewed decision.

## 7. Paper targets that are not yet claims

| Item | Printed target | Required Lean evidence |
|---|---:|---|
| EEA steps at `n = 256` | 1,620 | exact bound certificate |
| inversion space | `2n + 6 floor(log2 n) + 19` = 579 | concrete wire lists and reuse |
| point-add space | `3n + 6 floor(log2 n) + 19` = 835 | total point add plus all live controls |
| inversion Toffolis | `< 216.636 n² + O(n log n)` | sum of exact active-window block formulas |
| point-add Toffolis | `1003 n² + O(n log n)` | exact arithmetic composition |
| full leading term | `1008 n³ / log2 n + O(n²)` | proved signed-window schedule |
| secp window schedule | `w = 16`, 28 additions, five lookups/window | exact recoding, omission, and QROM proofs |

Two discrepancies remain explicit blockers for a headline resource claim.

### 7.1 `2^30.88` versus `2^30.63`

The abstract, overview, and Table 2 report `2^30.88` Toffolis for secp256k1. The last paragraph of
Section 6.4 reports `2^30.63`. Taking its rounded Table-6 point-add value `Q_A = 70.10 million`
literally gives

```text
28 * (5 * 2^16 + Q_A) = 1,971,975,040 ≈ 2^30.877,
```

which is consistent with `2^30.88`, not `2^30.63`. Because `70.10 million` is rounded, Lean will
derive an exact integer from the program rather than adopt either printed exponent.

### 7.2 The complete 835-wire schedule is absent

The paper's one-qubit semiclassical exponent schedule and its width-16 signed-window address are not
composed in the pinned supplement. The supplement demonstrates a one-control 835-wire point-adder
layout, not the complete order-finding lifetime schedule. The final plan therefore reports and
proves separately:

- live wires for one total controlled point addition; and
- maximum live wires for the complete adaptive order-finding program.

They are equal only if Phase 11 proves the required reuse.

## 8. Active branch disposition

- **PR #55, roadmap:** closed as superseded after its approved content was incorporated into PR #56.
- **PR #56, Phase 0:** merged at `de4fc892`; source split, import gates, and pinned paper reference.
- **PR #57, Phase 1a:** merged at `75613852`; adaptive Kraus-instrument semantics.
- **PR #58, Phase 1b:** merged at `66062cbf`; coherent refinement and final-event equivalence.
- **PR #54, former adaptive foundation:** closed as superseded by the reconciled PR #57.
- **PR #59, Phase-2 measurement uncomputation:** merged at `b1e6cd85`; rebuilt from merged Phase-1
  semantics under `Submission/2607_13816/Canary/` with no stale pre-split prototype carried forward.
- **PR #60, Phase-3 pure EEA model:** merged at `3fd38b4f`; circuit-free quotient recurrence, packed
  canonical-boundary geometry and value capacity, active-step left inverse, termination, modular
  inverse, and quotient-level terminal stuttering.
- **PR #61, Phase-4 exact EEA bound/windows:** merged at `553f41be`; exact 1,620-step bound,
  indexed active/padding reachability, borrowed terminal epoch, noncanonical frame packing, and
  certified active windows. The pinned generator remainder interval is retained only as reference;
  the concrete boundary includes the proved one-lane ordering correction.
- **PR #62, Phase-5 circuit unit 1:** merged at `d1f94940`; exact bit primitives, controlled shifts
  and increment, measurement-assisted path-AND erasure, and coherently refined pruned unary
  iteration.
- **PR #63, Phase-5 circuit unit 2:** current implementation/review unit; pinned-production clean
  MAJ/UMA ripple arithmetic and per-bit borrowed-work length-update kernels. The latter are not yet
  an aggregate count. Concrete endpoint scans, zero maps, full length blocks, and the indexed step
  remain open.
- **PR #53, checkpointed Fermat inversion:** correct as a Naive fallback but superseded by EEA for
  the paper target. Keep it unmerged unless an interim unitary improvement is explicitly desired;
  otherwise close it after Phase 6 is accepted.

No paper-performance claim is attached to any of these intermediate branches.

## 9. Review gates

Every implementation PR must pass:

1. warning-fatal build;
2. root/source closure and all import-direction guards;
3. no `sorry`, `admit`, `native_decide`, or new custom axiom;
4. targeted `#print axioms` for public correctness and resource theorems;
5. exhaustive reachable-declaration axiom audit;
6. direct statement and executable-body review against its specification;
7. small differential tests against the pinned supplement where applicable;
8. hosted CI and independent exact-head review before merge.

Explicit stop/go reviews occur after measurement-based uncomputation (Phase 2), EEA model/windows
(Phase 4), concrete inversion (Phase 6), total point addition (Phase 9), full window/lifetime
scheduling (Phase 11), and the final contract (Phase 12).

## 10. Approved implementation decisions

Runzhou approved the five roadmap choices on 2026-09-02:

1. the Phase-0 relocation is path-only; existing public declaration namespaces remain stable;
2. adaptive programs use a separate Kraus-instrument semantics with a coherent-refinement bridge;
3. point addition must implement the total group law even if the honest bound exceeds 835;
4. 835 qubits, 28 windows, and `2^30.88` Toffolis remain provisional until one explicit program
   derives them; and
5. PR #53 remains unmerged as a fallback while the EEA replacement is developed.

Phases 0--4 and Phase 5 circuit unit 1 are merged. Phase 5 circuit unit 2 is the current review unit
on that foundation.
