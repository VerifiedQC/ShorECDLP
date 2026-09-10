# ShorECDLP implementation plan

ShorECDLP is an ecdsa.fail-style Lean verification repository for quantum resource-estimate
submissions against secp256k1. It currently contains one complete, deliberately naive construction.
The next construction will implement the space-efficient algorithm from
[arXiv:2607.13816v2](https://arxiv.org/html/2607.13816v2) as an independent submission.

**Status snapshot.** The verified Naive result and merged paper foundation below are on
`main@11366f2eaecf86ef87097667eb6c1649580fa504`. PR #56 → PR #57 → PR #58 → PR #59
→ PR #60 → PR #61 → PR #62 → PR #63 → PR #64 → PR #65 → PR #66 → PR #67 → PR #68
→ PR #69 → PR #70 → PR #71 → PR #72 → PR #73 → PR #74 → PR #75 → PR #76 → PR #77
→ PR #78 → PR #79 → PR #80 → PR #81 → PR #82 → PR #83 → PR #84 landed the source split, adaptive Kraus semantics,
coherent-refinement bridge, measurement-based uncomputation, pure EEA model, indexed EEA
bounds/windows, and all twenty-one Phase-5 circuit units ending with the source-ordered indexed
four-phase microstep. Phase 6 schedule unit 1 serially composes the exact
1,620 one-based forward steps, the descending explicit reverse stream, the adaptive forward
program, and the direct automatically routed trace. That trace is noncircular relative to the
complete schedule, but its route extraction and Block-B endpoint semantics remain circuit-bound.
Phase 6 schedule-cancellation unit 2 is merged in PR #84. It proves that the same forward-route
invariant suffices for the pinned reverse to restore the complete basis state: inverse decoder
routes are derived inside the proof rather than assumed. PR #85 is merged: it proves that one
explicit repaired 580-role allocation satisfies every physical component layout at all 1,620
schedule indices. The reachable-state encoding/invariant, maximum-live allocation and pinned 579
target, and aggregate paper resources remain open.
A `✓` means a
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

**Status:** all twenty-one dependency-closed construction units are merged through PR #82. PR #62 contains
standalone exact Fredkin and dirty-`C³X` decompositions, controlled circular shifts,
the supplement's controlled increment, reusable measurement-assisted path-AND erasure, and the
pruned measured unary iteration. Each exported block has basis-state semantics, restoration or
named-wire locality, physical well-formedness, and constructor-derived resource equations. The
unary traversal coherently refines its full compute/uncompute reference and uses exactly one
measurement and seven T gates per internal decision node. PR #63 implements the pinned coherent
`_apply_cell` specialization (`MEASUREMENT_UNCOMPUTE = False`) and
its prepared-slice two-pass MAJ/UMA ripple core, plus a per-bit borrowed-work XOR normal form for
the later length decoders. The ripple has direct whole-basis-state semantics, clean-scratch
restoration, named locality, and physical well-formedness. Its seven-Toffoli-per-lane equation
matches the paper; the separate 49-T equation is only the repository Framework's derived cost for
this coherent reference circuit. A later adaptive aggregate must bind and count the actual coherent
or measurement-uncompute realization it composes. The borrowed writer's
four-CNOT-per-set-bit count is local only and is not a production aggregate until the grouped
write/zero-map/write/zero-map composition is proved. PR #64 generalizes
the pruned unary decoder to circuit-valued leaf actions in zero-subtree-first (`inc`) and
one-subtree-first (`dec`) order on a caller-supplied tree, while preserving decoder wires and
coherently refining the corresponding full unitary traversal. PR #65 composes two decoder stacks
over the same caller-supplied tree in the supplement's exact local
order: compute A then B, traverse each subtree with both equality controls, reverse the switches,
and erase B then A. It proves paired decoder restoration, physical well-formedness, coherent
refinement, and exact leaf-sum resource equations. PR #66 implements the concrete
supplement construction from a deduplicated label set by scanning aligned power-of-two blocks from
the highest candidate bit downward, pruning empty halves, and emitting a node only when both halves
survive. Its certificates identify `.inc` with the sorted labels and `.dec` with their reverse,
bound path depth and index-wire positions, and keep the separately handled top bit outside the main
tree's corresponding index bank, including the singleton-main-tree case. Cross-bank exclusion
remains a full-register layout obligation. PR #67, the sixth unit, binds the source-shaped
interval arithmetic leaves to the already-certified dual-traversal interface: each label receives
a caller-supplied `qpair(j)` target/addend lane; the first ripple pass follows `.dec`, the second
follows `.inc`; label zero is masked
by the endpoint top bit; and the separately handled top label uses the supplement's direct
equality-control stream while reusing the ripple cell's clean scratch. The same concrete terms have
direct basis semantics, cleanup/locality and well-formedness contracts, adaptive coherent
refinement, and constructor-derived local/traversal resource equations. PR #68, the seventh unit,
implements the source's reusable uncontrolled increment, literal Cuccaro add/sub streams, clean
constant add/subtract, `const - x`, and exact interval-endpoint preparation/restoration, with direct
word semantics, full shared-scratch cleanup, locality, well-formedness, and constructor-derived
coherent counts. The eighth unit in this tree implements the literal upper/lower dirty zero maps,
the grouped write/map/write/map length writers, and both complete affine/write/write/affine length
blocks. It proves their direct Boolean-word semantics, borrowed-bank and clean-scratch restoration,
full outside-target locality, physical well-formedness, and constructor-derived Toffoli/CNOT/T
equations. A separate Boolean-word-to-natural bridge gives the arithmetic meaning and involution
of the affine word transforms, while the exact endpoint prepare/restore streams now have a full
basis-state roundtrip theorem. The ninth unit now instantiates the certified source-built tree,
the two physical decoder stacks, endpoint/equality/carry/accumulator/cell scratch lanes, and every
`qpair(j)` work-bank lane in the complete forward interval wrapper. Its literal coherent circuit
and measurement-uncomputed adaptive realization share the source order
`prepare; top-first; decreasing scan; sign; increasing scan; top-second; restore`, with direct
basis-state semantics, clean-input coherent refinement, complete physical locality and
well-formedness, and constructor-derived Toffoli/CNOT/T/measurement equations. The adaptive term
follows the supplement's single global measurement-uncompute switch: reverse decoder paths, every
main-leaf ripple cell, every top-special ripple cell, and both top-special equality v-chains use
the measured erasure. Finite work-bank obligations are restricted to labels actually present in
the certified tree, and a closed five-lane physical allocation proves that the complete layout is
inhabited. Pinned regressions cover the singleton and two-lane edge cases, a nontrivial 8-bit
top-special instance, and the production-shaped 257-lane instance; their adaptive measurement/T
counts are respectively `2/315`, `4/462`, `34/987`, and `1598/18319`. Output
scratch restoration was left open at that boundary. The tenth unit adds the pinned source inverse
as the same exact wrapper at the opposite ripple mode, proves the literal endpoint streams reverse
each other without pretending they are syntactic adjoints, and proves the opposite-mode dual
traversals and top-special leaves implement the coherent body's adjoint. The inverse adaptive
realization reuses the forward coherent-refinement proof and has exactly the same Toffoli, CNOT, T,
and measurement formulas, including the closed five-lane regression. The eleventh unit closes the
scratch invariant directly at the interval boundary: dirty-scratch Cuccaro half-cell pairs and
opposite tree traversals restore every non-target lane, the sign update is transported through the
sign-disjoint second traversal, and the separately handled top pair is composed using the physical
lane separation. Consequently both forward and inverse coherent/unitary wrappers derive output
`IntervalReady` from the sole input premise, and the two whole-state round-trip theorems no longer
assume cleanup at the output boundary. The twelfth unit implements the forward production
`phase_update_gate`: three truth-minus-one zero tests, the literal phase/sign core, and the borrowed
shift-epoch conjugations at their exact source positions. It proves direct whole-state semantics,
scratch restoration, locality and well-formedness, adaptive coherent refinement, exact symbolic
counts, and small/production source regressions. At the 9/9/9-bit production widths the isolated
block uses 44 wires, 98 coherent Toffolis / 686 T, or 44 measurements / 378 T after the source's
measurement-uncomputation choice. The thirteenth unit implements the source's explicit inverse:
it reconstructs the unchanged zero predicates, reverses the phase/sign core, and erases the
predicates in the same source block order. Its coherent term is proved exactly equal to the
forward term's adjoint, while its adaptive term is defined separately so equality-chain cleanup
retains measurement uncomputation. Direct inverse semantics, clean-scratch restoration, both
whole-state round trips, locality/well-formedness, and equal forward/inverse symbolic and
small/production resource regressions are all certified. The fourteenth unit implements the
surrounding source-exact pre/post shifts: controlled
decrement, the cycle-decomposed right-by-two rotation, and both complete wrappers. Direct
whole-state semantics, all-scratch restoration, declared-support locality and outside preservation,
well-formedness, both adjoint round trips, literal small-source streams, and constructor-derived
counts are certified. At `work_size = 259` and `shift_width = 9`, each source block allocates 283
roles and restores all 13 scratch roles. Same-term `qubitCount` witnesses prove that pre-shift
touches exactly 280 roles and post-shift exactly 279; pre-shift has `566 CCX`, `1067 CX`, `68 X`,
and `3962 T`, while post-shift has `566 CCX`, `1065 CX`, `64 X`, and `3962 T`. The fifteenth unit
implements Figure 9's `lc_swap_unary_gate`: it adds the two truth-minus-one length words and the
source constant three, routes through the certified highest-varying-bit tree, conditionally swaps
the sign with exactly `Work1[J-k]` when the prepared value `J` lies in `k, ..., K`, then restores
both affine updates and all shared scratch. The route-to-numeric-label theorem and the modular word
equation certify that `J = ell_t + ell_q + 1`; whole-state semantics, locality,
well-formedness, adaptive coherent refinement, adjoint cancellation, and constructor-derived
coherent/adaptive resource equations are included. The closed `k=2`, `K=5`, width-three regression
uses 16 wires and certifies `34 CCX`, `62 CX`, `20 X`, `238` coherent T gates, or three measurements
and `217` adaptive T gates. The sixteenth unit implements the forward source block
`lc_prefix_addsub_prepared_boundary_gate`: it seeds the shared prefix accumulator, traverses the
exact highest-varying-bit tree in increasing order with the first Figure-11 ripple cell, optionally
updates the sign from carry, traverses in decreasing order with the second cell, and clears the
accumulator. The literal coherent and measurement-uncomputed terms share the same source tree and
leaf order; direct whole-state semantics, scratch restoration, locality/well-formedness, coherent
refinement, exact adjoint cancellation, and constructor-derived counts are certified. The closed
four-label regression touches 17 roles and has `40 CCX`, `39 CX`, `24 X`, and `280` coherent T
gates, or 14 measurements and `182` adaptive T gates. At the production 257-lane window the
symbolic formulas give `2823 CCX`, `2568 + signUpdate CX`, and `19761` coherent T gates, or 1026
measurements and `12579` adaptive T gates; an explicit 537-role allocation witnesses that full
`(1,257,9)` layout. Its coefficient-specific contract does not inherit the quotient selector's
unrelated equal-width arithmetic-register condition: the first actual narrow production call
`(k,K,len_width)=(1,2,9)` has an inhabited 27-role layout, touches 10 wires, and certifies `18 CCX`,
`18 CX`, `8 X`, and `126` coherent T gates, or 6 measurements and `84` adaptive T gates.
The seventeenth unit implements the exact `_prepare_latest_paper_t_boundary` and
`_restore_latest_paper_t_boundary` source pair around that prefix update: add/subtract the stored
truth-minus-one offset, reflect and subtract the low shift word, and select the Phase-4 endpoint
with the literal bitwise Fredkin loop. Pure-word and complete-basis-state semantics prove both
two-sided round trips, restore the shared width-plus-one arithmetic scratch, preserve every wire
outside the two boundary words, and establish locality, `HPFree`, and well-formedness. At the
production width nine, either block borrows ten clean scratch roles, touches exactly 38 wires, and
has `77 CCX`, `136 CX`, `16 X`, and `539` coherent T gates. The eighteenth unit implements the
exact `lc_prefix_addsub_prepared_boundary_gate(..., inverse=True)` branch. It preserves the pinned
tree and block order while replacing the second/first Figure-11 cells by opposite-mode first/second
cells, proves that literal specialization is exactly the coherent forward term's adjoint, and gives
a circuit-free reverse recurrence with direct whole-state semantics. Complete scratch restoration,
locality/HP-free/well-formedness, both circuit and recurrence round trips, adaptive coherent
refinement, two flattened narrow source comparisons, and constructor-derived coherent/adaptive
resource equations are certified. The inverse has the same `2823 CCX`,
`2568 + signUpdate CX`, `19761` coherent T, `1026` measurements, and `12579` adaptive T formulas
at the production 257-lane window. The nineteenth unit implements the remaining source-level
control and terminal helpers needed by
that composition: reverse-cleanup mixed-polarity `compute_control`; the nonterminal R-control with
its all-ones length exclusion erased before arithmetic; the quotient-low-bit spill/restore of the
borrowed terminal epoch; and the terminal padding left-rotate/increment/wrap update with its literal
inverse. Each circuit has complete-basis-state semantics, scratch restoration, two-sided
cancellation where an inverse exists, locality/HP-free/well-formedness, flattened source
regressions, and constructor-derived resources. At the production 259-bit Work2 and 9-bit shift
width, the minimum source-valid standalone terminal-padding witness declares 279 roles and touches
278. The full-step caller supplies 287 formal roles from its shared auxiliary pool but emits the
identical 278-wire stream: `305 CCX`, `527 CX`, and `2135 T`, with respectively 36 and 68
standalone X gates in the forward and inverse. The twentieth unit composes the pinned
`swap_work_and_len_unary_shared_gate` literally: a controlled full-Work Fredkin swap followed by
the upper and lower length updates in serial over one restored scratch pool; its inverse reverses
those blocks explicitly. Direct circuit-free and whole-state semantics, clean-scratch restoration,
outside preservation, locality/HP-free/well-formedness, and a forward-then-inverse round trip are
proved for the exact aggregate. Its constructor-derived formulas are closed by both a small
regression and the production windows `(k₄,K₄,k₅,K₅)=(1,258,164,259)`. The production allocation
declares 549 dense roles, and either direction has `14463 CCX`, `12034 CX`, `16948 X`, and
`101241 T`; this is a declared-role capacity witness, not an exact touched-wire claim. The
twenty-first unit composes all eight literal source blocks A--H over `certifiedActiveWindows`,
together with the supplement's explicit reverse block order. The coherent forward term has direct
blockwise whole-state semantics under the encoded borrowed-epoch boundary and decoded
end-of-iteration routes; it is noncircular relative to the full indexed circuit, while Block B
retains the interval layer's circuit-bound endpoint preparation/restoration semantics. It restores
every shared temporary. The same physical contract proves the forward, reverse, and adaptive
terms well formed and the two unitary terms HP-free. A closed 46-role compact allocation makes
the contract non-vacuous, and a complete `n=256,T=1` witness inhabits that entire contract with
580 internal roles; the already certified production end-of-iteration layout covers the optional
fourth-step aggregate. The adaptive term
replaces exactly the two interval calls, two coefficient-prefix calls, and the phase update, and
coherently refines the same forward circuit on clean, epoch-encoded inputs. Constructor-derived
formulas expose all eight coherent forward and reverse blocks and the exact adaptive
measurement/worst-branch-T sums. This closes the source-level single-step composition; the
1,620-step reachable-state encoding/refinement, reverse-program cancellation, maximum-live-wire
allocation, and aggregate paper vector remain Phase 6 rather than being inferred here.

### Phase 6 — forward and reverse EEA programs

Modules:

- `Submission/2607_13816/EEA/Schedule.lean`
- `Submission/2607_13816/EEA/Program.lean`
- `Submission/2607_13816/EEA/Secp256k1.lean`

Compose the exact 1,620-step schedule. Forward EEA produces the inverse and retained `Γ(x)`; a
separately proved reverse schedule restores `x` and clears `Γ(x)`. Measurement prevents using a
fictional `Circuit.adjoint` for the adaptive program.

**Status:** schedule unit 1 merged in PR #83 at `f5d91bef`. It defines one shared recursion for the exact
forward, descending explicit-reverse, adaptive-forward, and direct automatically routed schedules;
proves forward whole-state semantics, structural well-formedness/HP-freedom, and adaptive coherent
refinement; and fixes the secp256k1 horizon to indices `1, ..., 1620`. The routed trace avoids the
complete schedule circuit but retains circuit-bound route extraction and Block-B endpoint
semantics. Schedule-cancellation unit 2 merged in PR #84 at `72d2ffa`; it derives the inverse decoder routes
from those forward routes, proves each literal indexed step cancels, lifts cancellation through the
descending schedule, and instantiates the exact 1,620-step secp256k1 round trip. These theorems
remain conditional on the existing threaded layout/state invariant. PR #85 proves the physical
layout half for every index using the same explicit repaired 580-role allocation. The concrete EEA
state encoding must still inhabit the readiness, epoch, and routed-state invariant. No
unconditional nonzero-input inversion, live-allocation, or aggregate-resource claim is attached yet.

The pinned source target is `2n + 6 floor(log2 n) + 19`, or 579 wires at `n = 256` including the
external point-add control. The presently verified conservative remainder repair needs two more
internal scratch roles, so the closed first-step witness is 580 internal / 581 with that control.
Recovering 579 must follow either a tighter remainder-window proof or a concrete safe-reuse proof;
it is not inferred from the source formula.

**Gate:** forward then reverse is identity on every nonzero field input, branch coefficients are
input-independent, and the exact secp resource vector is derived.

### Phase 7 — Appendix-B multiplication and squaring

**Current:** Runzhou prioritized Phases 7–12 on 2026-09-06. The Phase-6 reachable-state
readiness/routing proof remains open and must remain explicit wherever later phases depend on
inversion. The first Phase-7 unit is `Arithmetic/CarryAdd.lean`: the pinned quadratic backend's
controlled carry-output adder and literal inverse, with direct arithmetic/frame correctness and
constructor-derived counts. The fixed 256-bit theorem combines controlled-sum and overflow
semantics, input/carry restoration, 769 Toffolis, 1,024 CNOTs, 5,383 coherent T gates, and exactly
515 distinct wires for the same circuit. This component certificate covers the binary adder.
The uniform recurrence matches the source for widths at least two and corrects its one-bit
special case, whose overflow update ignores the accumulator.

`Arithmetic/Compare.lean` adds the controlled unsigned carry-probe comparison. Its direct
whole-state theorem changes only the result flag and restores both operands and the clean
carry. The readable 256-bit certificate proves 513 Toffolis, 1,024 CNOTs, 516 X gates,
3,591 coherent T gates and exactly 515 distinct wires for that same circuit. Its stream
matches the pinned comparator for widths at least two; width one uses the full correct
carry chain instead of the source's shorter optimization.

`Arithmetic/ConstCarry.lean` implements the controlled `_xor_carries_all` gate stream used
by the Gidney constant-arithmetic cleanup. Its two sweeps XOR ordinary addition carries
into arbitrary borrowed data while preserving every other wire. The fixed 256-bit
`2^32 + 977` correction circuit has a combined correctness/resource certificate:
511 Toffolis, 47 CNOTs, 3,577 coherent T gates and exactly 514 distinct wires.
`Arithmetic/GidneyAdd.lean` completes the controlled measurement-assisted constant adder.
Its direct branch theorem proves the numeric sum modulo the word power of two, restores
all borrowed and clean work, and removes every measurement-dependent phase. The same
256-bit circuit has a readable combined certificate: 764 Toffolis, 1,344 CNOTs, 5,348 T,
255 measurement/resets and exactly 515 distinct physical wires. Well-formedness proves
total probability preservation. The zero-constant shortcut and width-one case are included.
`Arithmetic/GidneyCompare.lean` completes the controlled measurement-assisted constant
comparator, including zero and out-of-range threshold shortcuts. Every branch toggles
only the arbitrary result flag by the controlled numeric predicate; borrowed/clean work
is restored, both correction phases cancel, and total probability is preserved. The
same-circuit secp256k1-modulus certificate proves 767 Toffolis, 1,598 CNOTs, 5,369 T,
256 measurement/resets and exactly 517 physical wires. `Arithmetic/GidneyCarry.lean`
shares the existing measured-carry facts and metrics between the adder and comparator.
`Arithmetic/ModularCorrection.lean` proves the arithmetic bridge for modular addition:
the overflow/comparison XOR selects the correction, the corrected word is the canonical
modular sum, and the final comparison clears the flag. It also proves the odd-modulus
parity identity used to clear the doubling flag. These are arithmetic lemmas only; the
composed modular addition and doubling circuits are now proved below. The Horner schedule
and squaring remain open.
`Arithmetic/UncontrolledCompare.lean` supplies the uncontrolled constant-comparison
interface. `Arithmetic/ConstantControl.lean` compiles external-control CNOTs to X gates,
proves branch amplitudes are preserved, and removes exactly that control from physical
support. The compile-time fresh label appears in no emitted gate or measurement.
The same-circuit secp256k1 theorem proves the numeric flag predicate, complete frame and
workspace restoration, total probability one, 767 Toffolis, 1,537 CNOTs, 5,369 T gates,
256 measurement/resets and exactly 516 physical wires. No extra enable qubit is allocated.
`Arithmetic/ModularAdd.lean` composes the four actual source stages: controlled binary
addition with overflow, uncontrolled modulus comparison, conditional constant correction,
and the final comparison that erases the reduction flag. For canonical operands, every
branch implements controlled modular addition with positive input-independent amplitude
and restores every wire outside the accumulator, including the borrowed addend. Its
same-circuit certificate proves total probability one, well-formedness, 2,813 Toffolis,
4,929 CNOTs, 19,691 T gates, 511 measurement/resets and exactly 517 physical wires. The
source's fifth auxiliary wire is unused and excluded from actual support. Width one uses
the verified full binary comparator chain. `Arithmetic/Doubling.lean` supplies the literal high-bit extraction, descending swap
rotation and low-bit clearing prefix, then reuses measured comparison/correction and
proves parity-based flag cleanup for odd moduli. Every branch implements canonical modular
doubling and restores all other wires, including arbitrary borrowed data. Its same-circuit
certificate proves total probability one, well-formedness, 1,531 Toffolis, 3,649 CNOTs,
10,717 T gates, 511 measurement/resets and exactly 516 physical wires. The aggregate counts
are derived from the modular adder's same shared comparison/correction circuits, replacing
the binary-add/comparison endpoints with the doubling prefix/final CNOT. The fixed squaring circuit is now proved as described below. `Arithmetic/HornerMul.lean` composes the literal MSB-first schedule,
including the source’s carry/flag exchange in doubling. Its same-circuit certificate proves
the modular product from a zero output, restoration of all other wires, positive
input-independent branch amplitudes and total probability one. The fixed multiplier uses
1,110,533 Toffolis, 2,192,319 CNOTs, 7,773,731 T gates, 261,121 measurement/resets and
exactly 772 physical wires. Scalar-label-parametric component proofs account for the
reused register allocation; the fifth source auxiliary wire is unused.

Modules:

- `Submission/2607_13816/Arithmetic/HornerMul.lean`
- `Submission/2607_13816/Arithmetic/Square.lean`

`Arithmetic/Square.lean` copies each selected input bit to a clean control, performs the
modular addition, and un-copies it after the borrowed input is restored. Its same-circuit
certificate proves the modular square, complete frame restoration and normalized branches,
with 1,110,533 Toffolis, 2,192,831 CNOTs, 7,773,731 T gates, 261,121 measurement/resets
and exactly 517 wires. Both circuits use `n` additions and `n - 1` doublings; their costs
are derived symbolically over the loop length from the fixed 256-bit component counts.
`Arithmetic/ResourceGrowth.lean` additionally proves the exact count `17 n² - 14 n + 5`
for both actual circuits at every width `n ≥ 2`, with a nontrivial threshold and an odd
correction. It derives `3n - 4` for the constant adder, `3n - 1` for uncontrolled comparison,
`11n - 3` for modular addition and `6n - 5` for doubling, then counts the actual loop.
The same production terms retain their previously proved correctness and resource certificates.
Naive arithmetic is not imported.

**Gate:** exact 256-bit vectors and symbolic bounds are proved for multiplication and squaring.

Phase 7 completed and merged through PR #97 on 2026-09-08, after local verification,
independent review and hosted CI.

### Phase 8 — in-place division and multiplication

Module: `Submission/2607_13816/Arithmetic/InPlace.lean`.

Implement Figure 15: forward EEA; compute `y/x`; X-measure/reset old `Y`; reverse EEA using released
`Y`; recompute `y`; apply transcript-controlled Z correction; uncompute; and place the quotient.
Prove each branch equals `2^(-n/2)` times the intended map, independent of `x,y`, and prove the
analogous in-place multiply.

The first inverse-arithmetic prerequisite is implemented in `Arithmetic/ModularSub.lean`.
The actual source subtraction stages undo modular addition on canonical inputs in every
measurement branch, restoring the complete pre-addition state. Its same-circuit 256-bit
certificate records 2,813 Toffolis, 7,350 CNOTs, 19,691 T gates, 511 resets and 517 wires.
The correction adds the modulus rather than `2^256 - p`, so its CNOT count differs from
forward addition. The Figure-15 composition
remains open; the Phase-6 reachable EEA readiness invariant is still an explicit boundary.

`Arithmetic/Halving.lean` proves the next source inverse stage: measured halving
restores the complete state after modular doubling of a canonical residue modulo
an odd modulus. Its same-circuit 256-bit certificate gives 1,531 Toffolis, 6,070
CNOTs, 10,717 T gates, 511 resets and 516 wires. The measured stages are proved
directly; only the final unitary shift is adjointed.

`Arithmetic/HornerInverse.lean` composes the source subtraction/halving schedule
from the low multiplier bit upward. Every actual forward/inverse branch pair
restores the complete zero-output input state with a positive, input-independent
coefficient. The inverse's same-circuit certificate gives 1,110,533 Toffolis,
3,429,450 CNOTs, 7,773,731 T gates, 261,121 resets and 772 wires. This closes the
inverse multiplier prerequisite, not the Figure-15 in-place composition or EEA
readiness boundary.

`Arithmetic/ConstMinus.lean` implements the EEA wrapper's controlled complement,
measured increment and measured modulus addition. It proves canonical `p - x`,
complete frame preservation, and cancellation for arbitrary pairs of measurement
outcomes. The same-circuit certificate gives 1,528 Toffolis, 5,305 CNOTs, 10,696
T gates, 510 resets and 515 wires. This is the concrete preprocessing/postprocessing
primitive; full wrapper encoding, reachable-state readiness and Figure 15 remain open.

`EEA/Centering.lean` composes the actual comparison and constant-minus preprocessing
pair and its literal reverse. It produces `min(x,p-x)`, retains the sign in `Iter`,
and proves that the positive centered divisor fits in 255 bits. Every independent
forward/reverse measurement-branch pair restores the full initial state. Both
concrete directions have 2,295 Toffolis, 6,842 CNOTs, 16,065 T gates, 766 resets
and 516 wires. The general comparison support/count theorem now includes even
thresholds. This closes input centering; the rest of the wrapper and Figure 15
remain open.

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
| inversion space | pinned 579; current repaired witness 581 | tighter remainder proof or concrete wire reuse |
| point-add space | `3n + 6 floor(log2 n) + 19` = 835 | total point add plus all live controls |
| inversion Toffolis | `< 216.636 n² + O(n log n)` | sum of exact active-window block formulas |
| point-add Toffolis | `1003 n² + O(n log n)` | exact arithmetic composition |
| full leading term | `1008 n³ / log2 n + O(n²)` | proved signed-window schedule |
| secp window schedule | `w = 16`, 28 additions, five lookups/window | exact recoding, omission, and QROM proofs |

Three discrepancies remain explicit blockers for a headline resource claim.

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

### 7.3 The certified remainder repair currently costs two wires

The untouched pinned generator uses 578 internal EEA roles, or 579 after adding the external
point-add control, because its first remainder window is `3..259`. Correctness of the concrete
gate order currently requires the conservative certified window `2..259`. Its 258-lane dual
decoder needs 21 scratch roles after `Aux[0]`, two more than the pinned `Aux[1:]` bank supplies.
The complete Lean layout therefore appends two repair-only roles and certifies 580 internal / 581
with the external control. The two roles are used only by the repaired remainder block; every
other block retains the pinned source projection. A 579-wire headline remains open until Lean
either removes the extra lane from the correctness proof or proves those roles can safely alias
other live storage.

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
- **PR #63, Phase-5 circuit unit 2:** merged at `3eae43e9`; pinned coherent
  `_apply_cell` MAJ/UMA ripple arithmetic and per-bit borrowed-work length-update kernels. Seven
  Toffolis per lane matches the paper; 49 T is only the Framework-derived coherent-circuit cost.
  Neither that T equation nor the borrowed-writer equation is yet an adaptive aggregate.
- **PR #64, Phase-5 circuit unit 3:** merged at `74d86947`; circuit-valued pruned
  unary traversal in zero-subtree-first (`inc`) and one-subtree-first (`dec`) order on a
  caller-supplied tree, with decoder restoration, physical well-formedness, coherent refinement,
  and constructor-derived resource equations.
- **PR #65, Phase-5 circuit unit 4:** merged at `de9fff8f`; synchronized dual-endpoint traversal
  on a caller-supplied tree, with the exact A-then-B compute, paired branch switches, B-then-A
  cleanup, paired decoder restoration, coherent refinement, and constructor-derived resource
  equations.
- **PR #66, Phase-5 circuit unit 5:** merged at `e83ebd12`; concrete
  sorted/deduplicated-label, highest-varying-bit tree construction with numeric forward/reverse
  order, recursive source-shape, path-depth, index-wire, and corresponding-bank source-top-bit
  exclusion certificates. Cross-bank exclusion remained a full-register layout obligation at that
  boundary, alongside the arithmetic leaves, zero maps, full length blocks, and indexed step.
- **PR #67, Phase-5 circuit unit 6:** merged at `73434f1f`; clean v-chain direct equality,
  masked-zero main leaves and direct top-special leaves, caller-supplied per-label `qpair(j)` lanes
  in the `.dec`/`.inc` dual scans, shared equality/ripple scratch restoration, basis semantics,
  cleanup/locality, well-formedness, coherent refinement, and constructor-derived local/traversal
  resource equations. Complete interval-block instantiation remained open at that boundary.
- **PR #68, Phase-5 circuit unit 7:** merged at `7f4e9cb1`; source affine endpoint layer:
  uncontrolled increment,
  literal Cuccaro add/sub, clean constant add/subtract, `const - x`, and exact endpoint
  preparation/restoration, with direct word semantics, full shared-scratch cleanup, locality,
  well-formedness, and coherent resource equations. Their Nat/mod-`2^w` interpretation and the
  formal endpoint round trip remained open at that boundary.
- **PR #69, Phase-5 circuit unit 8:** merged at `deeeb945`; Boolean-word-to-natural affine
  semantics, a full
  endpoint prepare/restore basis-state round trip, literal upper/lower dirty zero maps, grouped
  write/map/write/map length writers, and both complete affine/write/write/affine length blocks,
  with direct semantics, borrowed-bank and scratch restoration, full outside-target locality,
  physical well-formedness, and exact constructor-derived Toffoli/CNOT/T equations. The
  source-built tree and physical register/lane instantiation in the complete interval wrapper, the
  inverse aggregate, and the indexed step remain open.
- **PR #70, Phase-5 circuit unit 9:** merged at `fc9436c`; complete forward interval wrapper over the certified
  source tree and concrete physical register/lane allocation, with literal coherent and adaptive
  programs, direct basis-state semantics, clean-input coherent refinement, complete
  locality/well-formedness, and exact constructor-derived resources. The adaptive program applies
  the source's global measurement-uncompute choice to decoder, ripple-cell, and equality cleanup;
  a kernel-checked five-lane layout witness rules out vacuous physical contracts. The inverse
  wrapper and the indexed reachable-state theorem needed to prove output scratch cleanup remain
  open.
- **PR #71, Phase-5 circuit unit 10:** merged at `4e7cad8b`; exact source inverse interval
  aggregate, defined by the source's opposite ripple-mode specialization of the same wrapper. It
  adds two-sided complete-state round trips under clean input/output wrapper boundaries, the
  reverse endpoint identity needed for that proof, coherent and adaptive contracts, and matching
  constructor-derived resource equations. Output scratch restoration remained open at that
  boundary.
- **PR #72, Phase-5 circuit unit 11:** merged at `c468d137`; the complete interval
  scratch-restoration proof.
  Dirty-state paired ripple cells and opposite tree traversals restore every non-target lane; the
  concrete sign/main/top layout transports that cancellation through the full body. Both
  coherent/unitary wrapper directions now derive output `IntervalReady` from input alone, so
  neither whole-state round trip retains the former intermediate output-readiness premise.
- **PR #73, Phase-5 circuit unit 12:** merged at `7f52576d`; the exact forward borrowed-epoch
  phase-update controller, with direct whole-state semantics and cleanup,
  locality/well-formedness, adaptive coherent refinement, constructor-derived counts, and pinned
  small/production stream and resource regressions.
- **PR #74, Phase-5 circuit unit 13:** merged at `7fb0cffe`; the pinned explicit phase-update
  inverse. Its
  coherent term is proved equal to the forward term's adjoint, while its separately defined
  adaptive term retains measurement-uncomputed predicate cleanup. Direct inverse semantics,
  scratch restoration, both whole-state round trips, locality/well-formedness, and equal
  forward/inverse resource regressions are certified.
- **PR #75, Phase-5 circuit unit 14:** merged at `0a5bc180`; the exact pre/post shift layer: controlled
  decrement, cycle-decomposed right-by-two rotation, and both literal source wrappers, with direct
  whole-state semantics, complete scratch restoration, locality/well-formedness, two-sided
  adjoint cancellation, literal source regressions, and exact production resources. Both wrappers
  allocate 283 roles and restore 13 scratch roles; same-term `qubitCount` witnesses certify exact
  touched-wire counts of 280 for pre-shift and 279 for post-shift.
- **PR #76, Phase-5 circuit unit 15:** merged at `fedbf2fc`; Figure 9's exact
  location-controlled quotient/sign swap,
  including affine preparation/restoration, a certified numeric route through the source-built
  unary tree, whole-state semantics and scratch restoration, locality/well-formedness, adaptive
  coherent refinement, symbolic resources, and a closed small-source regression.
- **PR #77, Phase-5 circuit unit 16:** merged at `9f5485e7`; the exact forward prepared-boundary
  coefficient-prefix block, including both ordered unary traversals, the optional sign update,
  direct whole-state semantics, scratch restoration, locality/well-formedness, adaptive coherent
  refinement, exact cancellation, and small/production resource regressions. Its dedicated routing
  contract permits the pinned schedule's narrow `(1,2,9)` window without dummy coefficient lanes.
- **PR #78, Phase-5 circuit unit 17:** merged at `42b8fa02`; the exact phase-dependent coefficient-boundary
  preparation/restoration pair surrounding the forward prefix block. It includes direct word and
  whole-state semantics, shared-scratch restoration, outside preservation, locality/HP-free/WF,
  two-sided round trips, and exact source-order and production resource witnesses.
- **PR #79, Phase-5 circuit unit 18:** merged at `29abb3d0`; the pinned explicit coefficient-prefix
  inverse as the same source traversal at opposite ripple mode. It includes the exact adjoint identity, direct
  gate-independent reverse semantics, full scratch restoration, two-sided circuit and recurrence
  round trips, locality/well-formedness, adaptive coherent refinement, flattened source
  comparisons, and equal forward/inverse symbolic and production resource equations.
- **PR #80, Phase-5 circuit unit 19:** merged at `1812e576`; the source-exact control/terminal prerequisite:
  reverse-cleanup mixed-polarity control, nonterminal R-control, borrowed terminal-epoch
  spill/restore, and the terminal padding rotation with its inverse. Direct whole-state semantics,
  complete scratch restoration, two-sided cancellation, locality/well-formedness, flattened source
  regressions, and exact production resource equations are included.
- **PR #81, Phase-5 circuit unit 20:** merged at `7b0b302c`; the exact end-of-iteration work/length aggregate
  and its explicit reverse. The literal circuit performs the full controlled Work-register swap,
  then the upper and lower length updates serially over shared restored scratch. Direct semantics,
  cleanup and outside preservation, locality/HP-free/well-formedness, a forward-then-inverse
  whole-state round trip, symbolic counts, a small constructor regression, and the production
  `(1,258,164,259)` window/allocation witness are included. The production witness declares 549
  dense roles and certifies `14463 CCX`, `12034 CX`, `16948 X`, and `101241 T` for either
  direction.
- **PR #82, Phase-5 circuit unit 21:** merged at `b056de52`; the exact indexed four-phase microstep. It composes the
  eight source blocks over the certified active windows, defines the explicit reverse stream,
  proves direct blockwise forward whole-state semantics and complete shared-scratch restoration,
  with Block B retaining the interval layer's circuit-bound endpoint semantics, and gives
  well-formedness/HP-free contracts plus coherent adaptive refinement for the same source term.
  Exact resource theorems decompose both coherent directions and the adaptive measurement/T
  realization. A compact 46-role nonterminal witness closes basic non-vacuity, while a full
  `n=256,T=1` witness certifies the repaired 580-internal / 581-with-external-control allocation.
  The pinned 578/579 source count is recorded separately and its recovery remains open. The
  1,620-step physical encoding/refinement, reverse-program
  identity, maximum live allocation, and aggregate resource theorem remain Phase 6.
- **PR #83, Phase-6 schedule unit 1:** merged at `f5d91bef`; the exact one-based `1, ..., 1620`
  scheduler. One
  recursion binds the forward unitary, descending explicit reverse, adaptive forward program, and
  direct automatically routed state trace. The trace is noncircular relative to the complete
  schedule but retains circuit-bound route extraction and Block-B endpoint semantics. The unit
  proves per-index structural composition, forward whole-state semantics and final scratch
  readiness, and input-independent coherent measurement-uncomputation under a threaded schedule
  invariant. That unit intentionally made no reverse-decoder agreement or identity claim; the
  concrete invariant witness, live-wire allocation, and aggregate paper vector remained open.
- **PR #84, Phase-6 schedule cancellation unit 2:** merged at `72d2ffa`; derives the explicit inverse decoder
  routes from the already required forward routes, proves all eight literal indexed-step blocks cancel,
  composes that result through the descending reverse schedule, and closes the exact 1,620-step
  secp256k1 round trip. The result uses the same threaded layout/state invariant as forward
  correctness and adds no reverse-correctness premise. A concrete reachable-state encoding/layout
  witness, maximum-live allocation, and aggregate resource vector remain open.
- **PR #85, Phase-6 schedule layout unit 3:** proves that the same explicit repaired
  580-role production allocation satisfies every physical `IndexedStepLayout` contract at all
  1,620 secp256k1 schedule indices. This is a fixed declared-role layout witness, not an exact
  maximum-live-wire or pinned-579 claim. The reachable-state encoding/readiness/route invariant,
  unconditional inversion endpoint, live allocation, and aggregate resource vector remain open.
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

Phases 0--5 and Phase 6 schedule units 1--2 are merged through PR #84 at `main@72d2ffa`. PR #85
closes the fixed 1,620-step physical layout with the explicit repaired 580-role allocation. The
reachable-state encoding/invariant, maximum-live allocation and pinned-579 recovery, unconditional
inversion endpoint, and aggregate resource boundary remain open.

### EEA encoded-length initialization

The concrete `lengthInitialize` circuit implements the source first-one scan and all-zero
sentinel. `lengthInitialize_correct` proves XOR of bit-length-minus-one into an arbitrary
target word with a complete frame; the clean flag and known modulus workspace are restored
after each case. Abstract source MCX calls are explicitly lowered using the existing clean
v-chain after clearing known workspace bits, then restoring their constant. This changes
the MCX implementation, not its logical action, and allocates no additional large register.

`secp256k1LengthInitialize_correct_resources` ties that same circuit to 131,068 CCX, 1,035 CX,
917,476 T and a 520-wire capacity bound, including 254 reused known workspace bits. The input
is big-endian; the target and known scratch constants are little-endian. These are costs of
this explicit lowering, not resource claims about Qiskit's abstract MCX implementation.
Full wrapper preparation/encoding, the reachable EEA invariant and Figure 15 remain open.

### EEA work-bank preparation

`workRegistersPrepare` composes the pinned Work2 permutation with the source-order Work1
constant toggle in the schedule's existing allocation. The same-program certificate proves
Work1=(t=1,r=p), Work2=(s=0,r′=x), their bit orders, a complete frame and full-state cancellation
by the explicit source reverse. Preparation has 641 gates (390 CX and 251 X), zero T and a
518-wire capacity bound for the two existing work banks. Both directions have proved physical
well-formedness, H/P freedom, 390 CX and zero Toffoli/T cost. The forward and reverse Work2
streams preserve the source permutation builder's exact 130-swap order.

This completes the initial work-bank arrangement. Its preprocessing composition follows below;
full EEA encoding and the reachable-state invariant remain open.


### EEA preprocessing composition

`eeaPreprocess` now composes bank preparation, adaptive input centering and all four source
length-word initializations in the existing 580-role allocation. The constant modulus bits
provide the known scratch for the explicitly lowered length-initializer MCXs.

`eeaPreprocess_branch_correct` proves that every actual measurement branch maps the complete
initial basis state to `eeaPreprocessIdealState`, with positive history-length amplitude.
`eeaPreprocessIdealState_correct` derives the positive centered divisor `min(x,p-x)`, retained
sign bit, coefficient headers, preserved modulus, both zero-length sentinels, divisor-length
encoding, clean remaining control/scratch roles and complete external frame. The concrete
prefix is well formed. Initialization assumes only the source's clean non-input roles and
`0 < x < p`; it does not assume that the desired output encoding already holds.

This closes the forward Algorithm-1 preprocessing prefix. The connection to the pure EEA
state, reachable-state schedule invariant and terminal/reverse wrapper remain open; this is not the full inverse or Figure-15 multiplication circuit.


### EEA preprocessing resources

`eeaPreprocess_correct_resources` combines the actual measurement-branch contract with exact
aggregate counts: 133,363 Toffolis, 8,267 CNOTs, 933,541 T gates and 766 measurements. The
physical-support proof keeps the whole prefix within the existing 580-role allocation.
These totals are composed from the actual primitive circuits, including the known-scratch
MCX lowering for length initialization. A generic CX-count invariance lemma transfers existing
adder counts to the wrapper's reordered data and borrowed registers without changing circuits.

The 580 figure is the proved capacity bound, not an exact used-wire or live-allocation claim.
The emitted prefix uses 550 distinct wires; proving the full wrapper, reachable EEA invariant
and eventual live-space/resource bounds remains separate work.


### Initial EEA numeric encoding and readiness

`EEA/InitialEncoding.lean` connects the concrete preprocessing prefix to the numeric
`paperInitial` divisor, iteration-parity bit and divisor-length metadata. Its generic
first-set-bit theorem identifies the big-endian scan with `Nat.size`, including zero;
the length initializer retains the all-ones sentinel on zero and stores size minus one
otherwise. The production prefix also establishes `IndexedStepReady` and
`IndexedStepEpochEncoded` for the first step, using the proved clean auxiliary bank
and all-ones quotient-length word.

This is an initial-state bridge. Complete packed-field encoding, preservation and
routing for all 1,620 reachable steps, the full EEA wrapper and aggregate resources
remain open. Circuit definitions and their resource certificates are unchanged.


### Complete initial packed work banks and metadata

`EEA/InitialPacked.lean` proves that both entire work-bank bit strings equal the
canonical `paperInitial` field concatenations, using the width from `packedView`.
The proof includes the Work1 separator and guard bit, the empty quotient, and all
leading zeros beside the Work2 zero coefficient. A second theorem connects both
phase bits, sign, iteration parity and all four length/shift words to the same
logical initial state. Zero length and shift retain the all-ones sentinel.

Together with `InitialEncoding`, this closes the initial packed-state connection
and its scratch/epoch premises. It does not establish preservation or routing for
subsequent microsteps; the full reachable-state invariant, EEA wrapper and remaining
phase deliverables are still open. No circuit definitions or costs changed.


### Decoder route bounds and remaining operational invariant

`EEA/RouteBounds.lean` proves that each unary decoder selects a leaf inside its
constructed source window for arbitrary states. The production scalar windows are
nonempty at all 1,620 indices, so `IndexedStepRoutesValid` is now unconditional
throughout the fixed schedule. This bounds selected labels; it does not identify
them with intended numeric values on arbitrary encodings.

`secp256k1ScheduleInvariant_of_epochTrace` derives scratch preservation and routing
along the full direct trace from initial scratch readiness plus the borrowed-epoch
condition at every prefix. Proving that remaining condition for the initialized
execution, and proving the arithmetic interpretation and terminal result, remain
open. No circuit definitions or costs changed.


### Borrowed-epoch restoration through the remainder prefix

`indexedStepRemainderPrefix_correct` proves that the actual A–C circuit is a literal
prefix of `indexedStepUnitary` and preserves both scratch readiness and epoch
encoding. A spills the borrowed epoch, B uses and restores the clean auxiliary
bank, and C restores the epoch/quotient pair. The C proof works for arbitrary
borrowed-clean states and obtains the terminal condition by frame preservation.

This closes the remainder-prefix preservation step. It does not cover D–H or prove
the epoch premise at all schedule prefixes; later phase/length consistency and full
arithmetic refinement remain open. Existing circuit definitions and costs are unchanged.

### Terminal EEA padding branch

`indexedStepRemainderPrefix_terminal_padding` derives terminal detection from
phase1=false and the all-ones remainder-length sentinel. The actual A–C circuit
then equals `terminalPaddingForwardState` with the terminal marker set for the
padding operation and cleared afterward. Disabled pre-shift and remainder
traversals are identity; epoch spill/restore and the intervening marker toggles
cancel on the complete state.

`indexedStepUnitary_terminal_padding` extends this result to the actual routed
A–H circuit and preserves scratch readiness and epoch encoding. It requires
phase 00 at entry, the remainder sentinel, and a nonzero extended shift counter
after the explicitly stated padding transition. The counter condition and the
phase/remainder premises still need proofs along reachable traces. Active-phase
arithmetic refinement and unconditional inversion remain open; this does not
close Phase 6 or change circuit definitions and costs.

The padding counter now has a numeric interpretation: its low word increments
modulo its width, and the epoch bit toggles exactly on low-word wrap.
`indexedStepUnitary_terminal_counter_correct` replaces the condition on the
padding result with an input-side modular bound on that extended counter. Proving
that bound and the phase/remainder encoding along reachable traces remains open.

`secp256k1TerminalScheduleInvariant` now proves the operational schedule invariant
for any production terminal suffix within the logical 596-step padding bound.
It starts from `Secp256k1TerminalState`, which records scratch/epoch readiness,
phase 00, the remainder sentinel and the existing `terminalShiftLow` /
`terminalShiftEpoch` formulas. Each actual routed step preserves this encoding;
the counter bound follows from those formulas, rather than being assumed at each
intermediate state. The active prefix must still establish the initial terminal
boundary, and its own arithmetic/epoch invariant remains open.

The active-tail composition theorem `indexedStepUnitary_active_tail_correct`
reduces the actual complete step to the phase update on the A–F prefix output
when that output has a non-sentinel remainder length, non-sentinel shift length
and a clear borrowed epoch. It also proves clean scratch and epoch encoding
after the step. The length conditions remain explicit; deriving them from
reachable active arithmetic states, including boundary transitions, is open.

The actual pre/post-shift circuits now have direct counter-word and numeric
transition theorems: an enabled shift increments when phase two is false and
decrements when phase two is true, modulo the physical counter width. Pre-shift
is enabled when phase one is false; post-shift is enabled when it is true.
The proofs include wraparound and disabled inputs. Connecting these per-block
transitions to the reachable active arithmetic encoding remains open.

The complete interval and coefficient-prefix arithmetic blocks now have frame
theorems: only the work banks and optional sign can change. The interval result
includes endpoint preparation and restoration; the coefficient scratch-cleanliness
result is derived from its stronger frame theorem. This establishes restoration
of the intervening length registers for future composition with the shift-counter
semantics. The reachable active prefix is still open.

`indexedStepShiftPrefix_counter` now derives the actual A–F counter transition
from the original input: with clean auxiliary wires and a non-sentinel remainder
length, it increments once when phase two is false and decrements once when phase
two is true, modulo the counter width. The proof composes inactive padding, the
two complementary shifts, and metadata restoration by the intervening blocks.
It does not assume the counter value after the prefix. Reachability of these input
conditions and the active boundary transitions remain open.

`indexedStepShiftPrefix_remainder` now preserves every remainder-length bit
across the actual A–F prefix from a clean, nonterminal input. The coefficient
block's stronger internal frame transports boundary words through arithmetic and
uses the prepare/restore round trip. Epoch preservation, reachable encoding and
active boundary transitions remain open.

`indexedStepShiftPrefix_clean` now returns the full auxiliary bank clear from a
clean, nonterminal input. In particular, the borrowed epoch remains zero because
the remainder condition disables block C's terminal restoration. Composing this
with the counter and remainder frames yields `indexedStepUnitary_active_correct`:
if the next modular counter value is not the sentinel, the actual full step is
its A–F output followed by the phase update, with readiness and epoch encoding
restored. All conditions are on the original input; certified route conditions
remain explicit. Reachable arithmetic encoding and counter-boundary transitions
are still open.

`eeaPreprocess_firstStep_correct` now instantiates the active-step theorem on the
concrete state established by preprocessing. The initial remainder length is
nonterminal, the auxiliary bank is clear, and the first prefix counter is zero.
The first complete physical step satisfies readiness and epoch encoding without
additional assumptions about its intermediate states. This bootstraps one step;
later reachable arithmetic and counter-boundary transitions remain open.

The active-step counter-sentinel exclusion is required only when `T % 4 = 0`.
At other indices the end-iteration block is absent, so the input-based result
covers all counter values. This removes an unnecessary restriction from both
active-step endpoints; the first-step instantiation now uses that absence
directly. Fourth-step boundary transitions and reachable arithmetic remain open.

`indexedStepUnitary_active_clean` now returns the entire auxiliary bank clear
from a clean, nonterminal input at every index, including fourth-step counter
boundaries. The end-iteration block preserves the borrowed epoch by restoring
its temporary complements; the remaining scratch follows the existing step
correctness theorem. Certified routes remain required. This cleanliness result
does not assert the next terminal encoding or logical arithmetic transition.

`indexedStepShiftPrefix_quotient_counter` now derives the actual prefix quotient
counter from the original phase bits: `(false,true)` increments, `(true,false)`
decrements, and equal bits preserve the word, modulo its physical width. The
proof tracks both counter wrappers and the intervening quotient swap, with all
other blocks framing the word. Input auxiliaries are clean and the input remainder
is nonterminal. Reachable quotient-length relations and terminal encoding remain
open; no circuit definitions or resource counts change.

`indexedStepUnitary_active_encoded` now preserves the next terminal encoding
from any clean, nonterminal input with certified routes, including fourth-step
boundaries. H preserves the quotient counter: when its all-ones guard holds,
the low quotient bit supplies the terminal marker; otherwise H is idle and the
remainder remains nonterminal. Together with full auxiliary cleanup, this closes
the active step's scratch and encoding obligations without a counter exclusion.
Reachable routing, logical arithmetic and the terminal-entry phase relation
remain open; no circuit definitions or resource counts change.

`eeaPreprocess_activeSchedule_correct` composes the active-step proofs across any
initialized production prefix of at most 1,620 steps. Its only trace condition is
that each step's input remainder length is nonterminal; the final output may be
terminal. It derives the operational schedule invariant, equality of the actual
coherent circuit with the direct routed trace, full auxiliary cleanup and final
epoch encoding. Production route ranges are supplied internally. Proving the
arithmetic stopping index and the terminal-entry phase/counter relation remains
open; the theorem does not assume epoch encoding at every intermediate state.

`eeaPreprocess_scheduleInvariant_of_terminalEntry` joins that active prefix to
the proved terminal padding suffix. For a stopping boundary between steps 1,024
and 1,620, the remaining assumptions are nonterminal earlier inputs and the four
entry facts: phase 00, terminal remainder length and a zero shift encoded as 511.
All scratch and epoch premises throughout the full schedule are derived. These
entry facts and the stopping boundary still require arithmetic refinement; this
is a conditional operational theorem, not a completed inverse-arithmetic proof.

`rightLengthXorWrite_firstSet` gives the actual grouped right-length writer an
arithmetic interpretation: with its control enabled, it XORs the encoded length
of the first set position in the decoded range into the arbitrary target word.
An all-zero range contributes the all-ones sentinel. The proof telescopes the
source's adjacent XOR constants under prefix-zero flags and composes the existing
gate theorem; dirty-bank and scratch restoration remain supplied by that theorem
family. This closes the local lower-writer interpretation. Relating its decoded
range to reachable packed arithmetic, and the corresponding upper writer, remain
open; circuits and resource counts are unchanged.

`highestPositionXorWrite_lastSet` gives the actual grouped upper writer the
matching arithmetic interpretation: it XORs the truth-minus-one encoding of the
last set label into the arbitrary target, or the all-ones sentinel for an empty
set of bits. The proof reverses the zero-flag telescope and checks the masked
subtraction identities at every width, including zero and one. Both local length
writers now have set-position semantics. Their composition with consistent
reachable work-bank and metadata encodings remains open.

`swapWorkAndLengthUnaryShared_lengths` composes both interpreted writers through
the actual enabled work-swap/length-update circuit. When the old metadata matches
the decoded lengths of the old work banks, the first XOR clears each old length
and the second writes the decoded length of its swapped bank. The theorem handles
all-zero sentinels and keeps the existing layout, route and readiness premises.
Proving that reachable packed arithmetic satisfies the old-metadata consistency
premises remains open; no circuit or resource definition changes.

`swapWorkAndLengthUnaryShared_bitLengths` expresses the actual metadata replacement
using ordinary binary lengths. The upper range is read little-endian and includes
its leading window offset; the lower range is read big-endian and includes omitted
trailing positions. Both zero words encode length zero through the all-ones
sentinel. The old consistency premise is now arithmetic rather than a first/last
list-index expression. Connecting these masked ranges to the evolving packed EEA
values remains open.

`endIterationUpperRangeBits_slice` and `endIterationLowerRangeBits_slice` identify
both masks with contiguous work-register slices and their zero padding. For a
positive, in-bounds label window containing the split boundary, the upper mask
keeps labels up to that boundary and the lower keeps labels from it onward.
Their numeric corollaries erase the padding in the respective little-/big-endian
orientations. These exact slice identities connect the preceding binary-length
formulas to work-register positions; reachable packed-value consistency still
requires the arithmetic invariant.

`endIterationUpperRangeBits_extract` and `endIterationLowerRangeBits_extract`
replace the selected slices with division and reduction modulo powers of two of
the complete packed work word. The lower formula reads that word big-endian and
uses the omitted suffix length as its division offset. Generic fitting-slice
lemmas cover zero-width extraction as well. The range values are now explicit
numeric fields of the bank; proving their evolving logical EEA interpretation
and consistency with the stored metadata remains open.

`packedWork1_decode` and `packedWork2_decode` recover all five logical values
from the canonical concatenated bank representations by numeric field extraction,
and prove the bank lengths equal their declared width. The first bank includes
the separating guard bit and the big-endian quotient/remainder fields; the second
bank is explicitly unrotated. Field-capacity bounds remain premises. These results
interpret the representation already established at initialization; preservation
through the bit-serial trace and the second bank's rotation remain open.

`controlledRotateLeftOne_numeric` and `controlledRotateRightTwo_numeric` bind the
actual controlled rotation circuits to numeric field exchange in a little-endian
packed word. Empty and short registers are covered, including the right-by-two
identity for widths at most two. `packedRotation_roundTrip` proves a normalized
inverse rotation recovers the complete word, so canonical field decoding can be
applied after undoing a stored shift. This establishes rotation semantics; the
reachable relation between the shift metadata and the packed EEA fields remains
open.

`preShiftUnitary_work_bits` and `postShiftUnitary_work_bits` give the combined
work-bank action of the actual shift wrappers. The enabled phase rotates left
when phase two is false and right when phase two is true; the pre-shift is enabled
by phase one being false and the post-shift by phase one being true. The proof
composes the source's left-one/right-two sequence and proves counter updates and
scratch marking do not alter the work bank. Together with the existing counter
semantics, this aligns the physical rotation direction with the counter update;
relating the encoded counter to a reachable logical shift remains open.

`preShiftUnitary_shiftEncoding` and `postShiftUnitary_shiftEncoding` preserve one
logical shift across the actual rotated bank and its truth-minus-one counter.
For an enabled wrapper, the bank remains the same canonical word rotated by the
updated shift, and the counter encodes that same bounded value. Decrement requires
a positive shift; increment requires the successor to fit the counter. Nonempty
work/counter registers and the old paired encoding are explicit premises. This
closes local shift-encoding preservation under those bounds, including zero's
all-ones sentinel; deriving the bounds and paired encoding along the complete EEA
trace remains open.

`controlledWindowRipple_arithmetic` proves the actual two-pass controlled ripple
adds or subtracts the addend and incoming carry modulo the target width, read in
big-endian physical order. Disabling the control leaves the target unchanged.
Every wire outside the target is restored, including the addend, arbitrary carry
and clean scratch. The proof binds both complete passes to a Boolean word
recurrence, then derives the arithmetic with carry/borrow conservation. Besides
the existing per-lane layouts, global data-register non-aliasing is required.
This closes the uniform-control ripple core's arithmetic interpretation; the
interval's changing unary accumulator, endpoint preparation and sign update
remain to be composed into the remainder-trial theorem.

### Prepared interval endpoint arithmetic

`prepareIntervalEndpoints_arithmetic` binds the literal preparation circuit to
`left = T + Q + 2 - offset` and `right = n + 3 - shift - offset`. The incoming
length and shift words use `truthMinusOneValue`, including its zero sentinel.
Nonnegative, fitting output indices suffice; intermediate modular wraparound
is allowed. The theorem also preserves the T word, cleans the scratch and carry,
and restores every wire outside the two endpoint words. The shared inverse
Cuccaro numeric lemma moves unchanged from TBoundary to WordNat.

Reachable states must still establish the metadata and output-bound premises;
composing the changing interval control with the ripple arithmetic remains open.

### Inclusive control at interval leaves

`intervalFirstLeaf_inclusive` and `intervalSecondLeaf_inclusive` bind each actual
source leaf to a ripple cell controlled by `enabled && (L ≤ label ∧ label ≤ R)`.
They also prove the next accumulator phase and the complete state action. The
source's masked zero leaf and shared dynamic control wire are supported.
Endpoint-match and incoming accumulator predicates remain explicit premises;
the decoder traversal and scan induction must establish them for the full interval.

### Both interval decoder banks

The existing quotient tree projection and source-built routing proof now support
either endpoint bank. `intervalTree_routeResidues` and `intervalTree_routeLabels`
identify both projected main-tree routes from their numeric words, under explicit
index-width and label-membership conditions. `intervalTree_singleton_route` covers
the source's singleton main tree without any endpoint-value restriction. The
quotient circuit retains its original first-bank projection. These are decoder
selection facts; the actual traversal must still establish each dynamic control
and the accumulator invariant used by the inclusive leaf theorems.

### Synchronized logical traversal

`run_dualUnaryActionUnitary_as_runLogicalTree` proves the actual dual traversal
equals a source-ordered execution on Boolean endpoint pulses with frozen index
bits. Its complete-state equality restores both path stacks and the possibly
shared root controls. A caller-selected clean leaf-scratch interface is preserved
throughout; physical/logical leaf simulation is required only when that scratch
is clean. The leaf simulation and decoder-frame premises remain explicit.
Instantiating them for interval cells and reducing the logical scan to arithmetic
remain the next composition steps.

### Routed-label scan

`run_dualUnaryActionUnitary_as_routedFold` reduces the same physical decoder
circuit to a fold over its actual visit order. Each Boolean pulse is the enabled
root control conjoined with equality to that bank's routed label. Duplicate-free
labels are explicit, and the complete frame and clean-scratch premises are
inherited from the logical-traversal theorem. The interval-cell instantiation
and arithmetic interpretation of this fold remain open.

### Concrete interval ripple scans

`run_intervalFirstTraversal_as_routedFold` and
`run_intervalSecondTraversal_as_routedFold` instantiate the decoder theorem for
the actual interval circuits, in decreasing and increasing visit order respectively.
Their logical cells retain the source zero-leaf mask, endpoint XOR switches and
ripple operations. The complete-state equalities require the existing traversal
layout, unique labels, clean path stacks and clean cell scratch; no abstract leaf
simulation premise remains. Decoder controls are selected from the decoder wires,
while the preserved interface additionally contains scratch. Numeric accumulator
induction and the arithmetic meaning of the entire scan remain next.

### Inclusive control across the scan

`run_intervalFirstTraversal_inclusiveScan` and its second-pass counterpart
replace every cell's accumulator-dependent control with the fixed inclusive
predicate `enabled && decide (L ≤ label ∧ label ≤ R)`. Their complete-state
fold equalities also establish the outgoing accumulator boundary. The proof
covers both traversal directions and arbitrary carry/data states, retaining the
source zero-leaf mask. The actual tree must have the stated consecutive labels;
the incoming accumulator and numeric interpretation of the effective endpoint
pulses remain explicit premises. Arithmetic fusion of the two passes and
establishing these endpoint premises in the enclosing interval block remain next.

### Numeric endpoint selection

`intervalTree_numericEndpointPulses` derives both effective decoder pulses from
the endpoint register values, including singleton main trees and the special top
endpoint. The source bitwise condition implies a power-of-two top lane; its high
bit suppresses exactly the aliased zero route. The two `numericScan` corollaries
instantiate the inclusive scan with the actual interval tree and existing
`IntervalLayout`. They require ordered endpoints within the physical lane bounds,
clean path/cell scratch and the incoming accumulator boundary. No separate route
or pulse interpretation premise remains. Initializing that boundary in the full
interval block and fusing its two passes into arithmetic remain next.

### Top-lane accumulator boundaries

`intervalTopFirst_accumulatorBoundary` proves that the actual separate top-lane
operation initializes the accumulator boundary required by the decreasing scan,
starting from a zero accumulator. `intervalTopSecond_accumulatorClean` proves
that its counterpart consumes the increasing scan's outgoing boundary and
restores the accumulator to zero. These results use numeric equality of bounded
endpoint words, their order and lane bounds, the physical layout and clean
comparison scratch. They cover special and ordinary windows. Composition through
the full prepared interval block and arithmetic fusion remain next.

### Complete interval numeric scans

`run_intervalAddSubBody_numeric` identifies the actual interval body with two
fixed numeric inclusive scans, retaining the actual separate top operations and
sign update. Endpoint and control preservation carries the original values
through both scans; the first top operation and first scan supply the incoming
accumulator boundaries. No separate pulse or scan-accumulator premises remain.
`run_intervalAddSubUnitary_numeric` includes actual endpoint preparation and
restoration, assuming the prepared endpoints are ordered and in range.
Arithmetic fusion and deriving those endpoint conditions from reachable metadata
remain open.

The separate top-lane circuits also have complete-state inclusive cell semantics:
`run_intervalTopFirst_inclusive` and `run_intervalTopSecond_inclusive` use the
same numeric control as ordinary lanes. Their accumulator boundary hypotheses
are the values established by the preceding top/scan results. These theorems
cover special windows; ordinary windows have no separate top operation.
Combining all lanes into one arithmetic interpretation remains open.

### Arithmetic of a contiguous ripple mask

`maskedRippleWords_fusion` proves the two passes with a distinct Boolean control
per bit restore the addend and incoming carry. Disabled first-pass writes are
retained and cancel in the matching second pass. `maskedRippleWords_interval`
proves a contiguous enabled slice leaves both outside slices unchanged;
`maskedRippleWords_interval_value` derives modular addition/subtraction on that
slice, including the input carry. The existing uniform ripple arithmetic proof
is reused. Connecting these word-level passes to the complete physical interval
body remains open.

`maskedRippleFirstState_words` and `maskedRippleSecondState_words` connect
per-bit masked ripple updates on distinct wire lists to the word-level passes.
`maskedRippleState_fusion` derives the fused target word and restores every
wire outside that target list, including the addend and arbitrary incoming carry.
These are wire-state semantics, with no additional circuit introduced. Matching
the source interval traversal and its accumulator writes to these passes remains
the next connection.

`intervalFirstInclusiveFold_words` and `intervalSecondInclusiveFold_words`
connect the source numeric inclusive-cell folds to those masked word passes.
Their accumulator updates do not affect target/addend reads or carry under
global wire separation. `intervalInclusivePair_fusion` gives the fused word
and restoration outside the target list plus accumulator. The complete source
body still needs its separate top operations and intervening sign update
combined with these folds before claiming full interval arithmetic.

### Complete physical interval body word semantics

`run_intervalAddSubBody_words` combines the actual separate top operations,
source main scans and intervening sign update. Its target word equals the
masked ripple arithmetic result; the addend and incoming carry are restored.
The optional sign update XORs the first pass's outgoing carry/borrow.
The theorem derives data-bank separation from `IntervalLayout` and assumes
clean top scratch, a zero initial accumulator, and ordered bounded numeric
endpoints. Endpoint preparation/restoration, reachable metadata conditions and
the complete packed EEA arithmetic connection remain separate boundaries.

### Complete interval body selected-slice arithmetic

`run_intervalAddSubBody_value` now derives modular addition/subtraction on the
numeric interval selected by the endpoint words, including the incoming
carry/borrow. It applies to the actual body circuit with its control enabled,
both target banks and either sign-update setting. The proof decomposes the
bounded numeric mask into a disabled prefix, enabled slice and disabled suffix,
then uses the existing masked ripple arithmetic and complete-body word theorem.
The physical layout, clean comparison scratch, zero accumulator and ordered
bounded endpoints remain explicit. Preparation/restoration and reachable-state
metadata still need connection to this arithmetic theorem.

### Complete interval arithmetic through endpoint restoration

`run_intervalAddSubUnitary_value` carries selected-slice modular arithmetic
through the actual endpoint preparation and restoration circuits. The selected
endpoints are those computed by preparation; their order and bounds remain
explicit. Ready scratch supplies zero carry, and physical support proves that
both endpoint transformations preserve the data banks and control. This is the
complete interval circuit, while reachable metadata and its relation to the
packed EEA step remain separate obligations.

### Interval arithmetic in logical length coordinates

`run_intervalAddSubUnitary_logicalValues` reuses the existing endpoint arithmetic
proof to derive full-circuit modular slice arithmetic with
`L = T + Q + 2 - k` and `R = n + 3 - shift - k`. Stored words encode the logical
lengths as truth-minus-one, including wrapped zero encodings. Explicit endpoint
bounds and order remain required; establishing the encoding and these bounds
for reachable packed EEA states is the next obligation.

### Complete interval word and sign result

`run_intervalAddSubBody_slices` and `run_intervalAddSubUnitary_slices` now specify
the entire target word as its original prefix, the arithmetic result on the
selected slice, and its original suffix. They also restore the addend and give
the optional sign XOR from the selected operation's outgoing carry/borrow.
Both control values are covered; the full interval starts with ready scratch.
The numeric body theorem now derives from this common word decomposition.
Prepared endpoint bounds/order and reachable packed-field interpretation remain
explicit proof boundaries.

### Remainder interval in full work-bank coordinates

`run_remainderInterval_logicalValues` lifts the actual indexed remainder view
from its local window to the original full work banks. The one-based window
offset cancels, so the selected field begins at zero-based index `T + Q + 1`,
immediately after the coefficient and quotient prefix. Encoding and endpoint
bounds/order remain explicit. This proves arithmetic for the actual isolated
interval used in Block B; control preparation and the full block's logical
remainder relation still require composition.

### Actual Block B1 subtraction arithmetic

`run_blockB1Forward_interval` reuses the existing complete-state control proof
to identify the actual interval call and subsequent control cleanup.
`blockB1Forward_logicalValues` proves modular subtraction of the aligned work2
field from work1 when phase1 is false and the divisor is nonterminal, with the
entire auxiliary bank clean afterward. Encoded logical lengths and endpoint
bounds/order remain explicit. The sign-adjustment/addback blocks and the full
logical remainder update still require composition.

### Actual Block B3 conditional addback arithmetic

`run_blockB3Forward_interval` identifies the actual source addback interval and
control cleanup. Its enable condition is `!phase1 && !(phase2 && sign)` together
with a nonterminal divisor. `blockB3Forward_logicalValues` proves addition modulo
the selected field width under that condition, returning all auxiliary wires
clean. Encoded lengths and endpoint bounds remain explicit. The sign adjustment
and full Block B composition remain next.

### Complete Block B control composition

`run_blockB2_sign` proves that the actual B2 circuit changes only the sign,
flipping it exactly when phase one is off, phase two is on, and the divisor is
nonterminal. `run_blockBForward_intervals` composes the actual B1 subtraction,
B2 sign update, and B3 addback into one complete-state equality and proves
auxiliary cleanup for the entire block. The interval calls are concrete source
circuits. A combined logical remainder formula and reachable-state bounds
still require proof.

### Unsigned borrow in actual Block B1

`uniformRippleExpectedWords_sub_borrow` identifies the outgoing subtraction
flag with unsigned borrow, including incoming borrow. The interval and logical
endpoint theorems propagate this result to `blockB1Forward_logicalBorrow`: in
the active nonterminal phase, sign is XORed with the comparison of the aligned
work1/work2 field values, and aux is clean afterward. Logical endpoint preparation
is shared with the existing numeric theorem. The combined conditional remainder
formula still requires carrying the preserved metadata through the three blocks.

### Complete interval and Block B frame

`intervalAddSubUnitary_preservesOutsideTarget` lifts the existing interval-body
frame through endpoint preparation and restoration: only the selected work bank
and sign may change. It requires a valid physical layout and clean scratch, but
no numeric endpoint bounds. `blockB1Forward_frame` and `blockBForward_frame`
propagate this to the actual source blocks, restoring the addend and all metadata.
This supplies the preserved encoding inputs needed for the combined remainder
formula; reachable-state bounds remain outstanding.

### Complete Block B active-phase arithmetic

`blockBForward_activeArithmetic` derives the complete source block from its
initial state with phase one off, sign zero, and a nonterminal divisor. With
phase two off, the aligned work1 field is unchanged and sign records `x < y`.
With phase two on, it becomes `if y ≤ x then x - y else x`, and sign records
successful subtraction. All auxiliaries return clean. Intermediate metadata,
addend values, sign updates, and conditional addback are derived. Initial
logical encoding and endpoint bounds remain explicit. Connecting these fields
to the packed logical remainder and proving reachable-state bounds remain open.

### Logical field reconstruction in the full remainder bank

`run_intervalAddSubUnitary_logicalSlices` gives the complete interval words and
sign for either target, operation, and control value under logical endpoint
encoding. `run_remainderInterval_logicalSlices` translates the actual certified
window back to work1: its coefficient prefix ends at `T+Q+1`, its selected field
is replaced by the ripple result, and its suffix begins at `n+3-shift`. The
physical frame preserves the prefix before the window. Packed remainder value
reconstruction and reachable-state bounds remain outstanding.

### Complete Block B word and field frame

`blockB1Forward_fieldFrame`, `blockB3Forward_fieldFrame`, and
`blockBForward_fieldFrame` preserve both neighboring work1 slices in every
phase under encoded endpoint bounds. Metadata needed by B3 is transported
from the initial state through the physical frame. `blockBForward_activeWord`
combines this with the active-phase arithmetic, giving the entire output bank
as original prefix, fixed-width binary result, and original suffix. Packed
remainder decoding and reachable-state invariants remain next.

### Decoded full remainder effect of Block B

`blockBForward_remainderValue` decodes all work1 remainder bits after the
coefficient prefix. It proves conditional subtraction by the aligned work2
field times `2^shift`, or preservation in the comparison phase. The proof
retains the low bits, derives the full-width comparison from their bound, and
uses the actual complete Block B word theorem. Identifying the aligned work2
field with the canonical rotated divisor and proving reachability remain open.

### Canonical rotated divisor and actual packed remainder update

`packedRotatedDivisor_value` identifies the selected work2 field after circular
rotation as the logical divisor: the coefficient fit bound forces intervening
bits to zero. `blockBForward_packedRemainder` applies this to actual Block B
with canonical input bank words and derives conditional subtraction of
`rPrime * 2^shift` from the logical remainder. Encoding, nonterminal phase,
initial sign, endpoint, and packing fit obligations remain explicit. Establishing
these obligations for reachable microsteps remains outstanding.

### Canonical first-bank preservation through Block B

`blockBForward_packedWork1` reconstructs the complete canonical output work1
word with unchanged coefficient, separator, and quotient fields and the updated
logical remainder. It combines the actual field frame with decoded arithmetic
and equal-width encoding uniqueness; output fit is derived from the word length.
Initial packing and endpoint assumptions remain explicit, so this closes the
first-bank preservation step without claiming a reachable-state invariant.

### Canonical Block B comparison and combined contract

`blockBForward_packedSign` identifies the final sign as the logical shifted-
divisor comparison XOR phase2, deriving the full comparison from the high field
and bounded low bits. `blockBForward_packedContract` combines the canonical
output work1 word, sign, complete external frame, and clean auxiliary bank for
the same actual source circuit. Initial encoding, packing fit, endpoint and
active-phase assumptions remain explicit; whole-microstep reachability is open.

### Logical quotient/sign selector boundary

`run_quotientSwapUnitary_logical` derives the selector label `T+Q+1` from
truth-minus-one length words, including zero logical lengths. The actual
selector swaps sign with this label and restores its temporary preparation.
`run_indexedQuotientSwap_logical` cancels the one-based window offset to locate
full-bank work1 index `T+Q`. Integrating Block D's counter updates and deriving
reachable selector bounds remain outstanding.

### Nonterminal terminal-restoration composition

`blockCForward_nonterminal` proves complete-state identity for actual Block C
on clean, nonterminal inputs. `blockBCForward_eq_blockB` derives the needed
cleanliness and divisor-length preservation from Block B's external frame,
so its full canonical output contract carries through the appended Block C.
This bridge applies to every phase and does not assume logical endpoint bounds.
Reachable-state bounds and Block D counter/selector composition remain open.

### Phase-controlled quotient routing

`blockD2Forward_logical` connects the actual middle component of Block D
to work1 index `T+Q`. It swaps that bit with sign exactly when phase1 and
phase2 differ, and restores every other wire, including the prepared control.
The source Block D now names this unchanged substream explicitly. Its length
encodings describe the state at the selector boundary; connecting the preceding
increment and following decrement, and deriving reachable bounds, remain open.

### Logical quotient counter boundaries

The named source `blockD1Forward` and `blockD3Forward` retain the unchanged
increment/decrement streams inside Block D. Their contracts expose the updated
lengthQ bits, complete external frame, and clean auxiliaries at each boundary.
`blockD1Forward_logicalLength` derives the logical increment even at length zero;
`blockD3Forward_logicalLength` derives the decrement when the enabled phase has
a positive logical length. The latter positivity premise remains explicit.
Composing these interfaces with the selector and deriving their reachable-state
conditions remain the next boundary.

### Complete logical quotient block

`blockDForward_logical` composes the actual increment, phase-controlled selector,
and decrement. It reconstructs the final lengthQ word and describes every
other wire by the exact sign/work1 boundary swap, with clean auxiliaries.
The selector uses the length after the first counter; its bounds are supplied
at that intermediate logical value. Enabled-decrement positivity is transported
through the unchanged phases. Canonical work-bank repacking and reachable-state
proofs remain open.

### Canonical quotient push/pop packing

`blockDForward_pushPacking` and `blockDForward_popPacking` interpret the actual
complete Block D on a packed coefficient/separator/quotient/remainder bank.
Phase 2 appends the sign bit to the quotient and clears the sign when the high
remainder bit is zero. Phase 3 extracts the last quotient bit into a clear sign,
shrinks the quotient and extends the remainder with a zero high bit. Both prove
the exact bank word, the new quotient value bound, the lengthQ encoding, the
outside frame and clean auxiliaries. Input packing, quotient/remainder bounds,
phase conditions and selector bounds remain explicit; reachable-state induction
and the coefficient Block E composition are subsequent boundaries.

### Inclusive coefficient-prefix scans

The actual increasing and decreasing coefficient traversals now have complete-state
contracts with a numeric inclusive prefix mask. The prepared boundary is routed to
its exact label; the increasing pass clears its seeded accumulator just after that
label, while the decreasing pass restores the accumulator to the external control.
The proof derives physical lane separation from `CoefficientPrefixLayout`. This
connects the source pulse order to arithmetic-enabled cells; whole-prefix numeric
word composition, Block E and reachable-state boundary conditions remain next.

### Coefficient scan word semantics

Both actual coefficient scans now return the corresponding masked ripple word
triple (target, addend and carry), deriving word-level physical separation from
the coefficient layout. The logical pair of prefix folds fuses to the existing
masked arithmetic result, restoring the addend, carry and every wire outside
the target and accumulator. Reversing coefficient lanes aligns their physical
little-endian order with the masked word model. Composition around the optional
sign update and boundary preparation, and the final numeric Block E contract,
remain subsequent work.

### Complete prepared coefficient-prefix word contract

`run_coefficientPrefixUnitary_words` composes the actual seed, increasing scan,
optional sign update, decreasing scan and cleanup. It proves the masked arithmetic
output word, restored addend, sign XOR with the arithmetic carry/borrow, clean
scratch and outside frame. Routing and scratch conditions are transported across
the intermediate states from physical layout separation. The boundary range is
still explicit. Numeric prefix-value specialization, Block E boundary preparation
and phase controls, and reachable-state invariants remain subsequent work.

### Prepared coefficient-prefix arithmetic

`run_coefficientPrefixUnitary_prefix` identifies the complete circuit's target word
as the updated little-endian low prefix followed by the unchanged high suffix.
It retains the restored addend, optional sign carry/borrow, scratch cleanup and frame.
`run_coefficientPrefixUnitary_value` derives enabled addition/subtraction modulo
`2^(boundary-k+1)` on that prefix. The modulus is the selected prefix width, not
the full bank width. Both results use the same `coefficientPrefixUnitary` term.
Block E preparation and phase controls, reachable-state invariants and aggregate
resources remain open; the prepared boundary must still lie in `k..K`.

### Block E subtraction enable and boundary preparation

The actual source prefix is now named `blockEPrepareForward`. Its contract derives
the subtraction control from the phase/sign bits, restores the temporary flag and
block scratch, and computes the prepared pair of boundary words. The full state is
preserved outside the control and those two words. The reusable control sandwich
allows an arbitrary initial control, so its XOR contract also supports cleanup.
This does not yet compose Block E's arithmetic scans or prove that reachable states
supply an in-range prepared boundary.

### Logical coefficient-boundary values

`prepareLatestPaperTBoundary_arithmetic` and `blockEPrepareForward_arithmetic`
interpret the same preparation circuits in logical lengths. The stored modular
truth-minus-one encoding yields endpoints `T+1` and `n+3-R-S`; phase 2 selects
their order. Logical zero is included. Nonnegativity and word-capacity bounds
remain explicit, as does the later obligation that the selected endpoint lies
inside the active coefficient window. The Block E theorem retains its control,
frame and scratch conclusions.

### Block E subtraction and control cleanup

`blockESubtractForward` names the actual source prefix through preparation,
subtraction and the repeated control sandwich. Its word theorem computes the
selected low-prefix subtraction, preserves the high suffix and addend, preserves
the sign, and proves that control and temporary flag finish false with block
scratch clean. Outside the control, sign and coefficient banks, the state agrees
with the prepared state, retaining its boundary words and phase flags. The cleanup predicate is derived from phase/sign preservation
across the scan. The prepared input-word boundary must still lie inside the
certified coefficient window. The following sign flip, addition and boundary
restoration remain the next composition boundary.

### Block E addition and boundary restoration

`blockEFinishForward` names the remaining source suffix. Its word contract derives
the low-prefix addition controlled by phase 1, high-bit and addend preservation,
and the sign flip followed by the arithmetic carry XOR. The final control is false
and block scratch is clean after the actual boundary restore. Both half-contracts
now frame the actual local coefficient windows, preserving unused work bits. The prepared boundary
must lie in the certified coefficient window. Composing the two arithmetic halves
and discharging their logical window conditions remains the next boundary.

`blockEForward_words` composes both actual Block E halves on the same prepared
boundary. It states the subtraction and subsequent addition words, the final
phase/carry sign update, preserved addend, shared-scratch readiness and complete
metadata frame. The prepared endpoint range is still an explicit premise; this
is the arithmetic composition, not a reachable-state range proof.

`blockEForward_arithmetic` specializes that same circuit to truth-minus-one
encoded logical lengths. Its endpoint is `T+1` when phase2 is false or `n+3-R-S` when
phase2 is true, with capacity, nonnegative subtraction and window membership explicit.

### Numeric coefficient update

`blockEForward_coefficient_value` interprets the complete source circuit using
ordinary arithmetic on the selected low prefix. It first subtracts modulo the
prefix width when the subtraction predicate holds, then adds modulo that same
width when phase1 holds. The final sign is the old sign XOR phase1 XOR the
explicit addition-overflow predicate. High bits, the addend, metadata and shared
scratch are retained. Boundary membership remains explicit; interpretation of the neighboring packed
fields and reachable-state induction remain subsequent work.

`blockEForward_coefficient_packed` reconstructs the exact output as the canonical
little-endian coefficient prefix followed by the original high fields. It derives
that packing from the numeric result and fixed physical word length, preserving
the same sign, addend, readiness and metadata guarantees.

### Complete physical coefficient banks

The complete Block E frame now excludes only the local coefficient windows and
sign; it explicitly preserves every work bit outside those windows. The stronger
frame propagates through the logical-length, numeric and canonical-prefix
contracts. `blockEForward_workBanks` reconstructs the entire target bank as its
original low neighboring bits, the canonical updated coefficient prefix and its
original high fields. The entire addend bank is unchanged. Certified boundary
membership remains explicit; reachable packed-state refinement is still open.

### Logical coefficients in the physical windows

`blockEForward_packedCoefficients` now decodes both selected windows from
the logical coefficients `t` and `tPrime`, including the latter bank's rotation.
The actual complete Block E circuit updates the canonical selected bits using
those numeric slices, preserves the entire addend bank and all neighboring
bits, and gives the sign overflow and clean-scratch guarantees. Coefficient
fits, selected-field spans and prepared boundary membership remain explicit.
The canonical reconstruction below now undoes the rotation algebraically.
Deriving these premises from reachable states remains subsequent work.

### Canonical updated coefficient and divisor preservation

`blockEForward_canonicalCoefficient` expresses the actual output bank as the
rotation of an updated canonical coefficient followed by the unchanged divisor
bits. For selected bit offset `pos = shift + (window.start - 1)`, the updated coefficient is its
original low field plus the new field at `pos` plus its original high field.
The theorem also proves the new coefficient fits its field, preserves the
complete addend bank, and retains the sign, readiness and local frame facts.
The logical packing and selected-span premises still require reachable-state
induction; this theorem does not claim full EEA refinement or stopping.

### Canonical coefficient contract from logical length metadata

`blockEForward_logicalCoefficient` derives the selected endpoint from the
truth-minus-one encodings of `lT`, `lRPrime` and the shift counter. It selects
`lT+1` or `n+3-lRPrime-shift` according to phase 2, then applies the complete
canonical coefficient theorem. The separate equation relating prepared circuit
words to an abstract boundary is no longer a caller premise. Endpoint capacity,
nonnegative subtraction, window membership, input packing and selected-field
spans remain explicit and still need to follow from reachable-state induction.

### Phase cases of the complete coefficient update

`blockEForward_coefficientPhaseCases` reduces the subtraction/addition pair to
one canonical field update. The coefficient changes only when phase 1 is set,
phase 2 is clear and the input sign is set; otherwise it is unchanged. The sign
is the corresponding addition carry or subtraction comparison, with the source
sign toggle included. `blockEForward_inactive` proves the entire physical state
is unchanged when phase 1 is clear, using only layout and scratch readiness;
it needs no boundary-membership or logical-packing assumptions. The active
logical contract retains the explicit metadata, capacity and span premises.

### Ordinary shifted coefficient arithmetic

`blockEForward_coefficientOrdinary` connects the actual stage to Algorithm 3's
ordinary `tPrime + 2^shift*t` update and full-value `tPrime < t*2^shift`
comparison. It derives the zero-based field offset from the certified
coefficient window's start at one. Selected-addend and coefficient fits, plus
a conditional bound preventing addition overflow, are explicit; the retained
canonical fit, divisor/addend preservation, sign, readiness and local frame all
belong to the same actual circuit. Deriving these bounds along reachable
microsteps remains necessary before unconditional inversion can be claimed.

### Quotient extraction composed with ordinary coefficient arithmetic

`blockDEForward_coefficient` proves the actual concatenated D/E circuit in the
coefficient phase. It consumes the low packed quotient bit, decreases its
length, preserves the remainder and addend, and conditionally adds `2^shift*t`
to `tPrime`. The result includes canonical banks, quotient metadata, sign,
coefficient/quotient fits and scratch readiness. Intermediate metadata and
readiness are derived using physical separation, rather than assumed by the
caller. Initial packing, route/span bounds and conditional no-overflow remain
explicit; the full reachable microstep invariant is still open.

### Post-shift composition after quotient/coefficient arithmetic

`blockDEFForward_coefficient` carries the actual D/E result through the source
post-shift. The canonical updated coefficient bank rotates by `shift+1`, and
the full truth-minus-one shift counter encodes that same value; coefficient
fit and indexed scratch readiness are retained. The D/E contract now also
exposes its complete frame outside quotient metadata, sign and the two work
banks. That frame supplies phase and counter preservation for the post-shift
handoff. Full shift encoding and increment capacity remain explicit initial
premises, in addition to the D/E bounds; reachable-state induction remains open.

### Coefficient accumulation invariant on the actual stage sequence

`blockDEFForward_coefficientInvariant` replaces the independent selected-fit
and no-overflow premises by `tPrime < 2^shift*t`. Together with the existing
addend bound, this derives the arithmetic preconditions and preserves the same
strict inequality at `shift+1`. It also preserves
`tPrime + 2^shift*t*q` as the quotient is consumed. This identifies the weighted
remaining contribution of the physical unweighted quotient prefix, while the
actual D/E/F circuit supplies the canonical coefficient and shift outputs.
Initial packing, routing/span bounds, phase and shift encodings remain explicit;
this is a coefficient-stage invariant, not yet a whole-loop invariant.

### Complete packed coefficient-stage result

`blockDEFForward_completeCoefficient` attaches the remaining quotient `q/2`
and length `lQ-1` to the actual final work bank and quotient word after post-shift.
The remainder and addend are preserved, the sign is cleared under the strict
coefficient bound, and the second bank and shift counter share `shift+1`.
The theorem retains coefficient/quotient fits, the accumulation invariant,
weighted conservation, readiness and the full frame outside the two banks,
quotient/shift words and sign. The post-shift frame is proved from its exact
state transition, including restoration of its temporary control. Initial
packing, phase and routing bounds still await whole-loop induction.

### Logical phase update from encoded lengths

`blockGForward_logical` identifies the entire state produced by the actual
phase-update block with the source Boolean transition on logical zero tests.
It derives these tests from bounded truth-minus-one encodings of the quotient
length, divisor length and full shift counter, including zero-width words when
the value bound permits them. The borrowed epoch is explicitly zero. Only the
three phase/sign bits are updated; the exact state equation preserves all other
wires, and indexed readiness is retained. The existing numeric all-ones lemma
is shared with terminal padding. These input encodings still need to be supplied
by composition and the reachable-state invariant.

### Phase transition after coefficient-bit consumption

`blockDEFGForward_coefficientPhase` composes the actual coefficient-stage
output with the phase-update circuit. With the initial strict coefficient
bound, sign is cleared before G and the advanced shift is positive. Thus G
sets phase2 and sign exactly when `lQ=1` and `lRPrime` is nonzero, while phase1
stays set. Its exact state equation preserves every other D/E/F output and
retains indexed readiness. Metadata and the zero epoch are derived from the
preceding frame and clean auxiliary bank. A representability bound for the
divisor length remains explicit with the existing initial encoding/routing
premises; A–C, H and whole-loop induction remain to be composed.

The coefficient phase also has a complete-state identity theorem for the actual
A–C remainder prefix: `indexedStepRemainderPrefix_coefficient_idle`. It requires
physical layout, clean auxiliary wires, phase1=true and phase2=false, with no
logical packing, capacity or endpoint-routing assumptions. The whole coefficient
microstep still needs the final H-stage composition.

`indexedStepUnitary_coefficientPhase` now composes A–H for the coefficient
microstep. The advanced positive shift disables H; both decoder-route bounds
are derived from the trees' label ranges, rather than assumed for an inactive
aggregate. The complete indexed circuit has the D/E/F physical result with the
last-quotient-bit phase/sign transition and readiness. Initial packing, capacity,
selected-window and strict coefficient bounds remain explicit. Other phase
refinements and a reachable whole-loop invariant remain open.

`IndexedPackedState` collects the two canonical packed banks, four logical
metadata words, phase/sign/parity and clean auxiliary bank. The actual complete
coefficient microstep preserves this interpretation for `coefficientMicrostep`,
with quotient/coefficient capacity, strict coefficient bound and weighted
conservation proved together. The low shift-word encoding needed by boundary
preparation is derived from the full word by modular projection. Active-window
and arithmetic input bounds remain explicit; iterating this phase is the next
step toward reachable-state refinement.

`indexedScheduleUnitary_coefficient_packed` proves the actual consecutive
coefficient-phase schedule by induction, for any count up to the initial quotient
length. Intermediate packing, capacities and strict coefficient bounds are
derived from the initial arithmetic bounds and the schedule's layout/window
conditions. The theorem gives the quotient-length decrease and shift advance;
consuming the complete quotient leaves zero quotient and adds its full weighted
contribution to the coefficient. These initial schedule conditions still need to
be connected to the other EEA phases and the production reachable-state invariant.

The inverse canonical rotation stages follow the pinned greedy opposite permutation. Each
of the ten stages preserves the complete external frame and has 258 CCX, 516 CX, zero X,
1,806 T and at most 260 physical wires. Forward and inverse certificates share the literal
source permutation builder. The descending composition now restores its counter and rotates Work2 by the terminal padding,
preserving every external wire. Its same-circuit certificate is 2,620 CCX, 5,240 CX, six X,
18,340 T and at most 280 wires. The same inverse wrapper cancels forward canonicalization on every basis state, including
arbitrary scratch contents. The complete inverse EEA wrapper remains a separate boundary.

The adaptive source reverse postprocessing now restores Work1, undoes parity and epoch
compression, and reverses canonicalization. Its full-state cancellation theorem applies to
original valid inputs; composing it with the forward wrapper coherently returns the complete
terminal schedule state with normalized input-independent branch coefficients. The reverse
Algorithm-3 schedule, inverse preprocessing and Figure 15 composition remain open.


The explicit adaptive inverse indexed step now follows the existing inverse unitary
in source order, using the proved measurement-assisted phase, coefficient, and
remainder inverses. Its well-formedness and coherent equivalence hold on
`IndexedStepInverseAdaptiveInput`: five readiness conditions evaluated at the
actual preceding unitary prefixes. No reachable-state claim is hidden in these
conditions. Deriving them from the forward endpoint, composing the reverse
schedule, and undoing preprocessing remain open.

The explicit adaptive inverse schedule is now composed in descending index order,
including the 1,620-step secp256k1 instance. Physical well-formedness follows from
the per-index layout. Coherent equivalence with the existing reverse unitary
uses the actual-prefix inverse readiness predicate at every descending step;
this predicate still needs a reachable-state derivation before the adaptive
reverse can be applied unconditionally to the forward endpoint.

The literal inverse preprocessing is now proved: it clears the divisor-length
encoding and all-one length words, reverses centering, and restores the original
work-bank arrangement. The length initializer's XOR action yields full-state
cancellation; every adaptive reverse branch restores a valid original input
with a uniform positive amplitude. The same concrete program is well formed
and coherent on the actual image of preprocessing, and preprocessing followed
by its explicit reverse preserves every valid superposition. This closes
inverse preprocessing; deriving inverse EEA readiness from reachable forward
endpoints remains open before joining the complete inverse wrapper.


The complete adaptive EEA reverse now applies to every valid actual forward
output. All five per-step inverse readiness conditions are derived at their
actual prefixes from the forward state, and induction supplies them across all
1,620 descending steps. The literal reverse wrapper composes postprocessing
undo, this adaptive schedule, and inverse preprocessing. It restores every
original wire, and the actual forward/reverse pair coherently implements the
identity on all valid input superpositions with uniform normalized branch
coefficients. This closes the inverse-wrapper and reachable inverse-readiness
boundaries described above. Phase 8 still requires Figure 15 in-place arithmetic
composition and its resource certificates; Phases 9–12 remain open.

The Figure 15 workspace interface now relabels the actual adaptive EEA trees
onto the cleared data bank. The wire bijection exchanges 7–262 with 580–835
and fixes every other wire. A generic Kraus-branch transport theorem preserves
transcripts and the same normalized coefficients; well-formedness, T count,
measurement count, distinct-wire count, and complete forward/reverse coherent
identity are preserved. No swap gates are inserted. This is a composition
interface, not a complete in-place multiplication/division theorem or the
paper's aggregate 835-wire claim; those resource and arithmetic obligations
remain open.

The existing Horner multiplier and explicit inverse now expose coherent
contracts with one normalized coefficient list for all valid inputs. The
forward contract requires a clean accumulator and shared scratch plus a
canonical multiplicand; the inverse contract applies to the actual forward
image and restores the complete original frame. The same forward/inverse
program pair coherently implements identity. These facts supply the arithmetic
composition contracts for Figure 15; its intervening measurement/recomputation
schedule and full resource certificates remain open.

Both concrete Figure 15 adaptive source schedules are now assembled at
secp256k1 width, with physical well-formedness for every gate and measurement.
The initial 256-bit X-reset transcript selects a continuation containing the
intervening EEA/multiplication calls, Z corrections, explicit multiplication
inverse, and final physical swaps in source order. A generic adaptive
continuation theorem proves coherent correction when its phase-reconstruction
hypotheses hold. Establishing those hypotheses for these two concrete schedules
and deriving their aggregate resource bounds remain open; physical
well-formedness alone is not the arithmetic correctness claim.

The actual coherent EEA schedule now has a direct physical-support certificate:
`secp256k1EEAForwardUnitary_production_usesOnly` places every gate wire in
`List.range 580`, and `secp256k1EEAForwardUnitary_production_qubitCount` derives
at most 580 distinct qubits for that same circuit. The support witness also
proves complete external-wire preservation and dependence only on the allocated
input registers. These facts compose symbolic component bounds across all
1,620 steps; the complete adaptive wrapper and Figure 15 resource certificate
remain subsequent obligations.

The complete EEA output ideal now preserves every wire outside `List.range 580`
and depends only on its allocated input registers. `secp256k1EEAOutputIdealState_patchOutside`
commutes replacement of an external bank with preprocessing, the EEA schedule,
and all output corrections. `Secp256k1EEAInputValid_congrOn` preserves the clean,
nonzero canonical input contract under the same replacement. These facts supply
forward-image reconstruction for the reverse-wrapper contract used in Figure 15;
they do not yet prove its specific phase-reconstruction arithmetic or total resources.

The actual reverse wrapper now has a coherent contract whenever its allocated
registers match a valid forward output, without restricting the retained external
values. The proof constructs a valid original input with the same external frame,
then applies the existing exact-forward-image inverse theorem with its unchanged
normalized branches. Its full output restores the original EEA registers and
preserves the current external frame. The contract also transports to the actual
relabeled inverse borrowing Y, supplying Figure 15's retained-result inverse interface.

The concrete Figure 15 multipliers and both initial prefixes now have coherent
contracts on the stated clean/nonzero/canonical input domain. For division,
quotient accumulation followed by Y reset satisfies the actual relabeled
inverse's live-register contract. Its deterministic output restores every
original wire except retained quotient A and cleared Y. Recomputing Y proves
full bit equality with the original measured word, so the literal transcript-
selected Z correction produces exactly its measurement sign for every outcome.
The actual final three-CX swap stream exchanges A and Y with a complete frame
proof. The full continuation/measurement coherent composition and multiplication
reconstruction remain open, followed by aggregate resources.

The literal Figure 15 division now coherently implements one common linear map on all canonical Y and nonzero canonical X inputs with clean EEA work. The proof composes the actual adaptive inverse, recomputation, transcript-selected Z correction, inverse multiplication and final swaps with the 256-bit measurement/reset schedule. Its normalized branch coefficients are input-independent. The same output state puts Y/X modulo p in Y and restores every other wire, including the clean A bank. Multiplication reconstruction and aggregate resources remain open.

The literal Figure 15 multiplication now has the corresponding complete coherent contract: every transcript implements the same product map with input-independent normalized coefficients, Y contains X*Y mod p, and all other wires are restored. The proof uses the actual borrowed-Y forward and reverse EEA calls, establishes bit-exact reconstruction of the measured Y, and composes the selected Z correction with uncomputation and final swaps. Both concrete Figure 15 arithmetic contracts are proved; aggregate resource accounting remains open.

The complete Figure 15 circuits now have exact T-count and measurement composition equalities on their actual adaptive terms. Both EEA directions have finite-sum resource formulas, and the production 1,620-step schedules each measure exactly 5,278,832 times. This numeric certificate counts decoder labels symbolically before kernel evaluation; it does not enumerate measurement branches. Full numerical T totals, wrapper and Horner resource specialization, and aggregate adaptive physical support remain open.

Each actual Figure 15 Horner component, including inverse recomputation, now has proved counts of 7,773,731 T gates and 261,121 measurements on its actual banks. Both complete EEA wrappers measure 5,280,108 times, including preprocessing and parity correction. The complete division and multiplication circuits each have worst-branch measurement count 11,343,835. These are constructor-derived certificates on the same circuits as the coherent contracts; full numerical EEA T totals and aggregate adaptive physical support remain open.

Both actual 1,620-step adaptive EEA schedules now have constructor-derived worst-branch T count 122,179,575. The proof reduces the forward and reverse unitary blocks independently, counts interval/coefficient/quotient decoder labels symbolically, and kernel-checks the resulting integer sum. Complete-wrapper T specialization and the aggregate adaptive physical-wire bound remain open.
