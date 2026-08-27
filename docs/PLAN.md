# ShorECDLP

A minimal, **ecdsa.fail-style verification infrastructure** for quantum resource-estimate
submissions, together with **one super-naive Shor/ECDLP submission** that fills it.

Repo: https://github.com/VerifiedQC/ShorECDLP. Toolchain: `leanprover/lean4:v4.28.0`,
Mathlib pinned. Curve: secp256k1 (Bitcoin).

**Status snapshot.** This document reflects the root-reachable source in this tree, refreshed
against code baseline `main@ca058b7d`. A `✓` below means the component is implemented, imported by
`ShorECDLP.lean`, and covered by the repository verifier. “Planned” means that no implementation
is present; a partial milestone lists its exact landed and open boundaries.

---

## 1. The infrastructure (`Framework/`)

The framework design fixes the following and nothing else. The gate set, cost model, and
classical/quantum semantics are implemented; the final submission-package structure is still an
M5 item:

- **A trusted primitive gate set** `{X, H, CX, CCX, P(dir,k)}` and a circuit as a list of them
  (`Circuit := List Gate`). The Clifford/Toffoli gates `{X, H, CX, CCX}` express all
  reversible arithmetic; `P(dir,k)` is a single-qubit rotation by `±2π/2^k`, which supplies
  the mutually adjoint phases the QFT and inverse QFT need (none of the other four can produce
  a non-trivial phase).
- **A naive, simple T-count cost model** `tCount : Circuit → ℕ`, curve- and
  construction-agnostic: Cliffords `{X, H, CX}` cost 0, Toffoli `CCX` costs 7, a rotation
  `P(dir,k)` costs 1 in either direction. A submission that wants a different or tighter count (a 4-T Toffoli, an
  exact rotation-synthesis cost, a Toffoli count, …) proves that as its own theorem — the
  framework only fixes the simple baseline.
- **A submission contract (planned at M5).** A submission will provide a `program` (a circuit
  family) together with a proof that it is `correct` and a proof of its `counted` T-count bound —
  both stated about the *same* `program` term.
- **The semantics `correct` is stated against.** A layer-neutral basis-state type
  `BasisState := Wire → Bool` with a *classical* action (`Classical.run`, gates as basis-state
  permutations) for the reversible arithmetic (M1–M3), and — added at M4 — a *separate*
  Hilbert-space layer over `BasisState →₀ ℂ` for the QFT, bridged to the classical one by an
  agreement lemma so arithmetic correctness lifts to the quantum layer for free (see §5).

The framework checks the two proofs and makes no claim about which curve or algorithm a
submission uses. Any construction that fills the contract is a submission; optimized
constructions are simply different submissions against the same framework.

---

## 2. The submission: Shor for ECDLP over secp256k1

### 2.1 Problem

Given the secp256k1 base point `P` of prime order `n` and a target `Q = [k]P`, recover `k`.

### 2.2 Algorithm

Shor's algorithm as 2-D period finding. The oracle `f(a,b) = [a]P ⊞ [b]Q = [a + k·b]P` is
constant on cosets of the hidden subgroup `H = ⟨(−k, 1)⟩`; the QFT runs on the domain
registers, and one measurement yields `(α, β)` with `β ≡ k·α (mod n)`.

```
Input : secp256k1 E/F_p, base point P (order n), target Q = [k]P.
Output: k.

1.  Registers: a, b (each m qubits);  R (an affine point of E, init O).
2.  H^{⊗m} on a and on b.
3.  Oracle U_f, by classically-controlled double-and-add over precomputed tables:
        for i in 0..m-1:  if a_i : R ← R ⊞ [2^i]P
        for i in 0..m-1:  if b_i : R ← R ⊞ [2^i]Q
    → 2m conditional point additions (each = one Fermat inversion + modular muls).
4.  Leave R unobserved (equivalently, discard it after the oracle). The current theorem
    marginalizes over R in the probability calculation; operational measurement/discard
    semantics are still planned.
5.  Inverse QFT over 2^m on a, and on b.
6.  Measure a, b → (α, β); round each phase to the nearest numerator modulo the known n,
    then recover k = β·α⁻¹ (mod n).
7.  Verify Q == [k]P classically; repeat if needed.
```

### 2.3 Construction (naive, un-optimized)

- **Field** `F_p`, `p = 2^256 − 2^32 − 977` (hardcoded). Schoolbook modular multiplication;
  inversion by Fermat, `a⁻¹ = a^(p−2)`.
- **Point addition**: affine Weierstrass, a quantum point ⊞ a classical constant point; the
  `[2^i]P` / `[2^i]Q` tables are precomputed classical constants with a verified doubling
  recurrence.
- **Scalar multiplication**: classically-controlled binary double-and-add, `2m` additions.
- **Oracle**: writes `[a]P ⊞ [b]Q` into `R`; `R` is then measured and discarded.
- **QFT**: textbook coherent in-register QFT over `2^m` (`H` +
  controlled-`P(.forward,k)`), with the inverse QFT defined by the generic circuit adjoint and
  applied to each exponent register in order finding.
- **Recovery**: because the subgroup order is known, round both sampled phases to their nearest
  numerators modulo `n`, then compute `k = β·α⁻¹ (mod n)` when `α ≠ 0`.

### 2.4 Current proof status

Landed on the status baseline:

- **Framework + M1 arithmetic.** Classical and quantum circuit semantics are defined, and the
  full reversible field-arithmetic chain is verified: ripple addition, modular addition,
  modular subtraction, clean zero/equality predicates, schoolbook modular multiplication,
  square-and-multiply exponentiation, and Fermat inversion. The generic constructors now have a
  concrete width-257 secp256k1 block allocation with exact numeric costs. Correctness,
  cleanup/locality, `HPFree`, well-formedness, and exact `tCount` obligations refer to the same
  circuit terms.
- **Partial M2.** The canonical Mathlib secp256k1 affine point type and standard generator are
  fixed; the injective 513-bit point encoding and its 256-to-257 register-padding interface are
  root-reachable; and generic `[2^i]P` tables have verified length, lookup, and doubling recurrence.
- **Partial M4.** The finite-support Hilbert-space semantics, classical-to-quantum agreement,
  inner-product preservation, exact QFT/IQFT circuits and proofs, generic exact/approximate
  phase estimation (under a supplied controlled-powers linear map), an abstract ECDLP-oracle
  contract, the generic circuit/classical-action-to-oracle refinement, the algebraic
  hidden-subgroup recovery reduction, and the conditional two-register Fourier-sampling theorem
  are verified. Under the abstract oracle contract, the latter recovers `d mod r` with one-shot
  probability at least `((r−1)/r)·(4/π²)²`.

Still open before the repository can claim the target end-to-end result:

- a circuit-free total affine formula and point-addition circuit covering infinity, inverse-pair,
  doubling, and generic cases, built from the now-landed concrete arithmetic/encoding leaves;
- controlled scalar addition over the verified doubling tables and one Bennett-clean ECDLP oracle
  with an exact classical whole-state theorem, then refinement to `ECDLPOracleSpec` and
  instantiation of the already-proved conditional `orderFinding_correct` theorem;
- operational measurement/discard and repetition semantics for turning the existing marginal
  probability statement into an executable sampling contract;
- the generator-order certificate needed by the concrete secp256k1 specialization;
- the same-program end-to-end correctness and T-count theorem, `Framework.Contract` instance,
  and checked secp256k1 reference number.

---

## 3. File structure

```
lakefile.lean  lean-toolchain  lake-manifest.json
docs/PLAN.md
docs/ARITHMETIC.md                         # bottom-up arithmetic textbook
scripts/verify.sh
ShorECDLP.lean                              # root aggregator
ShorECDLP/
  Framework/
    InstructionSet.lean                    # [M0 ✓] gates, adjoints, wires, circuits, well-formedness
    CostModel.lean                         # [M0 ✓] curve-agnostic naive tCount
    BasisState.lean                        # [M0 ✓] BasisState, register read/write, Clean
    Classical/
      Semantics.lean                       # [M1.0 ✓] basis-state run + HPFree
    Quantum/
      Semantics.lean                       # [M4 ✓] finite-support states + agreement bridge
      InnerProduct.lean                    # [M4 ✓] unitarity, normalization, circuit adjoints
      Measure.lean            (planned)    # [M4] measurement/discard semantics
    Contract.lean             (planned)    # [M5] same-program correct + counted package
  Submission/
    Field.lean                             # [M1 ✓] p, order, curve constants, Fermat identity
    Arithmetic/
      README.md                            # exact import and contract-composition DAGs
      Contracts.lean                      # [M1 ✓] clean same-program arithmetic interfaces
      Primitives.lean                     # [M1 ✓] load/copy/select and support lemmas
      Adder.lean                          # [M1.1 ✓] reversible full-adder cell
      RippleAdder.lean                    # [M1.2 ✓] n-bit ripple-carry adder
      ModAdd.lean                         # [M1.3 ✓] clean modular addition
      ModMul.lean                         # [M1.4 ✓] clean schoolbook modular multiplication
      ModExp.lean                         # [M1.5 ✓] clean square-and-multiply exponentiation
      FermatInv.lean                      # [M1.6 ✓] inversion from a ModExp contract
      Secp256k1Instance.lean              # [M1 ✓] concrete width-257 plans and wire allocation
      ModSub.lean                         # [M1 ✓] clean modular subtraction
      Predicates.lean                     # [M1 ✓] clean equality/zero flags
    EllipticCurve/
      Secp256k1.lean                      # [M2 ✓] canonical curve, affine Point, and generator
      Precompute.lean                     # [M2 ✓] generic verified [2^i]base tables
      PointEncoding.lean                  # [M2 ✓] concrete injective 513-bit encoding
      PointRegister.lean                  # [M2 ✓] slicing/write/padding interface
      AffineFormula.lean      (planned)    # [M2] total circuit-free group-law decision tree
      PointAdd.lean           (planned)    # [M2] quantum point + classical constant
      ScalarMul.lean          (planned)    # [M3] controlled double-and-add
      ECDLPOracle.lean        (planned)    # [M3] concrete U_f
    QFT/
      Defs.lean                            # [M4 ✓] cPhase, QFT, exact adjoint IQFT
      Main.lean                            # [M4 ✓] public QFT/IQFT correctness
      Proofs/
        CPhase.lean  Step.lean             # [M4 ✓] gate/step semantics
        Fourier.lean  Swap.lean            # [M4 ✓] Fourier expansion + bit reversal
        Count.lean                         # [M4 ✓] tCount, WF, normalization
    OrderFinding/
      OracleSpec.lean                      # [M4 ✓] abstract inner-product-preserving ECDLP oracle
      OracleRefinement.lean               # [M4 ✓] circuit/classical-action → ECDLPOracleSpec
      Defs.lean                            # [M4 ✓] two-register algorithm, postprocess, success mass
      Main.lean                            # [M4 ✓] conditional one-shot ECDLP success theorem
      Proofs/
        CyclicEigenstates.lean  OracleKickback.lean
        FourierSampling.lean   Probability.lean
        Postprocess.lean        SuccessProbability.lean
                                             # [M4 ✓] 2-D Fourier sampling and recovery proof chain
      PhaseEstimation/
        Defs.lean                          # [M4 ✓] generic semantic QPE map/contracts
        Main.lean                          # [M4 ✓] exact and ≥4/π² approximate theorems
        Proofs/
          Hadamard.lean  ControlledPowers.lean  Eigenphase.lean
          Fourier.lean  Probability.lean  Approximations.lean
                                             # [M4 ✓] generic QPE proof chain
    Correctness/
      Reduction.lean                       # [M4 ✓] period invariance + exact recovery in ZMod order
      EndToEnd.lean           (planned)    # [M4] concrete-oracle instantiation and composition
    Instance.lean             (planned)    # [M5] fills Framework.Contract
    Reference.lean            (planned)    # [M5] checked secp256k1 resource number
```

The five primitive gate families + the cost model are the entire trusted surface; everything else is
a derived circuit. Measurement and ancilla live in `Framework/Quantum/`, never as new gates.

---

## 4. Milestones

- **M0 ✓** — framework: instruction set `{X,H,CX,CCX,P(dir,k)}`, naive T-count cost model,
  layer-neutral `BasisState`.
- **M1 ✓** — field arithmetic, split into small steps (one PR per step):
    - **M1.0 ✓** classical basis-state semantics + register encoding
    - **M1.1 ✓** verified reversible full-adder cell
    - **M1.2 ✓** n-bit ripple-carry adder (`regValue(out) = a + b mod 2^n`)
    - **M1.3 ✓** clean modular adder (`(a + b) mod p`)
    - **M1.4 ✓** clean schoolbook modular multiplier + composable `HPFree` guard
    - **M1.5 ✓** clean modular exponentiation (square-and-multiply)
    - **M1.6 ✓** Fermat inversion from `ModExpContract`, discharged against `fermat_inv`
    - **Concrete instance ✓** clean subtraction/predicates plus an actual width-257 secp256k1
      adder wiring, multiplication plan, exponentiation plan, and same-program inversion theorem
- **M2 (partial)** — canonical curve/generator spec and generic precompute tables are complete.
  The concrete injective point encoding and 256-to-257 register-padding interface are complete;
  a total affine formula and the mixed point-addition circuit remain.
- **M3 (open)** — controlled scalar addition, the concrete clean oracle, its classical whole-state
  theorem, and the aggregate resource count remain.
- **M4 (partial)** — quantum semantics/bridge, unitarity, coherent QFT/IQFT, abstract oracle
  contract, generic exact/approximate phase estimation, algebraic reduction, conditional
  two-register ECDLP sampling/recovery, and the circuit-to-oracle refinement lemma are complete;
  concrete-oracle instantiation, measurement/repetition, generator-order specialization, and
  end-to-end same-program composition remain. Refining generic QPE's supplied
  `ControlledPowersOn` map is optional library work, not a dependency of the landed direct
  two-register order-finding theorem.
- **M5 (open)** — the framework contract instance and checked secp256k1 reference number remain.

Each layer: `lake build` green, `#print axioms` free of `sorry` / `native_decide` / new
axioms, and `counted` bound to the same `program` term as `correct`.

---

## 5. Notes

- **Disclosures** for this submission live beside the relevant construction in `Submission/`,
  never in the framework cost model. The current tree exposes the field/reduction assumptions
  and the coherent-QFT count; future scalar-multiplication disclosures belong with that future
  circuit.
- The register width `m` exceeds `⌈log₂ n⌉` by the phase-estimation precision padding.
- The landed point encoding uses 513 public bits: `O ↦ 0` and finite `(x,y) ↦
  `1 + 2*x.val + 2^257*y.val`. `PointRegister.lean` proves the explicit 256-to-257 zero-padding
  interface needed by the concrete field circuits, whose modular adder uses `width = 257` because
  it requires `2*p ≤ 2^width`.
- Primality of `p` and, where recovery needs field inversion, of `order` are visible
  `[Fact (Nat.Prime ...)]` hypotheses, not axioms. The stronger claim that `G` has order `order`
  is not yet proved.
- The framework metric is T-count; against Roetteler's `1.26×10¹¹` **Toffoli** the cross-check
  is `×7` (naive Toffoli→T), since the arithmetic Toffolis dominate and the QFT rotations are
  a lower-order term.
- **Classical→quantum bridge (M4 design locks).** `Classical.run` is the cheap base
  (permutation proofs ≪ unitary proofs). At M4 the quantum layer is *additive over the same
  `BasisState`* (amplitudes `BasisState →₀ ℂ`; `{X,CX,CCX}` permute the support exactly as the
  classical action already says, `H` makes a 2-term superposition, `P(dir,k)` scales by the
  corresponding signed phase — never
  a parallel `Fin (2^n)` basis). One **agreement lemma** — on an H/P-free circuit, the quantum
  run of `|s⟩` equals the delta at `⟪c⟫ s` — transports every M1–M3 arithmetic `correct` up to
  the quantum layer for free; arithmetic is never re-proved in Hilbert space.
- **H/P-free guard.** The classical semantics treats `H`/`P` as identity, so it is faithful
  only on H/P-free circuits. `Classical.HPFree : Circuit → Prop` is now machine-checked and
  composable; the M1 circuit theorems/contracts discharge it, and it is exactly the hypothesis
  used by the M4 agreement lemma.
- **Notation** (`Classical`-scoped): `s[i ↦ b]` (wire update), `⟦g⟧` (a gate's classical
  transformer), `⟪c⟫` (a circuit's, run left to right).

---

## 6. Conventions (every PR follows this — the "PR #1 style")

- **One PR per fine-grained step** (M1.0, M1.1, …), branched off the latest `main`, small
  enough to review on its own.
- **PR body**: what the step adds (bulleted), that it builds green, that `#print axioms` is
  free of `sorry` / `native_decide` / new axioms, and the next step.
- **Naming**: types stay layer-neutral (`BasisState`); the classical marker goes on the
  *actions* (`Classical.*`). Nothing should read as a semantics it isn't.
- **Notation**: use readable notation in statements *and* proofs so they read close to the
  math, and introduce new notation for each new operation as it appears (with `@[inherit_doc]`
  so it self-documents). Current: `s[i ↦ b]`, `⟦g⟧`, `⟪c⟫`.
- **Proofs**: no `sorry` / `native_decide` / new axioms; `correct` and `counted` are stated
  about the *same* `program` term; carry only the hypotheses actually used (the unused-argument
  linters enforce this).
- **Same trusted surface**: everything is a derived circuit over the five primitive gates;
  the framework cost model stays disclosure-free and curve-agnostic.

---

## 7. M4 quantum layer — landed components and remaining integration

The quantum semantics is implemented additively over the same `BasisState`. It provides the
amplitude state `BasisState →₀ ℂ`, gates as linear maps
(`onKet` + `linearCombination`), the **agreement bridge** (`run (ket s) = ket (Classical.run c s)`
for `HPFree` circuits — transports all M1–M3 arithmetic correctness up for free), and **norm
preservation** (`run_preservesNormSq` for `CircuitWellFormed` circuits ⇒ `normSq_run_ket = 1`,
the Born-rule input for the success bound). The gate set is adjoint-closed, and
`run_adjoint_run` / `run_run_adjoint` prove two-sided cancellation on arbitrary finite-support
states.

**Two orthogonal circuit predicates** (keep separate, never bundled): `Classical.HPFree` (no H/P —
for the agreement bridge) and `CircuitWellFormed` (distinct wires per gate — for unitarity).
Arithmetic needs **both**; the QFT needs **`WellFormed` only** (it has H/P, so it is not HPFree,
and its correctness goes through the quantum semantics, not the classical bridge).

**Landed QFT and phase-estimation components** (stated over `Quantum.run`):

- **Q0/Q1 ✓ — controlled-phase atom.** Controlled-`P(.forward,k)` is realized in-set as
  `cPhase k c t anc := [.CCX c t anc, .P .forward k anc, .CCX c t anc]` (`anc` fresh `|0⟩`) — ket action
  `(if s c && s t then phaseCoeff .forward k else 1) • ket s`, at cost 2 Toffoli
  + 1 P. Its require-and-restore spec says `anc` is `|0⟩` on entry and returns to `|0⟩` (the same
  freshness discipline as the adder's `st s = false`), so a single ancilla is reused across the
  whole QFT. The inverse atom is obtained by circuit adjoint and uses `P(.inverse,k)` at the
  same cost; synthesizing it from a product of positive phases would distort the resource count.
- **Q2 ✓ — single-target step.** `H` on the target plus the controlled-phase cascade has a
  proved ket action and well-formedness theorem.
- **Q3 ✓ — full QFT.** `qft_correct` proves the normalized Fourier-sum action for an LSB-first
  register, including the final bit reversal.
- **Q4 ✓ — count, well-formedness, and normalization.** `tCount_qft`, `tCount_iqft`, both
  well-formedness theorems, and norm preservation are proved about the concrete circuits.
- **Q5 ✓ — inverse QFT.** `iqft` is the generic circuit adjoint; exact two-sided cancellation is
  proved on arbitrary finite-support states.
- **Q6 ✓ — generic phase estimation.** `phaseEstimation_correct_exact` proves the exact-grid
  result, and `phaseEstimation_correct_approx` supplies a nearest label within half a grid cell
  with probability at least `4/π²`. These theorems intentionally assume a supplied linear
  controlled-powers block satisfying `ControlledPowersOn`.
- **Q7 ✓ — conditional two-register order finding.** `orderFinding_correct` decomposes the point
  register into cyclic characters, proves the joint oracle kickback, applies the two inverse QFTs,
  and combines peak rounding with division in `ZMod r`. Given `ECDLPOracleSpec`, it recovers the
  hidden shift `d mod r` with one-shot probability at least `((r−1)/r)·(4/π²)²`. The theorem
  marginalizes the unmeasured registers through `jointRegisterProbability`; it does not yet
  provide a measurement circuit, a concrete secp256k1 oracle, or the final resource theorem.

**Remaining M4 integration.** The concrete ECDLP path no longer needs a new generic
controlled-powers theorem: `orderFinding_correct` directly consumes one joint oracle. Build a
classical reversible oracle circuit, refine it to `ECDLPOracleSpec` through the H/P-free
classical-to-quantum bridge and the well-formedness/isometry theorem, instantiate the conditional
two-register result, and then add computational-basis measurement/discard and repetition
semantics plus the final same-program correctness/resource theorem.

---

## 8. Concrete oracle construction roadmap

`orderFinding_correct` should remain unchanged. It already proves the difficult 2-D
Fourier-sampling and recovery statement for any linear map satisfying `ECDLPOracleSpec`. The
concrete side must supply a single exact classical action:

```text
regValue aReg s = a
regValue bReg s = b
regValue pointReg s = (enc.encode R).val
Clean oracleWork s
----------------------------------------------------------------
Classical.run oracleCircuit s
  = writeReg pointReg
      (enc.encode (R + ecdlpFunction P Q a b)).val s
```

The whole-state equality is intentional: it preserves the exponent registers and every outside
wire and restores `oracleWork` exactly, so no garbage remains entangled with the Fourier
registers.

### 8.1 Dependency order

1. **Circuit-to-oracle refinement ✓.** `ECDLPOracleSpec.ofCircuit` is proved from point
   width/global non-aliasing,
   `Classical.HPFree oracleCircuit`, `CircuitWellFormed oracleCircuit`, and the classical equation
   above. Its two substantive fields then follow from existing framework theorems:
   `run_ket_agrees_classical` supplies `onKet`, while `run_preservesInner` supplies
   `preservesInner`. This module stays independent of concrete arithmetic.

2. **Point representation ✓.** The 513-bit affine encoding with raw-code validity and injectivity
   is root-reachable. `PointRegister.lean` supplies the register-slicing, `writeReg`, and
   256-to-257 zero-padding lemmas needed by the arithmetic implementation.

3. **Concrete field leaves ✓.** The tree contains actual width-257 secp256k1 `ModAddWiring`,
   `ModMul.Plan`, and `ModExp.Plan` values with proved validity and exact numeric costs. Fermat
   inversion is specialized from that exact exponentiation program. Clean modular subtraction and
   equality/zero predicates are also root-reachable; these supply slope numerators,
   exceptional-case tests, and the nonzero premise of `FermatInv.correct`.

4. **Circuit-free total affine specification.** Prove that one explicit decision tree agrees
   with Mathlib point addition for `R=O`, `C=O`, `R=-C`, `R=C` (doubling), and `x_R ≠ x_C`
   (generic addition). Every branch that invokes inversion first proves its denominator nonzero.
   Keeping this theorem free of wires separates elliptic-curve mathematics from reversible
   layout bookkeeping.

5. **Clean point translation.** First certify an out-of-place compute/XOR embedding for
   `R + C`, including functional correctness, cleanup/locality, exact `tCount`, H/P-freedom, and
   well-formedness on the same circuit. Then build the in-place and controlled translations by an
   explicit inverse/Bennett construction. Do not control every gate directly: controlling `CCX`
   would leave the primitive set. Compute the candidate and reuse the landed `selectBit`/
   `selectPoint` primitives for reversible selection and history. Behavior on invalid point codes
   may remain unspecified, but the gate circuit is a total permutation on all bit strings.

6. **Scalar folds and the joint oracle.** Fold controlled translations over the little-endian
   scalar bits and `Precompute.doublingTable`; prove by induction that the accumulator becomes
   `R + [a]P`. Repeat for `b,Q`, uncompute the complete history, and expose the classical
   whole-state oracle theorem displayed above together with exact cost, `HPFree`, and
   well-formedness.

7. **Refinement and Bitcoin specialization.** Apply step 1 to obtain
   `ECDLPOracleSpec enc (Quantum.run oracleCircuit) ...`, then instantiate
   `orderFinding_correct`; no new Fourier or success-bound proof is needed. A Bitcoin wrapper
   additionally needs visible proofs or hypotheses for `Nat.Prime order` and
   `addOrderOf Secp256k1.G = order`. Operational measurement/repetition and the final M5 resource
   contract remain later layers and must not be implied by this conditional specialization.

The remaining critical path is therefore:

```text
total affine formula + clean PointAdd
  → controlled scalar folds
  → classical ECDLP oracle equation
  → ECDLPOracleSpec refinement
  → instantiate orderFinding_correct
```

The first three leaves above are complete and root-reachable. The affine formula/PointAdd layer is
next; each remaining item stays a separate, reviewable PR with root reachability, warning-fatal
build, targeted axiom disclosure, and exhaustive axiom audit.
