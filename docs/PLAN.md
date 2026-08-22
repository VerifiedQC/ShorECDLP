# ShorECDLP

A minimal, **ecdsa.fail-style verification infrastructure** for quantum resource-estimate
submissions, together with **one super-naive Shor/ECDLP submission** that fills it.

Repo: https://github.com/VerifiedQC/ShorECDLP. Toolchain: `leanprover/lean4:v4.28.0`,
Mathlib pinned. Curve: secp256k1 (Bitcoin).

---

## 1. The infrastructure (`Framework/`)

The framework fixes the following and nothing else:

- **A trusted primitive gate set** `{X, H, CX, CCX, P(k)}` and a circuit as a list of them
  (`Circuit := List Gate`). The Clifford/Toffoli gates `{X, H, CX, CCX}` express all
  reversible arithmetic; `P(k)` is a single-qubit phase rotation, which supplies the phases
  the QFT needs (none of the other four can produce a non-trivial phase).
- **A naive, simple T-count cost model** `tCount : Circuit → ℕ`, curve- and
  construction-agnostic: Cliffords `{X, H, CX}` cost 0, Toffoli `CCX` costs 7, a rotation
  `P(k)` costs 1. A submission that wants a different or tighter count (a 4-T Toffoli, an
  exact rotation-synthesis cost, a Toffoli count, …) proves that as its own theorem — the
  framework only fixes the simple baseline.
- **A submission contract.** A submission provides a `program` (a circuit family) together
  with a proof that it is `correct` and a proof of its `counted` T-count bound — both stated
  about the *same* `program` term.
- **The semantics `correct` is stated against.** A layer-neutral basis-state type
  `BasisState := Nat → Bool` with a *classical* action (`Classical.run`, gates as basis-state
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
4.  Measure and discard R.
5.  QFT over 2^m on a, and on b.
6.  Measure a, b → (α, β);  k = β·α⁻¹ (mod n) by continued-fraction rounding.
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
- **QFT**: textbook coherent in-register QFT over `2^m` on each exponent register
  (`H` + controlled-`P`, the controlled phase built from `P` and `CX`).
- **Recovery**: from `(α, β)`, `k = β·α⁻¹ (mod n)` via phase-estimation / continued-fraction
  rounding.

### 2.4 What is proved

- **`correct`**: the assembled circuit yields the ideal ECDLP-oracle measurement
  distribution, with a phase-estimation success bound.
- **`counted`**: an end-to-end T-count bound on the same circuit (framework metric).

Every layer below carries both obligations as a derived circuit over the four primitives.

---

## 3. File structure

```
ShorECDLP/
  lakefile.lean  lean-toolchain  lake-manifest.json
  docs/PLAN.md
  ShorECDLP.lean
  ShorECDLP/
    Framework/
      InstructionSet.lean                # [M0 ✓] Gate {X,H,CX,CCX,P(k)}, Wire, Circuit
      CostModel.lean                     # [M0 ✓] tCount (naive T-count: Clifford 0, Toffoli 7, P 1), curve-agnostic
      BasisState.lean                    # [M0 ✓] layer-neutral BasisState := Nat→Bool, upd, regValue
      Classical/
        Semantics.lean                   # [M1.0 ✓] classical actions: Classical.applyGate / Classical.run
      Quantum/            (provisional)
        Semantics.lean                   # [M4] Hilbert-space layer over BasisState →₀ ℂ + the agreement lemma
        Measure.lean                     # [M4] measurement semantics
      Contract.lean       (provisional)  # [M5] program + correct + counted (same-term)
    Submission/
      Field.lean                         # [M1 ✓] secp256k1 constants + Fermat-inversion correctness
      Arithmetic/
        Adder.lean                       # [M1.1 ✓] verified reversible full-adder cell
        ModMul.lean  ModExp.lean         # [M1.4/M1.5] modular multiplication / exponentiation
      EllipticCurve/
        Precompute.lean                  # [M2] verified [2^i]P, [2^i]Q tables
        PointAdd.lean                    # [M2] affine add (quantum ⊞ classical constant)
        ScalarMul.lean                   # [M3] double-and-add (2m additions)
        ECDLPOracle.lean                 # [M3] U_f
      QFT.lean            (provisional)  # [M4] coherent QFT over 2^m
      Correctness/        (provisional)
        Reduction.lean                   # [M4] ECDLP ↔ ⟨(−k,1)⟩; k = β·α⁻¹ (mod n)
        SuccessBound.lean                # [M4] phase-estimation success bound
        EndToEnd.lean                    # [M4] the circuit implements the ECDLP oracle
      Instance.lean       (provisional)  # [M5] fills Framework.Contract
      Reference.lean      (provisional)  # [M5] secp256k1 → the checked Toffoli number
```

The four primitive gates + the cost model are the entire trusted surface; everything else is
a derived circuit. Measurement and ancilla live in `Framework/Quantum/`, never as new gates.

---

## 4. Milestones

- **M0 ✓** — framework: instruction set `{X,H,CX,CCX,P(k)}`, naive T-count cost model,
  layer-neutral `BasisState`.
- **M1** — field arithmetic, split into small steps (one PR per step):
    - **M1.0 ✓** classical basis-state semantics + register encoding
    - **M1.1 ✓** verified reversible full-adder cell
    - **M1.2** n-bit ripple-carry adder (`regValue(out) = a + b mod 2^n`)
    - **M1.3** modular adder (`(a + b) mod p`)
    - **M1.4** modular multiplier (schoolbook) — also promotes the `HPFree` guard (§5)
    - **M1.5** modular exponentiation (square-and-multiply)
    - **M1.6** Fermat inversion `modExp(·, p−2)`, discharging against `fermat_inv`
- **M2** — point addition + precompute tables.
- **M3** — scalar multiplication + oracle → end-to-end secp256k1 count.
- **M4** — quantum semantics (agreement-lemma bridge over `BasisState`) + coherent QFT +
  end-to-end correctness + success bound.
- **M5** — the contract instance and the checked secp256k1 reference number.

Each layer: `lake build` green, `#print axioms` free of `sorry` / `native_decide` / new
axioms, and `counted` bound to the same `program` term as `correct`.

---

## 5. Notes

- **Disclosures** for this submission live beside its constants in `Submission/` (generic
  reduction, Fermat inversion, un-windowed scalar mult, coherent-QFT qubit count). The
  framework cost model carries none.
- The register width `m` exceeds `⌈log₂ n⌉` by the phase-estimation precision padding.
- Primality of `p` is a hypothesis `[Fact (Nat.Prime p)]`, not an axiom.
- The framework metric is T-count; against Roetteler's `1.26×10¹¹` **Toffoli** the cross-check
  is `×7` (naive Toffoli→T), since the arithmetic Toffolis dominate and the QFT rotations are
  a lower-order term.
- **Classical→quantum bridge (M4 design locks).** `Classical.run` is the cheap base
  (permutation proofs ≪ unitary proofs). At M4 the quantum layer is *additive over the same
  `BasisState`* (amplitudes `BasisState →₀ ℂ`; `{X,CX,CCX}` permute the support exactly as the
  classical action already says, `H` makes a 2-term superposition, `P` scales by phase — never
  a parallel `Fin (2^n)` basis). One **agreement lemma** — on an H/P-free circuit, the quantum
  run of `|s⟩` equals the delta at `⟪c⟫ s` — transports every M1–M3 arithmetic `correct` up to
  the quantum layer for free; arithmetic is never re-proved in Hilbert space.
- **H/P-free guard.** The classical semantics treats `H`/`P` as identity, so it is faithful
  only on H/P-free circuits (all M1–M3 arithmetic). Enforcement: docstring + per-PR review
  through M1.3; at **M1.4** promote to a machine-checked, composable `HPFree : Circuit → Prop`
  proved per circuit — which is exactly the hypothesis of the M4 agreement lemma (one
  discipline keeps `run` faithful *and* lets arithmetic lift).
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

## 7. M4 quantum layer — status and the QFT plan

The quantum semantics is being built in parallel (branch `QFT-work`), additively over the same
`BasisState`, and already has: the amplitude state `BasisState →₀ ℂ`, gates as linear maps
(`onKet` + `linearCombination`), the **agreement bridge** (`run (ket s) = ket (Classical.run c s)`
for `HPFree` circuits — transports all M1–M3 arithmetic correctness up for free), and **norm
preservation** (`run_preservesNormSq` for `CircuitWellFormed` circuits ⇒ `normSq_run_ket = 1`,
the Born-rule input for the success bound).

**Two orthogonal circuit predicates** (keep separate, never bundled): `Classical.HPFree` (no H/P —
for the agreement bridge) and `CircuitWellFormed` (distinct wires per gate — for unitarity).
Arithmetic needs **both**; the QFT needs **`WellFormed` only** (it has H/P, so it is not HPFree,
and its correctness goes through the quantum semantics, not the classical bridge).

**QFT construction + correctness** (one PR per step, stated over `Quantum.run`):
- **Q0/Q1 — controlled-phase atom.** Realize controlled-`P(k)` in-set. Recommended:
  `cPhase k c t anc := [CCX c t anc, P k anc, CCX c t anc]` (`anc` fresh `|0⟩`) — ket action
  `(if s c && s t then phase k else 1) • ket s` is a one-line `onKet` computation, cost 2 Toffoli
  + 1 P, one reusable ancilla. Ancilla-free alternative: the negative dyadic phase in the 3-gate
  `CP` decomposition is a *product* of positive `P`s (`−2π/2^{k+1} ≡ Σ_{j=1}^{k+1} 2π/2^j`), `O(k)`
  phase gates, no ancilla. Prove ket action + `WellFormed` + tCount.
- **Q2 — single-target step.** `H` on the target + the `cPhase` cascade from the remaining wires;
  prove the one-qubit step action (`applyGate_H_ket` + Q1 + linearity).
- **Q3 — full QFT (main theorem, hard).** `run (qft ws) (ket s) = (1/√N) Σ_{y<N} ω^(x·y) • ket (s
  with ws↦y)`, `N=2^n`, `x=regValue ws s`, `ω=exp(2πi/N)`. Induction on `ws`; the phase telescoping
  is the work. Pin conventions first (normalization, LSB-first, bit-reversal choice) and check
  `n=1,2` before the induction.
- **Q4 — WellFormed + normalization.** `CircuitWellFormed (qft ws)` (WellFormed only); normalization
  falls out of `normSq_run_ket`.
- **Q5 (later) — recovery.** Inverse QFT, computational-basis measurement, phase-estimation /
  continued-fraction success bound — the `SuccessBound` pieces the ECDLP oracle needs.
