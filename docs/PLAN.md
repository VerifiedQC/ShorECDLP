# ShorECDLP — Algorithm and Project Structure

Repo: https://github.com/VerifiedQC/ShorECDLP. Curve: secp256k1.
Goal: a verified, end-to-end resource estimate (program + proof of correctness + proof of
gate count) for Shor's algorithm solving ECDLP.

> **Status labels.** M0 and the M1 field piece are concrete and landed. M2–M3 files are
> planned-concrete. The `Quantum/` split and `Correctness/*` subtree are **provisional** —
> a forecast of an unwritten layer, to be updated or deleted when M4 content exists (and
> re-checked at M5). Do not read the provisional subtree as a spec.

---

## 1. Algorithm — pseudocode

**Problem.** On secp256k1, given base point `P` of prime order `n` and target `Q = [k]P`,
recover `k` (the ECDLP; ECDSA key recovery reduces to it). Let `m` be the register width
(≥ `⌈log₂ n⌉`, with phase-estimation precision padding — see §2, decision 6).

**Quantum core = 2-D period finding** (hidden-subgroup over `Z_N × Z_N`, `N = 2^m`). Key
identity:
```
f(a, b) := [a]P  ⊞  [b]Q  =  [a + k·b] P        (since Q = [k]P)
```
so `f` is constant on cosets of the hidden subgroup `H = ⟨(−k, 1)⟩`. The QFT runs on the
**domain** registers — not on the curve; `E` is only the codomain "label."

```
Input : secp256k1 E/F_p, base point P (prime order n), target Q = [k]P.
Output: k = dlog_P(Q).

1.  Registers:
      a, b : two exponent registers, each m qubits                    (domain)
      R    : one point register, an affine point of E(F_p), init O     (codomain)

2.  Superposition:  H^{⊗m} on a and on b  →  (1/N) Σ_{a,b} |a⟩|b⟩|O⟩

3.  Oracle  U_f : |a⟩|b⟩|O⟩ ↦ |a⟩|b⟩ | [a]P ⊞ [b]Q ⟩,
      via classically-controlled scalar mult over PRECOMPUTED classical tables:
          for i in 0..m-1:  if a_i : R ← R ⊞ table_P[i]     # table_P[i] = [2^i]P (classical)
          for i in 0..m-1:  if b_i : R ← R ⊞ table_Q[i]     # table_Q[i] = [2^i]Q (classical)
      → 2m ≈ 512 conditional point additions, each affine Weierstrass add
        (1 Fermat modular inversion + a few modular multiplications).

4.  Measure-and-discard R (NO uncompute — decision 1). The a,b state is now supported on
      cosets of H (R is traced out in the success proof).

5.  QFT_N on a, QFT_N on b   (coherent, in-register — decision 6).

6.  Measure a, b → (α, β). Classical post-processing recovers k from the H^⊥ relation
      β ≡ k·α (mod n), via the standard phase-estimation / continued-fraction rounding
      (N = 2^m ≠ n, so this is approximate recovery, not an exact one-shot). Success is
      governed by the phase-estimation bound, not a naive (n−1)/n.

7.  Verify Q == [k]P classically; repeat if needed (expected repetitions O(1)).
```

**What is genuinely lighter than factoring:** only the *reduction / number-theory* layer —
`P, Q` are fixed, so there is no random-base casework (no order parity, no trivial-factor
case). The phase-estimation success analysis does **not** disappear.

---

## 2. Components, file structure, and design decisions

Every component below `InstructionSet`/`CostModel` is a **derived circuit** over the four
primitives `{X, H, CX, CCX}` — the trusted counting surface never grows. Each layer carries
both obligations, bound by the same-`prog`-term discipline: the circuit `gateCount` counts
is the one the correctness theorem is about.

| # | Component | Milestone | Obligations |
|---|-----------|-----------|-------------|
| 1 | Instruction set + Toffoli cost model | M0 ✓ | — |
| 2 | Field arithmetic (modmul, Fermat modinv) | M1 | correct + counted |
| 3 | EC point addition + precompute tables | M2 | correct + counted |
| 4 | Scalar mult + ECDLP oracle | M3 | correct + counted |
| 5 | Quantum semantics + QFT + end-to-end correctness + success bound | M4 *(provisional)* | correct (end-to-end) |
| 6 | Submission spec (ecdsa.fail interface) | M5 *(provisional)* | program + correct + counted |

```
ShorECDLP/
  lakefile.lean  lean-toolchain  lake-manifest.json   # lean4:v4.28.0, Mathlib pinned to ForShor
  docs/PLAN.md                         # this file (provisional M4/M5; update-or-delete at M5)
  ShorECDLP.lean                       # root aggregator
  ShorECDLP/
    InstructionSet.lean                # [M0 ✓] Gate {X,H,CX,CCX}, Wire, Circuit
    CostModel.lean                     # [M0 ✓] toffoliCost, gateCount (+append), disclosure statement
    Field.lean                         # [M1 ✓] secp256k1 params, Fp := ZMod p, fermat_inv (x^(p-2)=x⁻¹)
    Arithmetic/
      ModMul.lean                      # [M1] reversible modular multiplication — correct + counted
      ModExp.lean                      # [M1] modular exponentiation (reuses ModMul) — correct + counted
                                       #      (ModInv folds in here unless it carries its own theorem)
    EllipticCurve/
      Precompute.lean                  # [M2] classical tables [2^i]P,[2^i]Q + correctness (table[i]=[2^i]P)  (decision 5)
      PointAdd.lean                    # [M2] affine add: quantum point ⊞ classical constant — correct + counted
      ScalarMul.lean                   # [M3] classically-controlled double-and-add (2m adds) — correct + counted
      ECDLPOracle.lean                 # [M3] U_f : |a,b,O⟩ ↦ |a,b,[a]P⊞[b]Q⟩ — correct + counted  (decision 2: no Oracle/ folder)
    Quantum/            (provisional)
      Semantics.lean                   # [M4] state space + gate semantics (borrow ForShor QSemantics DESIGN)
      Measure.lean                     # [M4] measurement semantics (stays M4 under decision 6)
      QFT.lean                         # [M4] coherent in-register QFT over Z_N + the QFT-model statement (decision 6)
    Correctness/        (provisional)
      Reduction.lean                   # [M4] ECDLP ↔ ⟨(−k,1)⟩; k ≡ β·α⁻¹ (mod n)
      SuccessBound.lean                # [M4] phase-estimation success bound
      EndToEnd.lean                    # [M4] assembled circuit implements the ECDLP oracle
    Submission.lean     (provisional)  # [M5] ecdsa.fail-style spec: circuit family + proved Toffoli/T bound + end-to-end correct
    Reference.lean      (provisional)  # [M5] instantiate at secp256k1 → the checked end-to-end Toffoli number
```

### Design decisions (locked with proof-review / arxiv-scout)

1. **R is measure-and-discarded, not uncomputed** — keeps point-adds at ~2m ≈ 512 (uncompute
   would roughly double it); the success proof traces R out. Stated in `ECDLPOracle` docstring.
2. **No premature `Oracle/` folder** — `ECDLPOracle.lean` lives under `EllipticCurve/`.
3. **M4/M5 subtree is provisional**, labelled, not a spec.
4. **`ModInv` earns a file only if it carries its own `correct`** (discharging against
   `fermat_inv`); otherwise it folds into `ModExp.lean`.
5. **Precompute tables `[2^i]P`/`[2^i]Q` are verified constants** (a wrong table breaks oracle
   correctness while leaving the count valid) — `Precompute.lean` with a doubling-recurrence lemma.
6. **QFT model = (b) coherent stored-register `Z_{2^m}` QFT.** Rationale: ForShor's QFT is
   coherent in-register (directly borrowable; the semiclassical route would need mid-circuit
   measurement + feed-forward built from scratch), and it keeps the circuit unitary so the
   same-`prog`-term invariant is stated over a unitary circuit and measurement stays at M4.
   The Roetteler baseline uses the **semiclassical** (Griffiths–Niu) QFT (confirmed against
   arXiv:1706.06752), so our qubit count is **+2n** vs its `9n+2⌈log₂n⌉+10` — but the headline
   **Toffoli** count (dominated by the 2m point-additions) is unaffected and still reconciles
   against `1.26×10¹¹`. **Disclosure:** "QFT model = coherent stored-register; differs from the
   semiclassical reconciliation baseline; qubit count +2n, Toffoli count unaffected." The
   semiclassical variant is a future submission.

**Trusted surface** = only `InstructionSet` (4 gates) + `CostModel`. Measurement/ancilla live
in `Quantum/` (semantic layer), never as new primitives.
