# ShorECDLP — Algorithm and Project Structure

Repo: https://github.com/VerifiedQC/ShorECDLP. Curve: secp256k1 (Bitcoin), constants hardcoded.
Goal: a verified, end-to-end resource estimate (program + proof of correctness + proof of
gate count) for Shor's algorithm solving ECDLP.

> **Status labels.** M0 and the M1 field piece are concrete and landed. M2–M3 files are
> planned-concrete. The `Framework/Quantum/`, `Framework/Contract`, `Submission/QFT`,
> `Submission/Correctness/*`, `Submission/{Instance,Reference}` entries are **provisional** —
> a forecast of unwritten layers, to be updated or deleted when M4/M5 content exists.

---

## 1. Algorithm — pseudocode

**Problem.** On secp256k1, given base point `P` of prime order `n` and target `Q = [k]P`,
recover `k` (the ECDLP; ECDSA key recovery reduces to it). Let `m` be the register width
(≥ `⌈log₂ n⌉`, with phase-estimation precision padding).

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

1.  Registers:  a, b (each m qubits, domain);  R (an affine point of E(F_p), init O).
2.  Superposition:  H^{⊗m} on a and on b  →  (1/N) Σ_{a,b} |a⟩|b⟩|O⟩.
3.  Oracle  U_f : |a⟩|b⟩|O⟩ ↦ |a⟩|b⟩ | [a]P ⊞ [b]Q ⟩, via classically-controlled scalar
      mult over PRECOMPUTED classical tables:
          for i in 0..m-1:  if a_i : R ← R ⊞ table_P[i]     # table_P[i] = [2^i]P
          for i in 0..m-1:  if b_i : R ← R ⊞ table_Q[i]     # table_Q[i] = [2^i]Q
      → 2m ≈ 512 conditional point additions (each = 1 Fermat inversion + a few modmuls).
4.  Measure-and-discard R (NO uncompute — decision 1); a,b now on cosets of H.
5.  QFT_N on a, QFT_N on b   (textbook coherent in-register QFT over 2^m — decision 6).
6.  Measure a, b → (α, β). Recover k from H^⊥ (β ≡ k·α mod n) by the standard
      phase-estimation / continued-fraction rounding (N = 2^m ≠ n → approximate recovery;
      success governed by the phase-estimation bound, not a naive (n−1)/n).
7.  Verify Q == [k]P classically; repeat if needed (expected O(1)).
```

**Lighter than factoring in exactly one place:** the *reduction / number-theory* layer —
`P, Q` are fixed, so no random-base casework (no order parity, no trivial-factor case). The
phase-estimation success analysis does **not** disappear.

---

## 2. Structure — `Framework/` and `Submission/`

Top-level split (mirrors ForShor's Framework / Implementation):

- **`Framework/`** — the reusable, **curve- and construction-agnostic** judging apparatus:
  the primitive gate set, the Toffoli cost model (with **zero disclosures baked in**), the
  quantum semantics, and the submission **contract** (`program + correct + counted`). It is a
  small audited base that can judge *any* EC submission.
- **`Submission/`** — the concrete **secp256k1** ECDLP construction: hardcoded constants, the
  arithmetic/EC/oracle circuits, the QFT the construction uses, the correctness + success
  proofs, and the instance that fills the contract — **plus this submission's own disclosure
  note, beside the constants it describes.**

**Why disclosures are submission-side** (settled with proof-review / arxiv-scout): the three
obligations are machine-checked; disclosures ("we used generic reduction / Fermat / coherent
QFT") are *documentation of algorithm choices*, not theorems. Different epistemic status →
different home. A future optimized submission carries a *different* disclosure list against
the *identical* framework — the "each optimization is a new submission" story.

Every circuit is a **derived circuit** over the four primitives `{X, H, CX, CCX}`; the trusted
counting surface never grows. Each layer with both obligations obeys the same-`prog`-term
discipline (the counted circuit is the proven one).

```
ShorECDLP/
  lakefile.lean  lean-toolchain  lake-manifest.json   # lean4:v4.28.0, Mathlib pinned to ForShor
  docs/PLAN.md
  ShorECDLP.lean                         # root aggregator
  ShorECDLP/
    Framework/                           # reusable, curve-agnostic
      InstructionSet.lean                # [M0 ✓] Gate {X,H,CX,CCX}, Wire, Circuit
      CostModel.lean                     # [M0 ✓] Toffoli gateCount (+append) — NO disclosures
      Quantum/            (provisional)
        Semantics.lean                   # [M4] state space + gate semantics (borrow ForShor QSemantics design)
        Measure.lean                     # [M4] measurement semantics
      Contract.lean       (provisional)  # [M5] the submission contract: program + correct + counted
    Submission/                          # concrete secp256k1 ECDLP construction
      Field.lean                         # [M1 ✓] hardcoded secp256k1 constants (p, order, a=0, b=7) + fermat_inv + submission-side disclosure
      Arithmetic/
        ModMul.lean  ModExp.lean         # [M1] reversible modmul / modexp — correct + counted (ModInv folds into ModExp unless it earns a theorem)
      EllipticCurve/
        Precompute.lean                  # [M2] verified classical tables [2^i]P,[2^i]Q (table[i+1]=table[i]⊞table[i])
        PointAdd.lean                    # [M2] affine add: quantum point ⊞ classical constant — correct + counted
        ScalarMul.lean                   # [M3] classically-controlled double-and-add (2m adds) — correct + counted
        ECDLPOracle.lean                 # [M3] U_f — correct + counted (no premature Oracle/ folder)
      QFT.lean            (provisional)  # [M4] textbook coherent in-register QFT over 2^m (the construction's QFT)
      Correctness/        (provisional)
        Reduction.lean                   # [M4] ECDLP ↔ ⟨(−k,1)⟩; k ≡ β·α⁻¹ (mod n)
        SuccessBound.lean                # [M4] phase-estimation success bound (borrow ForShor's analysis)
        EndToEnd.lean                    # [M4] assembled circuit implements the ECDLP oracle
      Instance.lean       (provisional)  # [M5] fills Framework.Contract for ECDLP
      Reference.lean      (provisional)  # [M5] instantiate at secp256k1 → the checked end-to-end Toffoli number
```

### Design decisions (locked with proof-review / arxiv-scout / runzhou)

1. **R measure-and-discarded, not uncomputed** — keeps point-adds at ~2m ≈ 512; the success
   proof traces R out. Stated in `ECDLPOracle`'s docstring.
2. **No premature `Oracle/` folder** — `ECDLPOracle.lean` sits in `EllipticCurve/`.
3. **M4/M5 subtree labelled provisional** — forecast, not spec.
4. **`ModInv` folds into `ModExp`** unless it carries its own `correct` (discharge vs `fermat_inv`).
5. **Precompute tables are verified constants** — a wrong table breaks oracle correctness while
   the count stays valid.
6. **QFT model = textbook coherent stored-register `Z_{2^m}`** (runzhou: "naive QFT over 2^n,
   phase-estimation approximation needed, textbook only"). Borrows ForShor's coherent QFT; keeps
   the circuit unitary (measurement at M4, same-`prog`-term over a unitary circuit). Roetteler's
   baseline is *semiclassical* (confirmed, arXiv:1706.06752), so our qubit count is **+2n**, but
   the headline **Toffoli** count (dominated by the 2m point-adds) is unaffected and still
   reconciles against `1.26×10¹¹`.
7. **Constants hardcoded** — secp256k1 is the Bitcoin target, so `p`, `order`, `a`, `b` (and the
   base point at M2/M3) are explicit literals, not parameters.
8. **Disclosures live submission-side**, beside the constants; `Framework/CostModel` stays
   disclosure-free and curve-agnostic. Reviewer checks the boundary holds (no disclosure leaks
   into `Framework/`).

**Trusted surface** = only `Framework/InstructionSet` (4 gates) + `Framework/CostModel`.
Measurement/ancilla live in `Framework/Quantum/` (semantics), never as new primitives.
