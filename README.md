# ShorECDLP

A verified, end-to-end resource estimate for Shor's algorithm on the **elliptic-curve
discrete-logarithm problem (ECDLP)** over **secp256k1** — the quantum attack on ECDSA
as used by Bitcoin.

## What this is

The deliverable is a circuit family we *construct* together with two machine-checked
theorems about **that same circuit**:

- **functional correctness**, end-to-end (the circuit implements the ECDLP
  period-finding oracle, with a success-probability bound); and
- a **gate-count bound**, end-to-end (Toffoli-caliber; T-count derived).

The point is the *kind of evidence*, not the size of the number: the counted circuit is
the very circuit proved correct (one and the same `prog` term). That is the substantive
difference from resource estimates that transcribe a formula as an assumption, or that
rely on executable checks rather than machine-checked proof.

## Scope of this version

This is the **simplest, un-optimized** construction — a starting point, not a
compromise. It uses generic modular reduction (not specialized to secp256k1's
pseudo-Mersenne prime), Fermat inversion, and un-windowed double-and-add. Each
optimization (pseudo-Mersenne reduction, windowing, a cheaper inversion, …) is a
*future submission* in the same interface. See the cost-model statement in
`ShorECDLP/CostModel.lean` for how to read the number.

## Build

```
lake exe cache get   # fetch the pinned Mathlib cache
lake build
```

Toolchain: `leanprover/lean4:v4.28.0`; Mathlib pinned to the same revision as
[VerifiedQC/ForShor](https://github.com/VerifiedQC/ForShor).

## Status

M0 — project skeleton (instruction set + Toffoli cost model), builds green.
Roadmap: M1 field arithmetic → M2 point addition → M3 scalar multiplication + oracle →
M4 quantum semantics + end-to-end correctness → M5 submission spec.
