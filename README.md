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

The current `Submission/Naive` tree is the **simplest, un-optimized** construction — a starting
point, not a compromise. It uses generic modular reduction (not specialized to secp256k1's
pseudo-Mersenne prime), Fermat inversion, and un-windowed double-and-add. Each
alternative implementation lives in an isolated submission tree over the same shared mathematical
problem and generic framework. `Submission/2607_13816` is reserved for the space-efficient
construction from arXiv:2607.13816v2. See `ShorECDLP/Framework/CostModel.lean` for how to read
resource bounds.

## Build

```
lake exe cache get   # fetch the pinned Mathlib cache
lake build
```

Toolchain: `leanprover/lean4:v4.28.0`; Mathlib pinned to the same revision as
[VerifiedQC/ForShor](https://github.com/VerifiedQC/ForShor).

## Documentation

- [Implementation plan and proof status](docs/PLAN.md)
- [Verified reversible arithmetic: a bottom-up textbook](docs/ARITHMETIC.md)
- [Arithmetic module and API guide](ShorECDLP/Submission/Naive/Arithmetic/README.md)
- [Pinned paper generator, schedules, vectors, and quarantined claims](ShorECDLP/Submission/2607_13816/REFERENCE.md)

## Status

The Naive secp256k1 submission is complete and machine-verified end to end, including correctness,
success probability, T-count, and a qubit-capacity bound for the same program. The independent
arXiv:2607.13816v2 implementation has its source split and coherent adaptive semantics in the open
PR #56 → PR #57 → PR #58 stack; the remaining construction phases are tracked in
[the implementation plan](docs/PLAN.md).
