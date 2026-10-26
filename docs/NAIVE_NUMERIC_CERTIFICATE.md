# Naive: numeric protected certificate

`ShorECDLP.NaiveChallenge.naiveRepeatedEntry_numeric_certificate` certifies the
actual protected entry with the actual protected `nearestPair` decoder. It
covers all 26 rounds, including observation and fixed-wire reset.

| Quantity | Proven bound |
| --- | ---: |
| Quantum wires | 206,624 |
| T-model cost / declared score | 8,918,039,383,771,648 |
| Gate slots, including disabled slots | 4,000,000,000,000,000 |
| Measurement records | 5,385,536 |
| Fixed coefficient rows | 512 |
| Candidate checks | 26 |

The gate-slot number is a conservative admission cap, not an exact gate count
and not the T-model score. The latter is exactly the static T-cost expression
for 26 rounds; actual instantiated cost is bounded by that expression.

The certificate has no resource or producer-agreement hypotheses. Its success
clause has the public challenge contract's nonzero input and discrete-log
relation conditions. The probability is at least 99% for the protected
candidate verifier on the actual measurement history.

## Proof structure

- `NumericCosts`: constant loads have zero T-cost; fixed point-add segments,
  scalar loops and all 26 rounds compose to the stated T bound.
- `NumericQubits`: arbitrary constants share a fixed wire envelope. Observation
  and reset preserve that envelope and rounds reuse the same wires.
- `NumericLengths`: primitive length bounds compose through multiplication,
  exponentiation, arithmetic wrappers, point branches, scalar loops, Fourier
  transforms, and repetition. No complete large circuit is unfolded.
- `NumericCertificate`: the three numeric bounds instantiate the existing
  semantic certificate and fixed admission limits.

Four existing support lemmas are made public without changing their proofs.
No new axioms, admitted proofs, reduction-limit increases or semantic
assumptions are introduced. The resource numbers describe this Naive entry;
they do not establish any score or bound for the separate Streaming entry.
