# Additional primitive-count bounds

`Challenge.ExtendedCertificate` contains the existing `Certificate` and an
additional `diagnostics` proof. The original certificate's fields and score
remain unchanged. The proof bounds both protected counters on the **same
instantiated entry**, for every public point Q.

`ExtendedBounds.toffoli` bounds actual CCX primitives.
`ExtendedBounds.nonClifford` bounds CCX primitives plus phase primitives P with
k ≥ 3 (either direction). Both counters take the maximum across measurement
branches. Counts refer to gates that execute, rather than disabled template
slots. They are neither exact counts nor a rotation-synthesis cost estimate.
Measurements and Clifford gates do not contribute to these two counters.

The reusable `Certificate.extend` proves conservative diagnostic bounds from
an existing certificate:

- Toffoli ≤ floor(bounds.tModel / 7), because each CCX costs 7 in the protected
  abstract T model.
- Non-Clifford ≤ limits.gateSlots, because each counted primitive is an actual
  gate and actual gates are bounded by submitted slots.

The new Naive `naiveRepeatedEntry_extended_certificate` covers all 26 rounds:

| Metric | Proven upper bound |
|---|---:|
| Toffoli primitives | 1,274,005,626,253,092 |
| Non-Clifford primitives | 3,620,864,829,523,968 |

These conservative bounds reuse the existing numeric certificate. They do not
change its circuit, success theorem, qubit bound, measurement count, or abstract
T-model score. A protected judge can require `ExtendedCertificate` and report
these bounds alongside those existing metrics. The judge must label them as
upper bounds, not measured or exact gate counts.
