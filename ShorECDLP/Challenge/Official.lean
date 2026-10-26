import ShorECDLP.Challenge.Contract

namespace ShorECDLP.Challenge

/-- PROTECTED organizer admission limits, imported by the judge and by entrants.
Entrants cannot change them: this file is outside the editable path.
* `candidateChecks`: owner decision 2026-10-26, `budget55 = 56 * (2^49 + 2)`.
* `gateSlots`: provisional; covers the proved Naive baseline bound.
* `measurements`: provisional; covers both baselines (2607.13816: 56 trials of
  847,702,509 records; Naive: 5,385,536).
* `coefficientRows`: covers the 2607.13816 table (983,040 rows). -/
def officialLimits : Limits where
  gateSlots := 4000000000000000
  measurements := 47471340504
  coefficientRows := 983040
  candidateChecks := budget55

end ShorECDLP.Challenge
