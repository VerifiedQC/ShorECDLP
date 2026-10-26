import ShorECDLP.Challenge.ExtendedContract
import ShorECDLP.Submission.Naive.Challenge.NumericCertificate

namespace ShorECDLP.NaiveChallenge
open Challenge
noncomputable section

/-- Conservative worst-path primitive bounds for all 26 rounds.
These are upper bounds derived from the protected T and gate-slot bounds,
not exact counts and not a rotation-synthesis estimate. -/
def naiveExtendedBounds : ExtendedBounds where
  toffoli := 1274005626253092
  nonClifford := 3620864829523968

/-- The original numeric certificate plus diagnostics for the same entry. -/
theorem naiveRepeatedEntry_extended_certificate :
    ExtendedCertificate naiveNumericLimits repeatedDecodeLayout naiveRepeatedEntry
      naiveNumericBounds naiveExtendedBounds := by
  exact naiveRepeatedEntry_numeric_certificate.extend

end
end ShorECDLP.NaiveChallenge
