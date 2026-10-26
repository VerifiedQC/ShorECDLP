import ShorECDLP.Challenge.Contract
namespace ShorECDLP.Challenge
/-- PROTECTED organizer limits, imported by both the judge and entrants. Values TBD. -/
def officialLimits : Limits where
  gateSlots := 4000000000000000
  measurements := 5385536
  coefficientRows := 983040
  candidateChecks := budget55
end ShorECDLP.Challenge
