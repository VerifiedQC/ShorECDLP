import ShorECDLP.Submission.Naive.Challenge.NumericCertificate
import ShorECDLP.Challenge.Official
namespace ShorECDLP.Entrant
open ShorECDLP.Challenge ShorECDLP.NaiveChallenge
noncomputable section
def entry : StraightEntry := naiveRepeatedEntry
def layout : DecodeLayout := repeatedDecodeLayout
def bounds : Bounds := naiveNumericBounds
theorem certificate : Certificate officialLimits layout entry bounds :=
  have h := naiveRepeatedEntry_numeric_certificate
  { h with
    gateBudget := h.gateBudget.trans (by simp [naiveNumericLimits, officialLimits])
    recordBudget := h.recordBudget.trans (by simp [naiveNumericLimits, officialLimits])
    tableBudget := h.tableBudget.trans (by simp [naiveNumericLimits, officialLimits])
    candidateBudget := h.candidateBudget.trans (by simp [naiveNumericLimits, officialLimits, budget55]) }
end
end ShorECDLP.Entrant
