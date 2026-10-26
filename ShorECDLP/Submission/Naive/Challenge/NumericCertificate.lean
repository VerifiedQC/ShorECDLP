import ShorECDLP.Submission.Naive.Challenge.NumericCosts
import ShorECDLP.Submission.Naive.Challenge.NumericQubits
import ShorECDLP.Submission.Naive.Challenge.NumericLengths

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge
noncomputable section

/-- Conservative admission limits for the complete 26-round Naive entry.
The gate-slot bound counts disabled slots too; it is not the T-model score. -/
def naiveNumericLimits : Limits where
  gateSlots := 3620864829523968
  measurements := 5385536
  coefficientRows := 512
  candidateChecks := 26

/-- Resource bounds for all 26 rounds, including observations and resets. -/
def naiveNumericBounds : Bounds where
  qubits := 206624
  tModel := 8918039383771648
  measurements := 5385536

attribute [local irreducible] repeatedProgram naivePowerTable Straight.WellFormed

/-- A numeric certificate for the actual protected entry and protected decoder.
There is no assumed producer agreement or unproved resource premise. -/
theorem naiveRepeatedEntry_numeric_certificate :
    Certificate naiveNumericLimits repeatedDecodeLayout naiveRepeatedEntry naiveNumericBounds := by
  have h := naiveRepeatedEntry_certificate naiveNumericLimits naiveRepeatedEntry_gateSlots_le
    (by decide) (by decide) (by decide)
  refine { h with resources := ?_ }
  intro Q
  exact ⟨naiveRepeatedEntry_qubit_bound Q, naiveRepeatedEntry_tModel_bound Q,
    (naiveRepeatedEntry_resources Q).2.2.le⟩

theorem naiveNumericBounds_score : declaredScore naiveNumericBounds = 8918039383771648 := rfl

end
end ShorECDLP.NaiveChallenge
