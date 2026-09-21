import ShorECDLP.Submission.«2607_13816».Window.RawDistribution
import ShorECDLP.Submission.«2607_13816».Window.Repetition
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

/-- At least eight percent accepted, correct public-point decoding on the actual raw entry.
This is unconditional mass over all actual arithmetic and Fourier histories. -/
theorem reducedRawDecoder_success (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (2:ℝ)/25 ≤ reducedRawFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  have hb := (reducedRawDecoder_bounds Q hG hQ hrQ).1
  rw [reducedRawIdealDecoder_eq Q hG hQ hrQ d hQd] at hb
  have hi := secpSuccessBound_numeric.trans (reducedPhysicalVerifiedMass_lower Q hG hQ hrQ d hQd)
  linarith

/-- The probability formula for 56 independent fresh trials exceeds 99 percent.
A concrete reset-and-repeat circuit is a separate implementation obligation. -/
theorem reducedRawDecoder_independent_retry (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ independentRetrySuccessProbability
      (reducedRawFourierEventMass G Q (reducedRawDecoderAccept Q)) 56 := by
  have h := independentRetrySuccessProbability_mono 56
    (reducedRawFourierEventMass_le_one G Q _) (reducedRawDecoder_success Q hG hQ hrQ d hQd)
  have hn : (99:ℝ)/100 ≤ independentRetrySuccessProbability ((2:ℝ)/25) 56 := by
    norm_num [independentRetrySuccessProbability]
  exact hn.trans h
end
end ShorECDLP.Paper2607_13816
