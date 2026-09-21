import ShorECDLP.Submission.«2607_13816».Window.RawReset
import ShorECDLP.Submission.«2607_13816».Window.PhysicalRepetition
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Fifty-six physical trials, each preparing from zero and resetting its complete support. -/
def rawRepeatedProgram (Q : Point) : AdaptiveCircuit := repeatWindowProgram (resetRawTrial Q) 56
/-- Return the first candidate verified against the public point. -/
def rawRepeatedCandidate (Q : Point) (hist : List Bool) : Option (ZMod order) :=
  repeatWindowCandidate (resetRawTrial Q) (resetRawCandidate Q) 56 hist

theorem rawRepeatedCandidate_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : rawRepeatedCandidate Q hist=some c) : c=(d:ZMod order) :=
  repeatWindowCandidate_sound _ _ (d:ZMod order) (resetRawCandidate_sound Q d hQd) 56 hist c hc

/-- The independent-trial formula is derived from this actual sequential instrument. -/
theorem rawRepeatedCandidate_mass (Q : Point) :
    Instrument.bornMass ((rawRepeatedProgram Q).run.filter
      (fun b => (rawRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState)=
    independentRetrySuccessProbability (reducedRawFourierEventMass G Q (reducedRawDecoderAccept Q)) 56 := by
  simp only [rawRepeatedProgram, rawRepeatedCandidate, repeatWindowCandidate_failed]
  rw [repeatWindowSuccess_mass _ _ (resetRawTrial_zero_branch Q) (resetRawTrial_total Q), resetRawCandidate_mass]

/-- At least 99 percent correct acceptance in the concrete 56-trial raw program. -/
theorem rawRepeatedCandidate_success (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass ((rawRepeatedProgram Q).run.filter
      (fun b => (rawRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState) := by
  rw [rawRepeatedCandidate_mass]
  exact reducedRawDecoder_independent_retry Q hG hQ hrQ d hQd

/-- The repeated program also ends in zero in every branch. -/
theorem rawRepeatedProgram_zero (Q : Point) (b : InstrumentBranch) (hb : b∈(rawRepeatedProgram Q).run) :
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  repeatWindowProgram_zero (resetRawTrial Q) (resetRawTrial_zero_branch Q) 56 b hb
end
end ShorECDLP.Paper2607_13816
