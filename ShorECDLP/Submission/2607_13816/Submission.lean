import ShorECDLP.Submission.«2607_13816».Window.RawCounts

/-!
# Current verified raw submission — secp256k1 (256 bits)

Target reference remains arXiv:2607.13816v2. These certify our current physical
raw circuit, without exceptional-input correction tables.

                         One trial          56 trials, with reset
Logical wires            ≤ 1,303            ≤ 1,303 (reused)
Toffoli count            2,229,177,063      124,833,915,528
T-model upper bound      15,604,293,609     873,840,442,104
Success probability      ≥ 8%              ≥ 99%

Success assumes a nonzero public point Q = d • G of order dividing the group
order, and G ≠ 0. Inputs start in the all-zero quantum state. One trial includes
preparation and Fourier measurements; the repeated program resets the complete
used support after each trial. It has 54,168 phase-rotation units per trial.

`tCount` charges 7 per CCX and 1 per phase rotation. The bounds are not synthesized
Clifford+T counts: rotation approximation, synthesis and error remain unspecified.
The public-point-checked decoder is a noncomputable specification, not an efficient
executable classical implementation. The measured inversion optimization is not
yet connected to this whole program. The 835-wire target remains open.
-/
namespace ShorECDLP.Paper2607_13816.Submission
open Quantum ShorECDLP.Secp256k1
noncomputable section

/-- One actual raw trial, including physical preparation and Fourier measurements. -/
def trial (Q : Point) : AdaptiveCircuit := preparedRawTrial Q

/-- Fifty-six actual trials, resetting and reusing the same wires. -/
def algorithm (Q : Point) : AdaptiveCircuit := rawRepeatedProgram Q

/-- Exact primitive counts for the same trial certified below. -/
theorem trial_counts (Q : Point) :
    (primitiveResources (trial Q)).toffoli = 2229177063 ∧
    (primitiveResources (trial Q)).phase = 54168 ∧
    (trial Q).measurementCount = 659347223 := preparedRawTrial_counts Q

/-- The numeric resource bounds apply to the actual prepared trial. -/
theorem trial_resources (Q : Point) :
    (trial Q).qubitCount ≤ 1303 ∧ (trial Q).tCount ≤ 15604293609 := by
  have ht := primitiveResources_T_le (trial Q)
  rw [(trial_counts Q).1, (trial_counts Q).2.1] at ht
  exact ⟨rawTrialResetWires_length Q, by omega⟩

/-- Single-run acceptance probability, summing all actual measurement histories. -/
theorem trial_success (Q : Point) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (hrQ : ShorECDLP.order • Q = 0) (d : Nat) (hd : Q = d • G) :
    (2 : ℝ) / 25 ≤ Instrument.bornMass ((trial Q).run.filter
      (fun b => ((decodeReducedRawFourier G Q b.history).map
        (reducedRawDecoderAccept Q)).getD false)) (ket zeroBasisState) := by
  rw [trial, preparedRawTrial_selected Q (fun hist =>
    ((decodeReducedRawFourier G Q hist).map (reducedRawDecoderAccept Q)).getD false)]
  exact reducedRawDecoder_success Q hG hQ hrQ d hd

/-- Same physical 56-trial circuit: resource bounds and accepted Born mass. -/
theorem certificate (Q : Point) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (hrQ : ShorECDLP.order • Q = 0) (d : Nat) (hd : Q = d • G) :
    (algorithm Q).qubitCount ≤ 1303 ∧
    (algorithm Q).tCount ≤ 873840442104 ∧
    (algorithm Q).measurementCount ≤ 36923517456 ∧
    (99 : ℝ) / 100 ≤ Instrument.bornMass ((algorithm Q).run.filter
      (fun b => (rawRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState) :=
  rawRepeatedProgram_success_resources Q hG hQ hrQ d hd

/-- Any returned scalar is the correct discrete logarithm modulo the group order. -/
theorem decoder_sound (Q : Point) (d : Nat) (hd : Q = d • G)
    (history : List Bool) (c : ZMod ShorECDLP.order)
    (hc : rawRepeatedCandidate Q history = some c) : c = (d : ZMod ShorECDLP.order) :=
  rawRepeatedCandidate_sound Q d hd history c hc

end
end ShorECDLP.Paper2607_13816.Submission
