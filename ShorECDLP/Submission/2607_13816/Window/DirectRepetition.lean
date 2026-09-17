import ShorECDLP.Submission.«2607_13816».Window.DirectCandidate
import ShorECDLP.Submission.«2607_13816».Window.PhysicalRepetition
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Twenty-six physical trials, each restoring the same allocated quantum wires. -/
def directSecpWindowRepeatedProgram (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit :=
  repeatWindowProgram (resetDirectWindowTrial Q hrQ) 26
/-- A public decoder returns the first verified scalar, or none if all trials fail. -/
def directSecpWindowRepeatedCandidate (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (ZMod order) :=
  repeatWindowCandidate (resetDirectWindowTrial Q hrQ) (resetDirectWindowCandidate Q hrQ) 26 hist

theorem directSecpWindowRepeatedCandidate_sound (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) (hist : List Bool) (c : ZMod order)
    (hc : directSecpWindowRepeatedCandidate Q hrQ hist=some c) : c=(d:ZMod order) :=
  repeatWindowCandidate_sound _ _ (d:ZMod order) (resetDirectWindowCandidate_sound Q hrQ d hQd) 26 hist c hc

theorem directSecpWindowRepeatedCandidate_mass (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass ((directSecpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (directSecpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)=
      independentRetrySuccessProbability (secpWindowSuccessMass Q hrQ d) 26 := by
  simp only [directSecpWindowRepeatedProgram,directSecpWindowRepeatedCandidate,repeatWindowCandidate_failed]
  rw [repeatWindowSuccess_mass _ _ (resetDirectWindowTrial_zero_branch Q hrQ)
    (resetDirectWindowTrial_total Q hrQ d hQd),resetDirectWindowCandidate_mass Q hrQ d hQd]

theorem directSecpWindowRepeatedCandidate_success (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass ((directSecpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (directSecpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState) := by
  rw [directSecpWindowRepeatedCandidate_mass Q hrQ d hQd]
  exact secpWindowRetrySuccess Q hrQ d hQd

theorem directSecpWindowRepeatedProgram_clean (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(directSecpWindowRepeatedProgram Q hrQ).run) :
    b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  repeatWindowProgram_zero _ (resetDirectWindowTrial_zero_branch Q hrQ) 26 b hb

theorem directSecpWindowRepeatedProgram_resources (Q : Point) (hrQ : order • Q=0) :
    (directSecpWindowRepeatedProgram Q hrQ).tCount=26*(directSecpWindowProgram Q hrQ).tCount ∧
    (directSecpWindowRepeatedProgram Q hrQ).measurementCount=
      26*((directSecpWindowProgram Q hrQ).measurementCount+1383) := by
  have h := repeatWindowProgram_resources (resetDirectWindowTrial Q hrQ) 26
  rw [resetDirectWindowTrial_resources Q hrQ |>.1,resetDirectWindowTrial_resources Q hrQ |>.2] at h
  exact h

theorem directSecpWindowRepeatedProgram_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (directSecpWindowRepeatedProgram Q hrQ).qubitCount≤1383 := by
  have hs : (directSecpWindowRepeatedProgram Q hrQ).wires.dedup.toFinset ⊆ windowResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (resetDirectWindowTrial_support Q hrQ
      (repeatWindowProgram_support _ 26 (by simpa using hw)))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,windowResetWires,List.length_append,List.length_range,List.length_range'] using hc
end
end ShorECDLP.Paper2607_13816
