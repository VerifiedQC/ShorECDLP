import ShorECDLP.Submission.«2607_13816».Window.ReducedCandidate
import ShorECDLP.Submission.«2607_13816».Window.PhysicalRepetition
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
open scoped BigOperators
noncomputable section
private theorem output_nonneg (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G)
    (out : Fin (2^256) × Fin (2^208)) : 0≤reducedSecpWindowOutputMass Q hrQ out := by
  unfold reducedSecpWindowOutputMass
  split
  · split <;> norm_num
  · rw [reducedWindowTrialFiniteOutputMass_eq order_prime G Q _ _ _ _ generator_order d hQd]
    exact asymmetricPairMass_nonneg order 256 208 d out
theorem reducedSecpWindowSuccessMass_le_one (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    reducedSecpWindowSuccessMass Q hrQ d≤1 :=
  (selectedMass_le_total (fun out => reducedSecpWindowPostprocess Q out=some (d:ZMod order))
    (reducedSecpWindowOutputMass Q hrQ) (output_nonneg Q hrQ d hQd)).trans_eq
      (reducedSecpWindowOutputMass_total Q hrQ d hQd)
/-- At least 16.3 percent success in one concrete run. -/
theorem reducedSecpWindowSuccessMass_numeric (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (163:ℝ)/1000≤reducedSecpWindowSuccessMass Q hrQ d :=
  secpSuccessBound_numeric.trans (reducedSecpWindowSuccessMass_lower Q hrQ d hQd)
/-- Twenty-six independent measured runs exceed 99 percent success. -/
theorem reducedSecpWindowRetrySuccess (Q : Point) (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ independentRetrySuccessProbability (reducedSecpWindowSuccessMass Q hrQ d) 26 := by
  have h := independentRetrySuccessProbability_mono 26 (reducedSecpWindowSuccessMass_le_one Q hrQ d hQd)
    (reducedSecpWindowSuccessMass_numeric Q hrQ d hQd)
  have hn : (99:ℝ)/100 ≤ independentRetrySuccessProbability ((163:ℝ)/1000) 26 := by
    norm_num [independentRetrySuccessProbability]
  exact hn.trans h/-- Twenty-six physical trials, each restoring the same allocated quantum wires. -/
def reducedSecpWindowRepeatedProgram (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit :=
  repeatWindowProgram (resetReducedWindowTrial Q hrQ) 26
/-- A public decoder returns the first verified scalar, or none if all trials fail. -/
def reducedSecpWindowRepeatedCandidate (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (ZMod order) :=
  repeatWindowCandidate (resetReducedWindowTrial Q hrQ) (resetReducedWindowCandidate Q hrQ) 26 hist

theorem reducedSecpWindowRepeatedCandidate_sound (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) (hist : List Bool) (c : ZMod order)
    (hc : reducedSecpWindowRepeatedCandidate Q hrQ hist=some c) : c=(d:ZMod order) :=
  repeatWindowCandidate_sound _ _ (d:ZMod order) (resetReducedWindowCandidate_sound Q hrQ d hQd) 26 hist c hc

theorem reducedSecpWindowRepeatedCandidate_mass (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass ((reducedSecpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (reducedSecpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)=
      independentRetrySuccessProbability (reducedSecpWindowSuccessMass Q hrQ d) 26 := by
  simp only [reducedSecpWindowRepeatedProgram,reducedSecpWindowRepeatedCandidate,repeatWindowCandidate_failed]
  rw [repeatWindowSuccess_mass _ _ (resetReducedWindowTrial_zero_branch Q hrQ)
    (resetReducedWindowTrial_total Q hrQ d hQd),resetReducedWindowCandidate_mass Q hrQ d hQd]

theorem reducedSecpWindowRepeatedCandidate_success (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass ((reducedSecpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (reducedSecpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState) := by
  rw [reducedSecpWindowRepeatedCandidate_mass Q hrQ d hQd]
  exact reducedSecpWindowRetrySuccess Q hrQ d hQd

theorem reducedSecpWindowRepeatedProgram_clean (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(reducedSecpWindowRepeatedProgram Q hrQ).run) :
    b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  repeatWindowProgram_zero _ (resetReducedWindowTrial_zero_branch Q hrQ) 26 b hb

theorem reducedSecpWindowRepeatedProgram_resources (Q : Point) (hrQ : order • Q=0) :
    (reducedSecpWindowRepeatedProgram Q hrQ).tCount=26*(reducedSecpWindowProgram Q hrQ).tCount ∧
    (reducedSecpWindowRepeatedProgram Q hrQ).measurementCount=
      26*((reducedSecpWindowProgram Q hrQ).measurementCount+1303) := by
  have h := repeatWindowProgram_resources (resetReducedWindowTrial Q hrQ) 26
  rw [resetReducedWindowTrial_resources Q hrQ |>.1,resetReducedWindowTrial_resources Q hrQ |>.2] at h
  exact h

theorem reducedSecpWindowRepeatedProgram_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (reducedSecpWindowRepeatedProgram Q hrQ).qubitCount≤1303 := by
  have hs : (reducedSecpWindowRepeatedProgram Q hrQ).wires.dedup.toFinset ⊆ reducedResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (resetReducedWindowTrial_support Q hrQ
      (repeatWindowProgram_support _ 26 (by simpa using hw)))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,reducedResetWires,reducedPhaseWires,List.length_append,List.length_range,List.length_range'] using hc
end
end ShorECDLP.Paper2607_13816
