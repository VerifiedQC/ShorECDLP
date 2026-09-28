import ShorECDLP.Submission.«2607_13816».Window.StreamSamplingSuccess
import ShorECDLP.Submission.«2607_13816».Window.RawRepetition
/-! Actual streaming trials reset their complete support before repeating.
Acceptance uses only each trial prefix; all reset outcomes remain in the instrument. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def streamResetWires (Q : Point) : List Wire := (streamRawTrial G Q).wires.dedup
def streamTrialReset (Q : Point) : AdaptiveCircuit :=
  measureResetWithCorrection (streamResetWires Q) (fun _ => [])
def streamResetTrial (Q : Point) : AdaptiveCircuit := (streamRawTrial G Q).seq (streamTrialReset Q)
attribute [local irreducible] streamRawTrial streamResetWires streamTrialReset

def streamResetCandidate (Q : Point) (hist : List Bool) : Option (ZMod order) := do
  let rest ← consumeAdaptiveHistory (streamRawTrial G Q) hist
  streamRawPublicDecode Q (hist.take (hist.length-rest.length))
private theorem candidate_seq (Q : Point) (b a : InstrumentBranch) (hb : b∈(streamRawTrial G Q).run) :
    streamResetCandidate Q (b.seq a).history=streamRawPublicDecode Q b.history := by
  simp only [streamResetCandidate,InstrumentBranch.seq,consumeAdaptiveHistory_run _ b hb,
    Option.bind,Bind.bind,List.length_append,Nat.add_sub_cancel_right,List.take_left]
theorem streamResetTrial_total (Q : Point) : (streamResetTrial Q).run.bornMass (ket zeroBasisState)=1 := by
  rw [streamResetTrial,AdaptiveCircuit.run_seq,streamTrialReset,
    instrumentMass_seq_preserving _ _ _ (resetRegister_mass _),streamRawTrial_total]
theorem streamResetCandidate_mass (Q : Point) :
    Instrument.bornMass ((streamResetTrial Q).run.filter
      (fun b => (streamResetCandidate Q b.history).isSome)) (ket zeroBasisState)=
    streamRawFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  rw [streamResetTrial,AdaptiveCircuit.run_seq]
  rw [instrumentFilter_seq_first _ _ (fun b => (streamRawPublicDecode Q b.history).isSome) _ (by
    intro b hb a _; rw [candidate_seq Q b a hb])]
  rw [streamTrialReset,instrumentMass_seq_preserving _ _ _ (resetRegister_mass _),streamRawPublicDecode_eventMass]
theorem streamResetCandidate_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : streamResetCandidate Q hist=some c) : c=(d:ZMod order) := by
  unfold streamResetCandidate at hc
  obtain ⟨rest,_,hc⟩ := Option.bind_eq_some_iff.mp hc
  exact streamRawPublicDecode_sound Q d hQd _ c hc
private theorem reset_support (Q : Point) : (streamResetTrial Q).wires ⊆ streamResetWires Q := by
  intro w hw
  rw [streamResetTrial, modularWires_seq] at hw
  rcases hw with hw | hw
  · simpa only [streamResetWires, List.mem_dedup] using hw
  · exact resetRegister_support _ (by simpa only [streamTrialReset] using hw)

/-- Every complete trial/reset branch restores the same zero basis state. -/
theorem streamResetTrial_zero_support (Q : Point) (b : InstrumentBranch)
    (hb : b∈(streamResetTrial Q).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  have hc : SupportedOn (Clean (streamResetWires Q)) (b.kraus (ket zeroBasisState)) := by
    rw [streamResetTrial, AdaptiveCircuit.run_seq] at hb
    obtain ⟨before, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨after, ha, rfl⟩ := List.mem_map.mp hb
    exact resetRegister_clean _ (by rw [streamResetWires]; exact List.nodup_dedup _)
      after (by simpa only [streamTrialReset] using ha) (before.kraus (ket zeroBasisState))
  intro s hs
  funext w
  by_cases hw : w∈streamResetWires Q
  · exact hc s hs w hw
  · exact AdaptiveCircuit.branch_frame (streamResetTrial Q) w false
      (fun h => hw (reset_support Q h)) b hb (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs

theorem streamResetTrial_zero_branch (Q : Point) (b : InstrumentBranch)
    (hb : b∈(streamResetTrial Q).run) :
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (streamResetTrial_zero_support Q b hb)
def streamRepeatedProgram (Q : Point) : AdaptiveCircuit := repeatWindowProgram (streamResetTrial Q) 56
def streamRepeatedCandidate (Q : Point) (hist : List Bool) : Option (ZMod order) :=
  repeatWindowCandidate (streamResetTrial Q) (streamResetCandidate Q) 56 hist
theorem streamRepeatedCandidate_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : streamRepeatedCandidate Q hist=some c) : c=(d:ZMod order) :=
  repeatWindowCandidate_sound _ _ (d:ZMod order) (streamResetCandidate_sound Q d hQd) 56 hist c hc
theorem streamRepeatedCandidate_mass (Q : Point) :
    Instrument.bornMass ((streamRepeatedProgram Q).run.filter
      (fun b => (streamRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState)=
    independentRetrySuccessProbability (streamRawFourierEventMass G Q (reducedRawDecoderAccept Q)) 56 := by
  simp only [streamRepeatedProgram,streamRepeatedCandidate,repeatWindowCandidate_failed]
  rw [repeatWindowSuccess_mass _ _ (streamResetTrial_zero_branch Q) (streamResetTrial_total Q),streamResetCandidate_mass]
theorem streamRepeatedCandidate_success (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass ((streamRepeatedProgram Q).run.filter
      (fun b => (streamRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState) := by
  rw [streamRepeatedCandidate_mass]
  have hu : streamRawFourierEventMass G Q (reducedRawDecoderAccept Q) ≤ 1 := by
    unfold streamRawFourierEventMass
    exact (Instrument.bornMass_filter_le _ _ _).trans_eq (streamRawTrial_total G Q)
  have h := independentRetrySuccessProbability_mono 56 hu (streamRawDecoder_success Q hG hQ hrQ d hQd)
  have hn : (99:ℝ)/100 ≤ independentRetrySuccessProbability ((2:ℝ)/25) 56 := by
    norm_num [independentRetrySuccessProbability]
  exact hn.trans h
theorem streamRepeatedProgram_zero (Q : Point) (b : InstrumentBranch)
    (hb : b∈(streamRepeatedProgram Q).run) :
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  repeatWindowProgram_zero (streamResetTrial Q) (streamResetTrial_zero_branch Q) 56 b hb

theorem streamRepeatedProgram_qubits (Q : Point) : (streamRepeatedProgram Q).qubitCount ≤ 855 := by
  have hs : (streamRepeatedProgram Q).wires.dedup.toFinset ⊆ streamAllocation.toFinset := by
    intro w hw
    have hr := repeatWindowProgram_support (streamResetTrial Q) 56
      (show w∈(streamRepeatedProgram Q).wires by simpa using hw)
    have ht := reset_support Q hr
    have ho : w∈(streamRawTrial G Q).wires := by
      simpa only [streamResetWires,List.mem_dedup] using ht
    exact List.mem_toFinset.mpr (streamRawTrial_support G Q ho)
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,streamAllocation,streamAddress,List.length_append,
    List.length_range,List.length_range'] using hc

theorem streamRepeatedProgram_measurements (Q : Point) :
    (streamRepeatedProgram Q).measurementCount ≤ 47471340560 := by
  have hn : (streamResetWires Q).length ≤ 855 := by
    simpa only [streamResetWires,AdaptiveCircuit.qubitCount] using streamRawTrial_qubitCount G Q
  rw [streamRepeatedProgram,(repeatWindowProgram_resources _ _).2,streamResetTrial,
    modularMeasurements_seq,streamRawTrial_measurementCount,streamTrialReset,resetRegister_measurements]
  omega

theorem streamRepeatedProgram_certificate (Q : Point) (hG : G≠0) (hQ : Q≠0)
    (hrQ : order • Q=0) (d : Nat) (hQd : Q=d • G) :
    (streamRepeatedProgram Q).qubitCount ≤ 855 ∧
    (streamRepeatedProgram Q).measurementCount ≤ 47471340560 ∧
    (99:ℝ)/100 ≤ Instrument.bornMass ((streamRepeatedProgram Q).run.filter
      (fun b => (streamRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState) ∧
    (∀ hist c,streamRepeatedCandidate Q hist=some c → c=(d:ZMod order)) :=
  ⟨streamRepeatedProgram_qubits Q,streamRepeatedProgram_measurements Q,
    streamRepeatedCandidate_success Q hG hQ hrQ d hQd,streamRepeatedCandidate_sound Q d hQd⟩

end
end ShorECDLP.Paper2607_13816
