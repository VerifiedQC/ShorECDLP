import ShorECDLP.Submission.«2607_13816».Window.RawSuccess
import ShorECDLP.Submission.«2607_13816».Window.ResetFrame
import ShorECDLP.Submission.«2607_13816».Window.ResetOutcomes
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section

/-- One raw trial from zero, including the emitted Hadamards and root setup. -/
def preparedRawTrial (Q : Point) : AdaptiveCircuit :=
  .unitary reducedPhasePrepare (.unitary [.X 836] (reducedRawFourierProgram G Q))

/-- Reset every wire used by this actual trial, without assuming a numerical allocation bound. -/
def rawTrialResetWires (Q : Point) : List Wire := (preparedRawTrial Q).wires.dedup
def rawTrialReset (Q : Point) : AdaptiveCircuit :=
  measureResetWithCorrection (rawTrialResetWires Q) (fun _ => [])
def resetRawTrial (Q : Point) : AdaptiveCircuit := (preparedRawTrial Q).seq (rawTrialReset Q)
attribute [local irreducible] preparedRawTrial rawTrialResetWires rawTrialReset reducedRawFourierProgram

private theorem unitary_selected (c : Circuit) (a : AdaptiveCircuit) (accept : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((AdaptiveCircuit.unitary c a).run.filter (fun b => accept b.history)) ψ =
      Instrument.bornMass (a.run.filter (fun b => accept b.history)) (Quantum.run c ψ) := by
  simp only [AdaptiveCircuit.run, List.filter_map, Instrument.bornMass, List.map_map]
  rfl

/-- Preparation emits no classical outcomes and gives precisely the raw entry state. -/
theorem preparedRawTrial_selected (Q : Point) (accept : List Bool → Bool) :
    Instrument.bornMass ((preparedRawTrial Q).run.filter (fun b => accept b.history)) (ket zeroBasisState)=
      Instrument.bornMass ((reducedRawFourierProgram G Q).run.filter (fun b => accept b.history)) reducedRawEntryState := by
  rw [preparedRawTrial, unitary_selected, unitary_selected]
  rfl

theorem preparedRawTrial_total (Q : Point) :
    (preparedRawTrial Q).run.bornMass (ket zeroBasisState)=1 := by
  have h := preparedRawTrial_selected Q (fun _ => true)
  simp only [List.filter_true] at h
  rw [h, reducedRawFourierProgram, AdaptiveCircuit.run_seq,
    instrumentMass_seq_preserving _ _ _ (AdaptiveCircuit.run_preservesBornMass _ reducedFourierProgram_wellFormed),
    reducedRawProgram_bornMass, reducedRawEntryState_normSq]

/-- Parse the exact trial prefix and ignore only its subsequent reset outcomes. -/
def resetRawCandidate (Q : Point) (hist : List Bool) : Option (ZMod order) := do
  let rest ← consumeAdaptiveHistory (preparedRawTrial Q) hist
  let bits ← decodeReducedRawFourier G Q (hist.take (hist.length-rest.length))
  reducedRawPublicDecode Q bits

private theorem candidate_seq (Q : Point) (b a : InstrumentBranch) (hb : b∈(preparedRawTrial Q).run) :
    resetRawCandidate Q (b.seq a).history=
      (decodeReducedRawFourier G Q b.history).bind (reducedRawPublicDecode Q) := by
  simp only [resetRawCandidate, InstrumentBranch.seq, consumeAdaptiveHistory_run _ b hb,
    Option.bind, Bind.bind, List.length_append, Nat.add_sub_cancel_right, List.take_left]

/-- Reset preserves the total mass of the full trial. -/
theorem resetRawTrial_total (Q : Point) : (resetRawTrial Q).run.bornMass (ket zeroBasisState)=1 := by
  rw [resetRawTrial, AdaptiveCircuit.run_seq, rawTrialReset,
    instrumentMass_seq_preserving _ _ _ (resetRegister_mass _), preparedRawTrial_total]

/-- Appending reset measurements preserves the selected public-decoder event exactly. -/
theorem resetRawCandidate_mass (Q : Point) :
    Instrument.bornMass ((resetRawTrial Q).run.filter
      (fun b => (resetRawCandidate Q b.history).isSome)) (ket zeroBasisState)=
    reducedRawFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  rw [resetRawTrial, AdaptiveCircuit.run_seq]
  rw [instrumentFilter_seq_first _ _
    (fun b => ((decodeReducedRawFourier G Q b.history).bind (reducedRawPublicDecode Q)).isSome) _ (by
      intro b hb a _; rw [candidate_seq Q b a hb])]
  rw [rawTrialReset, instrumentMass_seq_preserving _ _ _ (resetRegister_mass _)]
  rw [preparedRawTrial_selected Q (fun hist => ((decodeReducedRawFourier G Q hist).bind (reducedRawPublicDecode Q)).isSome)]
  unfold reducedRawFourierEventMass
  apply congrArg (fun I => Instrument.bornMass I reducedRawEntryState)
  apply List.filter_congr
  intro b _
  cases decodeReducedRawFourier G Q b.history <;> rfl

theorem resetRawCandidate_sound (Q : Point) (d : Nat) (hQd : Q=d • G)
    (hist : List Bool) (c : ZMod order) (hc : resetRawCandidate Q hist=some c) : c=(d:ZMod order) := by
  unfold resetRawCandidate at hc
  obtain ⟨rest, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨bits, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  exact reducedRawPublicDecode_sound Q d hQd bits c hc

private theorem reset_support (Q : Point) : (resetRawTrial Q).wires ⊆ rawTrialResetWires Q := by
  intro w hw
  rw [resetRawTrial, modularWires_seq] at hw
  rcases hw with hw | hw
  · simpa only [rawTrialResetWires, List.mem_dedup] using hw
  · exact resetRegister_support _ (by simpa only [rawTrialReset] using hw)

/-- Every complete trial/reset branch restores the same zero basis state. -/
theorem resetRawTrial_zero_support (Q : Point) (b : InstrumentBranch)
    (hb : b∈(resetRawTrial Q).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  have hc : SupportedOn (Clean (rawTrialResetWires Q)) (b.kraus (ket zeroBasisState)) := by
    rw [resetRawTrial, AdaptiveCircuit.run_seq] at hb
    obtain ⟨before, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨after, ha, rfl⟩ := List.mem_map.mp hb
    exact resetRegister_clean _ (by rw [rawTrialResetWires]; exact List.nodup_dedup _)
      after (by simpa only [rawTrialReset] using ha) (before.kraus (ket zeroBasisState))
  intro s hs
  funext w
  by_cases hw : w∈rawTrialResetWires Q
  · exact hc s hs w hw
  · exact AdaptiveCircuit.branch_frame (resetRawTrial Q) w false
      (fun h => hw (reset_support Q h)) b hb (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs

theorem resetRawTrial_zero_branch (Q : Point) (b : InstrumentBranch)
    (hb : b∈(resetRawTrial Q).run) :
    b.kraus (ket zeroBasisState)=(b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (resetRawTrial_zero_support Q b hb)
end
end ShorECDLP.Paper2607_13816
