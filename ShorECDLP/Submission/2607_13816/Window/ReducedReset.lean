import ShorECDLP.Submission.«2607_13816».Window.ReducedSecp
import ShorECDLP.Submission.«2607_13816».Window.ResetFrame
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Reset the complete physical allocation between trials. -/
def reducedResetWires : List Wire := List.range 839++reducedPhaseWires
def reducedResetProgram : AdaptiveCircuit := measureResetWithCorrection reducedResetWires (fun _ => [])
private theorem reset_nodup : reducedResetWires.Nodup := by
  simp only [reducedResetWires,reducedPhaseWires,List.nodup_append]
  refine ⟨List.nodup_range,⟨List.nodup_range',List.nodup_range',?_⟩,?_⟩
  · intro w hw v hv he
    subst v
    simp only [List.mem_range'_1] at hw hv
    omega
  · intro w hw v hv he
    subst v
    simp only [List.mem_range,List.mem_append,List.mem_range'_1] at hw hv
    omega

theorem reducedReset_support : reducedResetProgram.wires ⊆ reducedResetWires :=
  resetRegister_support reducedResetWires

theorem reducedReset_clean (b : InstrumentBranch) (hb : b∈reducedResetProgram.run) (ψ : State) :
    SupportedOn (Clean reducedResetWires) (b.kraus ψ) :=
  resetRegister_clean reducedResetWires reset_nodup b hb ψ

theorem reducedReset_resources : reducedResetProgram.tCount=0 ∧
    reducedResetProgram.measurementCount=1303 := by
  exact ⟨resetRegister_tCount reducedResetWires, (resetRegister_measurements reducedResetWires).trans (by simp [reducedResetWires,reducedPhaseWires])⟩
def resetReducedWindowTrial (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (reducedSecpWindowProgram Q hrQ).seq reducedResetProgram

theorem resetReducedWindowTrial_clean (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetReducedWindowTrial Q hrQ).run) (ψ : State) :
    SupportedOn (Clean reducedResetWires) (b.kraus ψ) := by
  rw [resetReducedWindowTrial,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,_,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,ha,rfl⟩ := List.mem_map.mp hb
  exact reducedReset_clean after ha (before.kraus ψ)

private theorem direct_support (Q : Point) (hrQ : order • Q=0) :
    (reducedSecpWindowProgram Q hrQ).wires ⊆ reducedResetWires := by
  unfold reducedSecpWindowProgram
  split
  · exact List.nil_subset _
  · exact reducedWindowTrialProgram_support _ _ _ _ _ _

theorem resetReducedWindowTrial_support (Q : Point) (hrQ : order • Q=0) :
    (resetReducedWindowTrial Q hrQ).wires ⊆ reducedResetWires := by
  intro w hw
  rw [resetReducedWindowTrial,modularWires_seq] at hw
  rcases hw with h | h
  · exact direct_support Q hrQ h
  · exact reducedReset_support h

theorem resetReducedWindowTrial_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (resetReducedWindowTrial Q hrQ).qubitCount≤1303 := by
  have hs : (resetReducedWindowTrial Q hrQ).wires.dedup.toFinset ⊆ reducedResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (resetReducedWindowTrial_support Q hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,reducedResetWires,reducedPhaseWires,List.length_append,List.length_range,List.length_range'] using hc

theorem resetReducedWindowTrial_resources (Q : Point) (hrQ : order • Q=0) :
    (resetReducedWindowTrial Q hrQ).tCount=(reducedSecpWindowProgram Q hrQ).tCount ∧
    (resetReducedWindowTrial Q hrQ).measurementCount=(reducedSecpWindowProgram Q hrQ).measurementCount+1303 := by
  have ht := modularGateCount_seq tCost (reducedSecpWindowProgram Q hrQ) reducedResetProgram
  simp only [gidneyGateCount_tCount,reducedReset_resources.1,Nat.add_zero] at ht
  have hm := modularMeasurements_seq (reducedSecpWindowProgram Q hrQ) reducedResetProgram
  rw [reducedReset_resources.2] at hm
  exact ⟨ht,hm⟩
/-- Starting from zero, the reset trial returns each branch to the same zero basis state. -/
theorem resetReducedWindowTrial_zero_support (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(resetReducedWindowTrial Q hrQ).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  intro s hs
  funext w
  by_cases hw : w∈reducedResetWires
  · exact resetReducedWindowTrial_clean Q hrQ b hb (ket zeroBasisState) s hs w hw
  · have hn : w∉(resetReducedWindowTrial Q hrQ).wires := fun h => hw (resetReducedWindowTrial_support Q hrQ h)
    exact AdaptiveCircuit.branch_frame (resetReducedWindowTrial Q hrQ) w false hn b hb
      (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs
theorem resetReducedWindowTrial_zero_branch (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(resetReducedWindowTrial Q hrQ).run) :
    b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (resetReducedWindowTrial_zero_support Q hrQ b hb)
end
end ShorECDLP.Paper2607_13816
