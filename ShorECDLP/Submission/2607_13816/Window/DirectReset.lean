import ShorECDLP.Submission.«2607_13816».Window.DirectSecp
import ShorECDLP.Submission.«2607_13816».Window.ResetFrame
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
def resetDirectWindowTrial (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (directSecpWindowProgram Q hrQ).seq windowResetProgram

theorem resetDirectWindowTrial_clean (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetDirectWindowTrial Q hrQ).run) (ψ : State) :
    SupportedOn (Clean windowResetWires) (b.kraus ψ) := by
  rw [resetDirectWindowTrial,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,_,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,ha,rfl⟩ := List.mem_map.mp hb
  exact windowReset_clean after ha (before.kraus ψ)

private theorem direct_support (Q : Point) (hrQ : order • Q=0) :
    (directSecpWindowProgram Q hrQ).wires ⊆ windowResetWires := by
  unfold directSecpWindowProgram
  split
  · exact List.nil_subset _
  · exact directWindowTrialProgram_support _ _ _ _ _ _

theorem resetDirectWindowTrial_support (Q : Point) (hrQ : order • Q=0) :
    (resetDirectWindowTrial Q hrQ).wires ⊆ windowResetWires := by
  intro w hw
  rw [resetDirectWindowTrial,modularWires_seq] at hw
  rcases hw with h | h
  · exact direct_support Q hrQ h
  · exact windowReset_support h

theorem resetDirectWindowTrial_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (resetDirectWindowTrial Q hrQ).qubitCount≤1383 := by
  have hs : (resetDirectWindowTrial Q hrQ).wires.dedup.toFinset ⊆ windowResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (resetDirectWindowTrial_support Q hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,windowResetWires,List.length_append,List.length_range,List.length_range'] using hc

theorem resetDirectWindowTrial_resources (Q : Point) (hrQ : order • Q=0) :
    (resetDirectWindowTrial Q hrQ).tCount=(directSecpWindowProgram Q hrQ).tCount ∧
    (resetDirectWindowTrial Q hrQ).measurementCount=(directSecpWindowProgram Q hrQ).measurementCount+1383 := by
  have ht := modularGateCount_seq tCost (directSecpWindowProgram Q hrQ) windowResetProgram
  simp only [gidneyGateCount_tCount,windowReset_resources.1,Nat.add_zero] at ht
  have hm := modularMeasurements_seq (directSecpWindowProgram Q hrQ) windowResetProgram
  rw [windowReset_resources.2] at hm
  exact ⟨ht,hm⟩
/-- Starting from zero, the reset trial returns each branch to the same zero basis state. -/
theorem resetDirectWindowTrial_zero_support (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(resetDirectWindowTrial Q hrQ).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  intro s hs
  funext w
  by_cases hw : w∈windowResetWires
  · exact resetDirectWindowTrial_clean Q hrQ b hb (ket zeroBasisState) s hs w hw
  · have hn : w∉(resetDirectWindowTrial Q hrQ).wires := fun h => hw (resetDirectWindowTrial_support Q hrQ h)
    exact AdaptiveCircuit.branch_frame (resetDirectWindowTrial Q hrQ) w false hn b hb
      (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs
theorem resetDirectWindowTrial_zero_branch (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(resetDirectWindowTrial Q hrQ).run) :
    b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (resetDirectWindowTrial_zero_support Q hrQ b hb)
end
end ShorECDLP.Paper2607_13816
