import ShorECDLP.Submission.«2607_13816».Window.Secp
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
/-- Reset the complete physical allocation between trials. -/
def windowResetWires : List Wire := List.range 839++List.range' 855 544
def windowResetProgram : AdaptiveCircuit := measureResetWithCorrection windowResetWires (fun _ => [])
private theorem reset_clean (ws : List Wire) (hn : ws.Nodup) (b : InstrumentBranch)
    (hb : b∈(measureResetWithCorrection ws (fun _ => [])).run) (ψ : State) :
    SupportedOn (Clean ws) (b.kraus ψ) := by
  rw [run_measureResetWithCorrection] at hb
  obtain ⟨out,ho,rfl⟩ := List.mem_map.mp hb
  have h := xResetRegisterKraus_clean ws out ψ (mem_boolTranscripts_length ho) hn
  exact h
private theorem reset_wires (ws : List Wire) :
    (measureResetWithCorrection ws (fun _ => [])).wires ⊆ ws := by
  induction ws with
  | nil => exact List.Subset.refl _
  | cons w ws ih =>
    intro v hv
    simp only [measureResetWithCorrection,AdaptiveCircuit.wires,List.mem_cons,List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hv)
    · exact List.mem_cons_of_mem _ (ih hv)
private theorem reset_measurements (ws : List Wire) :
    (measureResetWithCorrection ws (fun _ => [])).measurementCount=ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [measureResetWithCorrection,AdaptiveCircuit.measurementCount,ih,Nat.add_comm]
private theorem reset_T (ws : List Wire) :
    (measureResetWithCorrection ws (fun _ => [])).tCount=0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [measureResetWithCorrection,AdaptiveCircuit.tCount,ih]
private theorem reset_nodup : windowResetWires.Nodup := by
  rw [windowResetWires,List.nodup_append]
  refine ⟨List.nodup_range, List.nodup_range', ?_⟩
  intro w hw v hv he
  subst v
  simp only [List.mem_range,List.mem_range'] at hw hv
  omega

theorem windowReset_support : windowResetProgram.wires ⊆ windowResetWires :=
  reset_wires windowResetWires

theorem windowReset_clean (b : InstrumentBranch) (hb : b∈windowResetProgram.run) (ψ : State) :
    SupportedOn (Clean windowResetWires) (b.kraus ψ) :=
  reset_clean windowResetWires reset_nodup b hb ψ

def resetWindowTrial (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit :=
  (secpWindowProgram Q hrQ).seq windowResetProgram

theorem resetWindowTrial_clean (Q : Point) (hrQ : order • Q=0) (b : InstrumentBranch)
    (hb : b∈(resetWindowTrial Q hrQ).run) (ψ : State) :
    SupportedOn (Clean windowResetWires) (b.kraus ψ) := by
  rw [resetWindowTrial,AdaptiveCircuit.run_seq] at hb
  obtain ⟨before,_,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨after,ha,rfl⟩ := List.mem_map.mp hb
  exact windowReset_clean after ha (before.kraus ψ)

theorem windowReset_resources : windowResetProgram.tCount=0 ∧
    windowResetProgram.measurementCount=1383 := by
  exact ⟨reset_T windowResetWires, (reset_measurements windowResetWires).trans (by decide +kernel)⟩
private theorem secp_support (Q : Point) (hrQ : order • Q=0) :
    (secpWindowProgram Q hrQ).wires ⊆ windowResetWires := by
  unfold secpWindowProgram
  split
  · exact List.nil_subset _
  · exact windowTrialProgram_support _ _ _ _ _ _

theorem resetWindowTrial_support (Q : Point) (hrQ : order • Q=0) :
    (resetWindowTrial Q hrQ).wires ⊆ windowResetWires := by
  intro w hw
  rw [resetWindowTrial,modularWires_seq] at hw
  rcases hw with h | h
  · exact secp_support Q hrQ h
  · exact windowReset_support h

theorem resetWindowTrial_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (resetWindowTrial Q hrQ).qubitCount≤1383 := by
  have hs : (resetWindowTrial Q hrQ).wires.dedup.toFinset ⊆ windowResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (resetWindowTrial_support Q hrQ (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,windowResetWires,List.length_append,List.length_range,List.length_range'] using hc

theorem resetWindowTrial_resources (Q : Point) (hrQ : order • Q=0) :
    (resetWindowTrial Q hrQ).tCount=(secpWindowProgram Q hrQ).tCount ∧
    (resetWindowTrial Q hrQ).measurementCount=(secpWindowProgram Q hrQ).measurementCount+1383 := by
  have ht := modularGateCount_seq tCost (secpWindowProgram Q hrQ) windowResetProgram
  simp only [gidneyGateCount_tCount,windowReset_resources.1,Nat.add_zero] at ht
  have hm := modularMeasurements_seq (secpWindowProgram Q hrQ) windowResetProgram
  rw [windowReset_resources.2] at hm
  exact ⟨ht,hm⟩

end
end ShorECDLP.Paper2607_13816
