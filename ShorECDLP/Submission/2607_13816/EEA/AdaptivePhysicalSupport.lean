import ShorECDLP.Submission.«2607_13816».EEA.PhysicalSupport

/-! Adaptive schedule support follows from the literal coherent streams, without
expanding measurement histories. The forward production allocation uses 580 wires. -/
namespace ShorECDLP.Paper2607_13816
open Quantum

theorem indexedScheduleAdaptive_wires_subset (r : IndexedStepRegisters) (n start count : Nat) :
    (indexedScheduleAdaptive r n start count).wires ⊆
      circuitWires (indexedScheduleUnitary r n start count) := by
  induction count generalizing start with
  | zero => simp [indexedScheduleAdaptive,indexedScheduleUnitary,AdaptiveCircuit.wires,circuitWires]
  | succ count ih =>
    have hs := indexedStepAdaptive_wires_subset r n start
    have ht := ih (start+1)
    simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs ht
    intro w hw
    simp only [indexedScheduleAdaptive,indexedScheduleUnitary,modularWires_seq,
      circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
    aesop

theorem indexedScheduleInverseAdaptive_wires_subset (r : IndexedStepRegisters) (n start count : Nat) :
    (indexedScheduleInverseAdaptive r n start count).wires ⊆
      circuitWires (indexedScheduleInverseUnitary r n start count) := by
  induction count generalizing start with
  | zero => simp [indexedScheduleInverseAdaptive,indexedScheduleInverseUnitary,AdaptiveCircuit.wires,circuitWires]
  | succ count ih =>
    have hs := indexedStepInverseAdaptive_wires_subset r n start
    have ht := ih (start+1)
    simp only [List.subset_def,circuitWires,List.mem_flatMap] at hs ht
    intro w hw
    simp only [indexedScheduleInverseAdaptive,indexedScheduleInverseUnitary,modularWires_seq,
      circuitWires,List.flatMap_append,List.mem_append] at hw ⊢
    aesop

/-- Every gate and measurement in the actual forward EEA uses the fixed production allocation. -/
theorem secp256k1EEAForwardAdaptive_wires_subset :
    (secp256k1EEAForwardAdaptive indexedStepProductionRegisters).wires ⊆ List.range 580 := by
  intro w hw
  have hs := indexedScheduleAdaptive_wires_subset indexedStepProductionRegisters 256 1 secp256k1ScheduleLength
  have hm := hs hw
  obtain ⟨g,hg,hwg⟩ := List.mem_flatMap.mp hm
  exact secp256k1EEAForwardUnitary_production_usesOnly g hg w hwg

/-- The bound counts all distinct wire labels across the full adaptive tree. -/
theorem secp256k1EEAForwardAdaptive_qubitCount :
    (secp256k1EEAForwardAdaptive indexedStepProductionRegisters).qubitCount ≤ 580 := by
  have hs : (secp256k1EEAForwardAdaptive indexedStepProductionRegisters).wires.dedup.toFinset ⊆
      (List.range 580).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (secp256k1EEAForwardAdaptive_wires_subset (by simpa using hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 580))] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc
end ShorECDLP.Paper2607_13816
