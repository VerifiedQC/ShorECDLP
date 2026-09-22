import ShorECDLP.Submission.«2607_13816».EEA.MeasuredSupport
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapper
import ShorECDLP.Submission.«2607_13816».EEA.WrapperSupport
/-! Physical allocation of the actual measured inversion wrappers, across all branches. -/
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem seq_mono {a b c d : AdaptiveCircuit}
    (ha : a.wires ⊆ c.wires) (hb : b.wires ⊆ d.wires) :
    (a.seq b).wires ⊆ (c.seq d).wires := by
  intro w hw
  simp only [modularWires_seq] at hw ⊢
  exact hw.elim (fun h => Or.inl (ha h)) (fun h => Or.inr (hb h))
/-- Replacing the last H block does not enlarge the full adaptive step support. -/
theorem measuredIndexedStep_wires_subset (r : IndexedStepRegisters) (n T : Nat) :
    (measuredIndexedStep r n T).wires ⊆ (indexedStepAdaptive r n T).wires := by
  rw [measuredStepPrefix_factor]
  apply seq_mono (List.Subset.refl _)
  change (measuredBlockHForward r n T).wires ⊆ (AdaptiveCircuit.unitary (blockHForward r n T) .done).wires
  simpa only [AdaptiveCircuit.wires,List.append_nil] using measuredBlockHForward_wires_subset r n T
/-- Replacing the first inverse H block retains all original adaptive tail wires. -/
theorem measuredIndexedStepInverse_wires_subset (r : IndexedStepRegisters) (n T : Nat) :
    (measuredIndexedStepInverse r n T).wires ⊆ (indexedStepInverseAdaptive r n T).wires := by
  rw [indexedStepInverseAdaptive_factor]
  apply seq_mono (b := indexedStepInverseTailAdaptive r n T) (d := indexedStepInverseTailAdaptive r n T)
  · simpa only [AdaptiveCircuit.wires,List.append_nil] using measuredBlockHInverse_wires_subset r n T
  · exact List.Subset.refl _
/-- All branches of the measured schedule stay within the previous adaptive schedule. -/
theorem measuredIndexedSchedule_wires_subset (r : IndexedStepRegisters) (n start count : Nat) :
    (measuredIndexedSchedule r n start count).wires ⊆
      (indexedScheduleAdaptive r n start count).wires := by
  induction count generalizing start with
  | zero => exact List.Subset.refl _
  | succ count ih =>
    exact seq_mono (measuredIndexedStep_wires_subset r n start) (ih (start+1))
/-- All branches of the measured schedule stay within the previous adaptive schedule. -/
theorem measuredIndexedScheduleInverse_wires_subset (r : IndexedStepRegisters) (n start count : Nat) :
    (measuredIndexedScheduleInverse r n start count).wires ⊆
      (indexedScheduleInverseAdaptive r n start count).wires := by
  induction count generalizing start with
  | zero => exact List.Subset.refl _
  | succ count ih =>
    exact seq_mono (ih (start+1)) (measuredIndexedStepInverse_wires_subset r n start)
/-- The actual measured 1,620-step forward keeps the original allocation. -/
theorem secp256k1MeasuredEEAForward_wires_subset :
    (secp256k1MeasuredEEAForward indexedStepProductionRegisters).wires ⊆ List.range 580 :=
  (measuredIndexedSchedule_wires_subset indexedStepProductionRegisters 256 1 secp256k1ScheduleLength).trans
    secp256k1EEAForwardAdaptive_wires_subset
/-- The actual measured 1,620-step reverse keeps the original allocation. -/
theorem secp256k1MeasuredEEAReverse_wires_subset :
    (secp256k1MeasuredEEAReverse indexedStepProductionRegisters).wires ⊆ List.range 580 :=
  (measuredIndexedScheduleInverse_wires_subset indexedStepProductionRegisters 256 1 secp256k1ScheduleLength).trans
    secp256k1EEAReverseAdaptive_wires_subset
private theorem measuredForward_subset :
    (secp256k1MeasuredEEAForward indexedStepProductionRegisters).wires ⊆
      (secp256k1EEAForwardAdaptive indexedStepProductionRegisters).wires :=
  measuredIndexedSchedule_wires_subset indexedStepProductionRegisters 256 1 secp256k1ScheduleLength
private theorem measuredReverse_subset :
    (secp256k1MeasuredEEAReverse indexedStepProductionRegisters).wires ⊆
      (secp256k1EEAReverseAdaptive indexedStepProductionRegisters).wires :=
  measuredIndexedScheduleInverse_wires_subset indexedStepProductionRegisters 256 1 secp256k1ScheduleLength
attribute [local irreducible] eeaPreprocess eeaUnpreprocess secp256k1MeasuredEEAForward
  secp256k1MeasuredEEAReverse secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive
  secp256k1EEAParityCorrection canonicalWork2Rotation terminalEpochCompression terminalWork1Clear
  secp256k1EEAReversePostprocessing
/-- Every measurement branch of the complete forward inversion stays in 580 wires. -/
theorem secp256k1MeasuredEEAForwardWrapper_wires_subset :
    secp256k1MeasuredEEAForwardWrapper.wires ⊆ List.range 580 := by
  apply List.Subset.trans (l₂ := secp256k1EEAForwardWrapper.wires)
  · unfold secp256k1MeasuredEEAForwardWrapper secp256k1EEAForwardWrapper
    exact seq_mono (seq_mono (seq_mono (seq_mono (List.Subset.refl _)
      measuredForward_subset)
      (List.Subset.refl _)) (List.Subset.refl _)) (List.Subset.refl _)
  · exact secp256k1EEAForwardWrapper_wires_subset
/-- Every measurement branch of the complete inverse inversion stays in 580 wires. -/
theorem secp256k1MeasuredEEAReverseWrapper_wires_subset :
    secp256k1MeasuredEEAReverseWrapper.wires ⊆ List.range 580 := by
  apply List.Subset.trans (l₂ := secp256k1EEAReverseWrapper.wires)
  · unfold secp256k1MeasuredEEAReverseWrapper secp256k1EEAReverseWrapper
    exact seq_mono (seq_mono (List.Subset.refl _)
      measuredReverse_subset)
      (List.Subset.refl _)
  · exact secp256k1EEAReverseWrapper_wires_subset
private theorem count580 (p : AdaptiveCircuit) (h : p.wires ⊆ List.range 580) : p.qubitCount ≤ 580 := by
  have hs : p.wires.dedup.toFinset ⊆ (List.range 580).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h (by simpa using hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 580))] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc
/-- Whole adaptive-tree distinct-wire count, without subtracting measured/reset wires. -/
theorem secp256k1MeasuredEEAForwardWrapper_qubitCount :
    secp256k1MeasuredEEAForwardWrapper.qubitCount ≤ 580 :=
  count580 _ secp256k1MeasuredEEAForwardWrapper_wires_subset
/-- Whole adaptive-tree distinct-wire count for the reverse wrapper. -/
theorem secp256k1MeasuredEEAReverseWrapper_qubitCount :
    secp256k1MeasuredEEAReverseWrapper.qubitCount ≤ 580 :=
  count580 _ secp256k1MeasuredEEAReverseWrapper_wires_subset
end ShorECDLP.Paper2607_13816
