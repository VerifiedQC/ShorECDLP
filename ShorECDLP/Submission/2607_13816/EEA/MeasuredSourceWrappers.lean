import ShorECDLP.Submission.«2607_13816».EEA.SourceWrappers
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredSourceH
namespace ShorECDLP.Paper2607_13816
open Quantum
def measuredIndexedStepSource256 (r : IndexedStepRegisters) (T : Nat) : CorrectionProgram :=
  (CorrectionProgram.unitary [.ordinary (blockAForward r)] .done).seq
    ((blockBSource r 256 (certifiedActiveWindows 256 T).remainder).seq
      ((CorrectionProgram.unitary [.ordinary (blockCForward r ++ blockDForward r (certifiedActiveWindows 256 T).quotientSwap)] .done).seq
        ((blockESource r 256 (certifiedActiveWindows 256 T).coefficient).seq
          ((CorrectionProgram.unitary [.ordinary (blockFForward r)] .done).seq
            ((phaseUpdateEpochSource r.phaseUpdate r.shiftEpoch).seq
              (measuredBlockHForwardSource r 256 T))))))
theorem measuredIndexedStepSource256_erase (r : IndexedStepRegisters) (T : Nat) :
    (measuredIndexedStepSource256 r T).erase=measuredIndexedStep r 256 T := by
  simp only [measuredIndexedStepSource256, CorrectionProgram.erase_seq, blockBSource_erase,
    blockESource_erase, phaseUpdateEpochSource_erase, measuredBlockHForwardSource_erase,
    CorrectionProgram.erase, correctionBlockErase, CorrectionFragment.erase, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, measuredIndexedStep, measuredStepPrefix, circuit_seq_assoc]
  rfl
def measuredIndexedStepInverseSource256 (r : IndexedStepRegisters) (T : Nat) : CorrectionProgram :=
  (((((((((((measuredBlockHInverseSource r 256 T).seq (phaseUpdateEpochInverseSource r.phaseUpdate r.shiftEpoch)).seq (CorrectionProgram.unitary [.ordinary ((blockFForward r).adjoint ++ prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch)] .done)).seq (coefficientPrefixInverseSource (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2)).seq (CorrectionProgram.unitary [.ordinary (computeControl [r.phase1] 1 r.control r.blockScratch ++ [.CX r.phase1 r.sign] ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch)] .done)).seq (coefficientPrefixInverseSource (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2)).seq (CorrectionProgram.unitary [.ordinary (computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]))] .done)).seq (intervalAddSubInverseSource (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1)).seq (CorrectionProgram.unitary [.ordinary ((([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]) ++ blockB2 r ++ rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)] .done)).seq (intervalAddSubInverseSource (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1)).seq (CorrectionProgram.unitary [.ordinary (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r)] .done))
theorem measuredIndexedStepInverseSource256_erase (r : IndexedStepRegisters) (T : Nat) :
    (measuredIndexedStepInverseSource256 r T).erase=measuredIndexedStepInverse r 256 T := by
  simp only [measuredIndexedStepInverseSource256, CorrectionProgram.erase_seq,
    phaseUpdateEpochInverseSource_erase, coefficientPrefixInverseSource_erase,
    intervalAddSubInverseSource_erase, measuredBlockHInverseSource_erase,
    CorrectionProgram.erase, correctionBlockErase, CorrectionFragment.erase,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    measuredIndexedStepInverse, indexedStepInverseTailAdaptive, circuit_seq_assoc]
  rfl
def measuredIndexedScheduleSource256 (r : IndexedStepRegisters) (start : Nat) : Nat → CorrectionProgram
  | 0 => .unitary [] .done
  | count+1 => (measuredIndexedStepSource256 r start).seq (measuredIndexedScheduleSource256 r (start+1) count)
theorem measuredIndexedScheduleSource256_erase (r : IndexedStepRegisters) (start count : Nat) :
    (measuredIndexedScheduleSource256 r start count).erase=measuredIndexedSchedule r 256 start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [measuredIndexedScheduleSource256, measuredIndexedSchedule, CorrectionProgram.erase_seq,
      measuredIndexedStepSource256_erase, ih]
def measuredIndexedScheduleInverseSource256 (r : IndexedStepRegisters) (start : Nat) : Nat → CorrectionProgram
  | 0 => .unitary [] .done
  | count+1 => (measuredIndexedScheduleInverseSource256 r (start+1) count).seq (measuredIndexedStepInverseSource256 r start)
theorem measuredIndexedScheduleInverseSource256_erase (r : IndexedStepRegisters) (start count : Nat) :
    (measuredIndexedScheduleInverseSource256 r start count).erase=measuredIndexedScheduleInverse r 256 start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [measuredIndexedScheduleInverseSource256, measuredIndexedScheduleInverse, CorrectionProgram.erase_seq,
      measuredIndexedStepInverseSource256_erase, ih]
def secp256k1MeasuredEEAForwardSource : CorrectionProgram :=
  measuredIndexedScheduleSource256 indexedStepProductionRegisters 1 1620
theorem secp256k1MeasuredEEAForwardSource_erase : secp256k1MeasuredEEAForwardSource.erase=secp256k1MeasuredEEAForward indexedStepProductionRegisters :=
  measuredIndexedScheduleSource256_erase _ _ _
def secp256k1MeasuredEEAReverseSource : CorrectionProgram :=
  measuredIndexedScheduleInverseSource256 indexedStepProductionRegisters 1 1620
theorem secp256k1MeasuredEEAReverseSource_erase : secp256k1MeasuredEEAReverseSource.erase=secp256k1MeasuredEEAReverse indexedStepProductionRegisters :=
  measuredIndexedScheduleInverseSource256_erase _ _ _
def secp256k1MeasuredEEAForwardWrapperSource : CorrectionProgram :=
  ((((eeaPreprocessSource.seq (secp256k1MeasuredEEAForwardSource)).seq
    (CorrectionProgram.unitary [.ordinary (canonicalWork2Rotation ++ terminalEpochCompression)] .done)).seq
    secp256k1EEAParitySource).seq (CorrectionProgram.unitary [.ordinary terminalWork1Clear] .done))
theorem secp256k1MeasuredEEAForwardWrapperSource_erase : secp256k1MeasuredEEAForwardWrapperSource.erase=secp256k1MeasuredEEAForwardWrapper := by
  simp [secp256k1MeasuredEEAForwardWrapperSource, secp256k1MeasuredEEAForwardWrapper, secp256k1MeasuredEEAForwardSource_erase,
    eeaPreprocessSource_erase,
    secp256k1EEAParitySource_erase,
    CorrectionProgram.erase_seq, CorrectionProgram.erase, correctionBlockErase, CorrectionFragment.erase]
def secp256k1MeasuredEEAReverseWrapperSource : CorrectionProgram :=
  (secp256k1EEAReversePostprocessingSource.seq
    (secp256k1MeasuredEEAReverseSource)).seq eeaUnpreprocessSource
theorem secp256k1MeasuredEEAReverseWrapperSource_erase : secp256k1MeasuredEEAReverseWrapperSource.erase=secp256k1MeasuredEEAReverseWrapper := by
  simp [secp256k1MeasuredEEAReverseWrapperSource, secp256k1MeasuredEEAReverseWrapper, secp256k1MeasuredEEAReverseSource_erase,
    eeaUnpreprocessSource_erase,
    secp256k1EEAReversePostprocessingSource_erase,
    CorrectionProgram.erase_seq]

attribute [local irreducible] measuredBlockHForwardSource measuredBlockHInverseSource
  blockBSource blockESource phaseUpdateEpochSource phaseUpdateEpochInverseSource
  coefficientPrefixInverseSource intervalAddSubInverseSource
  eeaPreprocessSource eeaUnpreprocessSource secp256k1EEAParitySource
  secp256k1EEAReversePostprocessingSource
  CorrectionProgram.events CorrectionProgram.erase
  AdaptiveCircuit.measurementCount
private def SourceBalance (a b : CorrectionProgram) : Prop :=
  a.events + b.erase.measurementCount = b.events + a.erase.measurementCount
private theorem source_refl (a : CorrectionProgram) : SourceBalance a a := rfl
private theorem source_seq (a b c d : CorrectionProgram)
    (ha : SourceBalance a c) (hb : SourceBalance b d) : SourceBalance (a.seq b) (c.seq d) := by
  simp only [SourceBalance, CorrectionProgram.events_seq, CorrectionProgram.erase_seq,
    modularMeasurements_seq] at *
  omega
private theorem source_hf (r : IndexedStepRegisters) (T : Nat) :
    SourceBalance (measuredBlockHForwardSource r 256 T)
      (.unitary [.ordinary (blockHForward r 256 T)] .done) := by
  simp [SourceBalance, measuredBlockHForwardSource_events, measuredBlockHForwardSource_erase,
    CorrectionProgram.erase, CorrectionProgram.events, correctionBlockEvents,
    CorrectionFragment.events, AdaptiveCircuit.measurementCount]
private theorem source_hi (r : IndexedStepRegisters) (T : Nat) :
    SourceBalance (measuredBlockHInverseSource r 256 T)
      (.unitary [.ordinary (blockHInverse r 256 T)] .done) := by
  simp [SourceBalance, measuredBlockHInverseSource_events, measuredBlockHInverseSource_erase,
    CorrectionProgram.erase, CorrectionProgram.events, correctionBlockEvents,
    CorrectionFragment.events, AdaptiveCircuit.measurementCount]
private theorem step_balance (r : IndexedStepRegisters) (T : Nat) :
    SourceBalance (measuredIndexedStepSource256 r T) (indexedStepSource256 r T) := by
  unfold measuredIndexedStepSource256 indexedStepSource256
  repeat' first
    | exact source_hf _ _
    | exact source_hi _ _
    | exact source_refl _
    | apply source_seq
private theorem schedule_balance (r : IndexedStepRegisters) (start count : Nat) :
    SourceBalance (measuredIndexedScheduleSource256 r start count) (indexedScheduleSource256 r start count) := by
  induction count generalizing start with
  | zero => exact source_refl _
  | succ count ih =>
    unfold measuredIndexedScheduleSource256 indexedScheduleSource256
    apply source_seq
    · exact step_balance _ _
    · exact ih _
private theorem stepInverse_balance (r : IndexedStepRegisters) (T : Nat) :
    SourceBalance (measuredIndexedStepInverseSource256 r T) (indexedStepInverseSource256 r T) := by
  unfold measuredIndexedStepInverseSource256 indexedStepInverseSource256
  repeat' first
    | exact source_hf _ _
    | exact source_hi _ _
    | exact source_refl _
    | apply source_seq
private theorem scheduleInverse_balance (r : IndexedStepRegisters) (start count : Nat) :
    SourceBalance (measuredIndexedScheduleInverseSource256 r start count) (indexedScheduleInverseSource256 r start count) := by
  induction count generalizing start with
  | zero => exact source_refl _
  | succ count ih =>
    unfold measuredIndexedScheduleInverseSource256 indexedScheduleInverseSource256
    apply source_seq
    · exact ih _
    · exact stepInverse_balance _ _
attribute [local irreducible] measuredIndexedStepSource256 indexedStepSource256
  measuredIndexedStepInverseSource256 indexedStepInverseSource256
  measuredIndexedScheduleSource256 indexedScheduleSource256
  measuredIndexedScheduleInverseSource256 indexedScheduleInverseSource256
private theorem forward_source_balance :
    SourceBalance secp256k1MeasuredEEAForwardSource secp256k1EEAForwardSource :=
  schedule_balance _ _ _
private theorem forward_wrapper_balance :
    SourceBalance secp256k1MeasuredEEAForwardWrapperSource secp256k1EEAForwardWrapperSource := by
  unfold secp256k1MeasuredEEAForwardWrapperSource secp256k1EEAForwardWrapperSource
  repeat' first
    | exact forward_source_balance
    | exact source_refl _
    | apply source_seq
private theorem reverse_source_balance :
    SourceBalance secp256k1MeasuredEEAReverseSource secp256k1EEAReverseSource :=
  scheduleInverse_balance _ _ _
private theorem reverse_wrapper_balance :
    SourceBalance secp256k1MeasuredEEAReverseWrapperSource secp256k1EEAReverseWrapperSource := by
  unfold secp256k1MeasuredEEAReverseWrapperSource secp256k1EEAReverseWrapperSource
  repeat' first
    | exact reverse_source_balance
    | exact source_refl _
    | apply source_seq
attribute [local irreducible] secp256k1MeasuredEEAForwardSource secp256k1MeasuredEEAReverseSource
  secp256k1EEAForwardSource secp256k1EEAReverseSource
  secp256k1MeasuredEEAForwardWrapperSource secp256k1MeasuredEEAReverseWrapperSource
  secp256k1EEAForwardWrapperSource secp256k1EEAReverseWrapperSource
  secp256k1MeasuredEEAForwardWrapper secp256k1MeasuredEEAReverseWrapper
  secp256k1EEAForwardWrapper secp256k1EEAReverseWrapper
private theorem balance_events (a b : CorrectionProgram) (ha : a.erase.measurementCount=6961844)
    (hb : b.erase.measurementCount=5280108) (hc : b.events=5281384)
    (h : SourceBalance a b) : a.events=6963120 := by
  unfold SourceBalance at h
  omega
theorem secp256k1MeasuredEEAForwardWrapperSource_certificate :
    secp256k1MeasuredEEAForwardWrapperSource.erase=secp256k1MeasuredEEAForwardWrapper ∧
    secp256k1MeasuredEEAForwardWrapperSource.events=6963120 := by
  refine ⟨secp256k1MeasuredEEAForwardWrapperSource_erase, ?_⟩
  apply balance_events _ secp256k1EEAForwardWrapperSource
  · rw [secp256k1MeasuredEEAForwardWrapperSource_erase]
    exact congrArg PrimitiveResources.measurements secp256k1MeasuredEEAForwardWrapper_primitive_exact
  · rw [secp256k1EEAForwardWrapperSource_erase]
    exact congrArg PrimitiveResources.measurements secp256k1EEAForwardWrapper_primitive_exact
  · exact secp256k1EEAForwardWrapperSource_certificate.2
  · exact forward_wrapper_balance
theorem secp256k1MeasuredEEAReverseWrapperSource_certificate :
    secp256k1MeasuredEEAReverseWrapperSource.erase=secp256k1MeasuredEEAReverseWrapper ∧
    secp256k1MeasuredEEAReverseWrapperSource.events=6963120 := by
  refine ⟨secp256k1MeasuredEEAReverseWrapperSource_erase, ?_⟩
  apply balance_events _ secp256k1EEAReverseWrapperSource
  · rw [secp256k1MeasuredEEAReverseWrapperSource_erase]
    exact congrArg PrimitiveResources.measurements secp256k1MeasuredEEAReverseWrapper_primitive_exact
  · rw [secp256k1EEAReverseWrapperSource_erase]
    exact congrArg PrimitiveResources.measurements secp256k1EEAReverseWrapper_primitive_exact
  · exact secp256k1EEAReverseWrapperSource_certificate.2
  · exact reverse_wrapper_balance
end ShorECDLP.Paper2607_13816
