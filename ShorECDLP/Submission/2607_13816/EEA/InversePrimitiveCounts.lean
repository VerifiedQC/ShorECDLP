import ShorECDLP.Submission.«2607_13816».EEA.SchedulePrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- The explicit reverse has the forward vector plus the padding decrement's 32 X gates.
This counts the emitted inverse stages; semantic cancellation alone does not imply this result. -/
theorem indexedStepInverseAdaptive256_primitive (r : IndexedStepRegisters) (T : Nat)
    (hl : IndexedStepLayout r 256 T)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9)
    (hs : r.lengthS.length=9) (hr : r.lengthRPrime.length=9) :
    primitiveResources (indexedStepInverseAdaptive r 256 T)=
      (primitiveResources (indexedStepAdaptive r 256 T)).add ⟨32,0,0,0,0,0⟩ := by
  have hsource : r.sourceScratch.length=18 := by
    simp [IndexedStepRegisters.sourceScratch,hl.aux_length]
  have hblock : 8≤r.blockScratch.length := by
    simp only [IndexedStepRegisters.blockScratch,List.length_drop,hsource]; omega
  have hp : 8≤r.phaseUpdate.equalityScratch.length := by
    simp [IndexedStepRegisters.phaseUpdate,IndexedStepRegisters.phaseEqualityScratchSize,
      List.length_take,List.length_drop,hsource,hq,hs,hr]
  have he := intervalLengthQ_le_endpointScratch _ _ _ _ hl.remainder
  have heq := intervalLengthQ_sub_two_le_equalityScratch _ _ _ _ hl.remainder
  change r.lengthQ.length≤_ at he
  change r.lengthQ.length-2≤_ at heq
  rw [hq] at he heq
  have hA : primitiveResources (.unitary (blockAInverse r) .done)=
      (primitiveResources (.unitary (blockAForward r) .done)).add ⟨32,0,0,0,0,0⟩ := by
    rw [blockAInverse259_primitive r hl.terminalPadding hl.preShift hl.work2_length hs hr hblock,
      blockAForward259_primitive r hl.terminalPadding hl.preShift hl.work2_length hs hr hblock]
    rfl
  have hC : primitiveResources (.unitary (blockCInverse r) .done)=
      primitiveResources (.unitary (blockCForward r) .done) := by
    rw [blockCInverse9_primitive r hr hblock,blockCForward9_primitive r hr hblock]
  have hD : primitiveResources (.unitary (blockDInverse r (certifiedActiveWindows 256 T).quotientSwap) .done)=
      primitiveResources (.unitary (blockDForward r (certifiedActiveWindows 256 T).quotientSwap) .done) := by
    rw [blockDInverse9_primitive r _ hl.quotient ht hq (by omega),
      blockDForward9_primitive r _ hl.quotient ht hq (by omega)]
  have hG : primitiveResources (phaseUpdateEpochInverseAdaptive r.phaseUpdate r.shiftEpoch)=
      primitiveResources (phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch) := by
    rw [phaseUpdateEpochInverseAdaptive9_primitive _ _ hq hr hs hp,
      phaseUpdateEpochAdaptive9_primitive _ _ hq hr hs hp]
  have hI (mode : RippleMode) (flag : Bool) :
      primitiveResources (intervalAddSubInverse (r.remainder (certifiedActiveWindows 256 T).remainder)
        256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop mode flag .work1)=
      primitiveResources (intervalAddSub (r.remainder (certifiedActiveWindows 256 T).remainder)
        256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop mode flag .work1) := by
    rw [intervalAddSubInverse9_primitive _ _ _ _ _ _ _ hl.remainder ht hq hs he heq,
      intervalAddSub9_primitive _ _ _ _ _ _ _ hl.remainder ht hq hs he heq]
  letI : Std.Associative PrimitiveResources.add := ⟨by
    intro a b c; cases a; cases b; cases c; simp [PrimitiveResources.add,Nat.add_assoc]⟩
  letI : Std.Commutative PrimitiveResources.add := ⟨by
    intro a b; cases a; cases b; simp [PrimitiveResources.add,Nat.add_comm]⟩
  rw [indexedStepInverseAdaptive_eq_parts,indexedStepAdaptive_eq_parts,
    blockBAdaptive_eq_parts,blockEAdaptive_eq_parts]
  simp only [primitiveResources_seq,primitiveResources_unitary_append,
    primitiveResources_unitary_adjoint,hA,hC,hD,hG,hI,
    coefficientPrefixInverseAdaptive_primitive _ _ _ _ _ _ hl.coefficient,
    blockHInverse_primitive r 256 T hl.endIteration]
  ac_rfl
private theorem inverseSchedule_primitive_sum (a b : PrimitiveResources) (count : Nat) :
    (b.add ⟨32*count,0,0,0,0,0⟩).add (a.add ⟨32,0,0,0,0,0⟩)=
      (a.add b).add ⟨32*(count+1),0,0,0,0,0⟩ := by
  cases a; cases b
  simp only [PrimitiveResources.add]
  congr 1 <;> omega
/-- The descending explicit inverse preserves the forward vector except for its
32 extra X gates per source index. -/
theorem indexedScheduleInverseAdaptive256_primitive (r : IndexedStepRegisters) (start count : Nat)
    (hl : IndexedScheduleLayout r 256 start count)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9)
    (hs : r.lengthS.length=9) (hr : r.lengthRPrime.length=9) :
    primitiveResources (indexedScheduleInverseAdaptive r 256 start count)=
      (primitiveResources (indexedScheduleAdaptive r 256 start count)).add ⟨32*count,0,0,0,0,0⟩ := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleInverseAdaptive,primitiveResources_seq,ih,
      indexedStepInverseAdaptive256_primitive r start head ht hq hs hr,
      indexedScheduleAdaptive,primitiveResources_seq]
    exact inverseSchedule_primitive_sum _ _ _
/-- Complete resources of the actual production descending adaptive schedule. -/
theorem secp256k1EEAReversePrimitive_certificate :
    primitiveResources (secp256k1EEAReverseAdaptive indexedStepProductionRegisters)=
      (⟨19097456,10557664,29716831,17454225,0,5278832⟩ : PrimitiveResources) := by
  have h := indexedScheduleInverseAdaptive256_primitive indexedStepProductionRegisters 1 1620
    secp256k1ScheduleLayout_production rfl rfl rfl rfl
  change primitiveResources (secp256k1EEAReverseAdaptive indexedStepProductionRegisters)=
    (primitiveResources (secp256k1EEAForwardAdaptive indexedStepProductionRegisters)).add _ at h
  rw [secp256k1EEAForwardPrimitive_certificate] at h
  exact h
end ShorECDLP.Paper2607_13816
