import ShorECDLP.Submission.«2607_13816».EEA.SourceStep
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleResources
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem sourceDualOnes {t : DualUnaryActionTree} {a b : Wire} {pa pb : List Wire}
    (h : t.Layout a b pa pb) : t.leafCostSum (fun _ _ _ => 1) a b pa pb=t.leaves := by
  induction h with
  | leaf => rfl
  | node a b c d e f z o pa pb hn hz ho ihz iho =>
    simp only [DualUnaryActionTree.leafCostSum,DualUnaryActionTree.leaves,ihz,iho]
/-- The independently annotated event sum agrees with the existing EEA measurement formula. -/
theorem indexedStepSourceEvents256_eq (r : IndexedStepRegisters) (T : Nat)
    (hl : IndexedStepLayout r 256 T)
    (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9) (hr : r.lengthRPrime.length=9) :
    indexedStepSourceEvents256 r T=indexedStepAdaptiveMeasurementFormula r 256 T := by
  have hS : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS=r.lengthS := rfl
  have hQ : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ=r.lengthQ := rfl
  have pq : r.phaseUpdate.lengthQ.length=9 := hq
  have pr : r.phaseUpdate.lengthRPrime.length=9 := hr
  have ps : r.phaseUpdate.lengthS.length=9 := hs
  simp only [indexedStepSourceEvents256,indexedStepAdaptiveMeasurementFormula,intervalMeasurementFormula,
    sourceDualOnes hl.remainder.traversal.1,hS,hQ,hq,hs,pq,pr,ps]
  norm_num [mcxVChainMeasurementCost]
  split <;> omega
private theorem sourceLayoutSumCongr (r : IndexedStepRegisters) (start count : Nat)
    (f g : Nat → Nat) (heq : ∀ T, IndexedStepLayout r 256 T → f T=g T)
    (h : IndexedScheduleLayout r 256 start count) :
    ((List.range' start count).map f).sum=((List.range' start count).map g).sum := by
  induction h with
  | done start => rfl
  | @step start count head tail ih =>
    simp only [List.range'_succ,List.map_cons,List.sum_cons,heq start head,ih]
/-- Actual chronological EEA source annotations, instantiated at the physical production layout. -/
def secp256k1EEAForwardSource : CorrectionProgram :=
  indexedScheduleSource256 indexedStepProductionRegisters 1 1620
theorem secp256k1EEAForwardSource_certificate :
    secp256k1EEAForwardSource.erase=secp256k1EEAForwardAdaptive indexedStepProductionRegisters ∧
      secp256k1EEAForwardSource.events=5278832 := by
  constructor
  · exact indexedScheduleSource256_erase _ _ _
  · rw [secp256k1EEAForwardSource,indexedScheduleSource256_events _ 1 1620 secp256k1ScheduleLayout_production rfl rfl rfl]
    exact (sourceLayoutSumCongr _ 1 1620 _ _
      (fun T h => (indexedStepSourceEvents256_eq _ T h rfl rfl rfl).trans
        (secp256k1StepMeasurements_eq T h)) secp256k1ScheduleLayout_production).trans secp256k1StepMeasurements_sum
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
def indexedStepInverseSource256 (r : IndexedStepRegisters) (T : Nat) : CorrectionProgram :=
  (((((((((((CorrectionProgram.unitary [.ordinary (blockHInverse r 256 T)] .done).seq (phaseUpdateEpochInverseSource r.phaseUpdate r.shiftEpoch)).seq (CorrectionProgram.unitary [.ordinary ((blockFForward r).adjoint ++ prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch)] .done)).seq (coefficientPrefixInverseSource (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2)).seq (CorrectionProgram.unitary [.ordinary (computeControl [r.phase1] 1 r.control r.blockScratch ++ [.CX r.phase1 r.sign] ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch)] .done)).seq (coefficientPrefixInverseSource (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2)).seq (CorrectionProgram.unitary [.ordinary (computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]))] .done)).seq (intervalAddSubInverseSource (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1)).seq (CorrectionProgram.unitary [.ordinary ((([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]) ++ blockB2 r ++ rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)] .done)).seq (intervalAddSubInverseSource (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1)).seq (CorrectionProgram.unitary [.ordinary (rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r)] .done))
theorem indexedStepInverseSource256_erase (r : IndexedStepRegisters) (T : Nat) :
    (indexedStepInverseSource256 r T).erase=indexedStepInverseAdaptive r 256 T := by
  rw [indexedStepInverseAdaptive_eq_parts]
  simp [indexedStepInverseSource256,CorrectionProgram.erase_seq,phaseUpdateEpochInverseSource_erase,
    coefficientPrefixInverseSource_erase,intervalAddSubInverseSource_erase,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase]
theorem indexedStepInverseSource256_events (r : IndexedStepRegisters) (T : Nat)
    (hl : IndexedStepLayout r 256 T)
    (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9)
    (hr : r.lengthRPrime.length=9) :
    (indexedStepInverseSource256 r T).events=indexedStepSourceEvents256 r T := by
  have hsource : r.sourceScratch.length=18 := by
    simp [IndexedStepRegisters.sourceScratch,hl.aux_length]
  have hp : 8≤r.phaseUpdate.equalityScratch.length := by
    simp [IndexedStepRegisters.phaseUpdate,IndexedStepRegisters.phaseEqualityScratchSize,
      List.length_take,List.length_drop,hsource,hq,hs,hr]
  have heq := intervalLengthQ_sub_two_le_equalityScratch _ _ _ _ hl.remainder
  change r.lengthQ.length-2≤_ at heq
  have hes : r.lengthS.length-2≤((r.remainder (certifiedActiveWindows 256 T).remainder).equalityScratch
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).length := by
    rw [hs,hq] at *
    exact heq
  have pq : r.phaseUpdate.lengthQ.length=9 := hq
  have pr : r.phaseUpdate.lengthRPrime.length=9 := hr
  have ps : r.phaseUpdate.lengthS.length=9 := hs
  simp only [indexedStepInverseSource256,CorrectionProgram.events_seq,
    intervalAddSubInverseSource_events _ _ _ _ _ _ _ hl.remainder.traversal.1 hes heq,
    coefficientPrefixInverseSource_events _ _ _ _ _ _ hl.coefficient.tree,
    phaseUpdateEpochInverseSource_events _ _ (by omega : r.phaseUpdate.lengthQ.length-2≤r.phaseUpdate.equalityScratch.length)
      (by omega : r.phaseUpdate.lengthRPrime.length-2≤r.phaseUpdate.equalityScratch.length)
      (by omega : r.phaseUpdate.lengthS.length+1-2≤r.phaseUpdate.equalityScratch.length),
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
  have hS : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS=r.lengthS := rfl
  have hQ : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ=r.lengthQ := rfl
  simp only [indexedStepSourceEvents256,hS,hQ,hq,hs,pq,pr,ps]
  norm_num only
  omega

end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- The explicit inverse visits source indices in descending order. -/
def indexedScheduleInverseSource256 (r : IndexedStepRegisters) (start : Nat) : Nat → CorrectionProgram
  | 0 => .unitary [] .done
  | count+1 => (indexedScheduleInverseSource256 r (start+1) count).seq (indexedStepInverseSource256 r start)
theorem indexedScheduleInverseSource256_erase (r : IndexedStepRegisters) (start count : Nat) :
    (indexedScheduleInverseSource256 r start count).erase=indexedScheduleInverseAdaptive r 256 start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [indexedScheduleInverseSource256,indexedScheduleInverseAdaptive,CorrectionProgram.erase_seq,
      indexedStepInverseSource256_erase,ih]
theorem indexedScheduleInverseSource256_events (r : IndexedStepRegisters) (start count : Nat)
    (hl : IndexedScheduleLayout r 256 start count)
    (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9) (hr : r.lengthRPrime.length=9) :
    (indexedScheduleInverseSource256 r start count).events=
      ((List.range' start count).map (indexedStepSourceEvents256 r)).sum := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleInverseSource256,CorrectionProgram.events_seq,
      indexedStepInverseSource256_events r start head hq hs hr,ih]
    simp only [List.range'_succ,List.map_cons,List.sum_cons,Nat.add_comm]
/-- Source annotation of the actual physical reverse EEA schedule. -/
def secp256k1EEAReverseSource : CorrectionProgram :=
  indexedScheduleInverseSource256 indexedStepProductionRegisters 1 1620
theorem secp256k1EEAReverseSource_certificate :
    secp256k1EEAReverseSource.erase=secp256k1EEAReverseAdaptive indexedStepProductionRegisters ∧
      secp256k1EEAReverseSource.events=5278832 := by
  constructor
  · exact indexedScheduleInverseSource256_erase _ _ _
  · rw [secp256k1EEAReverseSource,indexedScheduleInverseSource256_events _ 1 1620 secp256k1ScheduleLayout_production rfl rfl rfl]
    have h := secp256k1EEAForwardSource_certificate.2
    rw [secp256k1EEAForwardSource,indexedScheduleSource256_events _ 1 1620 secp256k1ScheduleLayout_production rfl rfl rfl] at h
    exact h
end ShorECDLP.Paper2607_13816
