import ShorECDLP.Submission.«2607_13816».EEA.SourceIntervals
import ShorECDLP.Submission.«2607_13816».EEA.SourceCoefficients
import ShorECDLP.Submission.«2607_13816».EEA.SourcePhase
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStepPrimitiveCounts
namespace ShorECDLP.Paper2607_13816
open Quantum
def blockBSource (r : IndexedStepRegisters) (n : Nat) (w : ActiveWindow) : CorrectionProgram :=
  let subControl := rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
  let phaseControl := rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch
  let restoreControl := ([.CCX r.phase2 r.sign r.terminal] ++
    rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime
      (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]
  (((CorrectionProgram.unitary [.ordinary subControl] .done).seq
    ((intervalAddSubSource (r.remainder w) n w.start w.stop .sub true .work1).seq (CorrectionProgram.unitary [.ordinary subControl] .done))).seq
    ((CorrectionProgram.unitary [.ordinary ((phaseControl ++ [.CX r.control r.sign]) ++ phaseControl)] .done).seq
      ((CorrectionProgram.unitary [.ordinary restoreControl] .done).seq
        ((intervalAddSubSource (r.remainder w) n w.start w.stop .add false .work1).seq
          (CorrectionProgram.unitary [.ordinary restoreControl] .done)))))
theorem blockBSource_erase (r : IndexedStepRegisters) (n : Nat) (w : ActiveWindow) :
    (blockBSource r n w).erase=blockBAdaptive r n w := by
  simp only [blockBSource,CorrectionProgram.erase_seq,intervalAddSubSource_erase,
    CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]
  rfl
theorem blockBSource_events (r : IndexedStepRegisters) (n : Nat) (w : ActiveWindow)
    (hl : IntervalLayout (r.remainder w) w.start w.stop .work1)
    (hs : r.lengthS.length-2≤((r.remainder w).equalityScratch w.start w.stop).length)
    (hq : r.lengthQ.length-2≤((r.remainder w).equalityScratch w.start w.stop).length) :
    (blockBSource r n w).events=
      4*((intervalTree (r.remainder w) w.start w.stop).leaves+
        2*(intervalTree (r.remainder w) w.start w.stop).internalNodes)+
      4*(if intervalHasTopSpecial w.start w.stop then
        2*(r.lengthS.length-2)+2*(r.lengthQ.length-2)+1 else 0) := by
  simp only [blockBSource,CorrectionProgram.events_seq,
    intervalAddSubSource_events _ _ _ _ _ _ _ hl.traversal.1 hs hq,
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
  have hS : (r.remainder w).lengthS=r.lengthS := rfl
  have hQ : (r.remainder w).lengthQ=r.lengthQ := rfl
  rw [hS,hQ]
  omega
def blockESource (r : IndexedStepRegisters) (n : Nat) (w : ActiveWindow) : CorrectionProgram :=
  ((CorrectionProgram.unitary [.ordinary (((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary n)] .done).seq
        (coefficientPrefixSource (r.coefficient w) w.start w.stop .sub false .work2)).seq
      ((CorrectionProgram.unitary [.ordinary ((((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ [.CX r.phase1 r.sign]) ++
          computeControl [r.phase1] 1 r.control r.blockScratch)] .done).seq
        ((coefficientPrefixSource (r.coefficient w) w.start w.stop .add true .work2).seq
          (CorrectionProgram.unitary [.ordinary (computeControl [r.phase1] 1 r.control r.blockScratch ++
            restoreLatestPaperTBoundary r.tBoundary n)] .done)))
theorem blockESource_erase (r : IndexedStepRegisters) (n : Nat) (w : ActiveWindow) :
    (blockESource r n w).erase=blockEAdaptive r n w := by
  rw [blockEAdaptive_eq_parts]
  simp [blockESource,CorrectionProgram.erase_seq,coefficientPrefixSource_erase,
    CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
theorem blockESource_events (r : IndexedStepRegisters) (n : Nat) (w : ActiveWindow)
    (hl : CoefficientPrefixLayout (r.coefficient w) w.start w.stop) :
    (blockESource r n w).events=
      4*((coefficientPrefixTree (r.coefficient w) w.start w.stop).leaves+
        (coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes) := by
  simp only [blockESource,CorrectionProgram.events_seq,
    coefficientPrefixSource_events _ _ _ _ _ _ hl.tree,
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
  omega
end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Annotate the eight literal blocks of one production-width EEA step. -/
def indexedStepSource256 (r : IndexedStepRegisters) (T : Nat) : CorrectionProgram :=
  (CorrectionProgram.unitary [.ordinary (blockAForward r)] .done).seq
    ((blockBSource r 256 (certifiedActiveWindows 256 T).remainder).seq
      ((CorrectionProgram.unitary [.ordinary (blockCForward r ++ blockDForward r (certifiedActiveWindows 256 T).quotientSwap)] .done).seq
        ((blockESource r 256 (certifiedActiveWindows 256 T).coefficient).seq
          ((CorrectionProgram.unitary [.ordinary (blockFForward r)] .done).seq
            ((phaseUpdateEpochSource r.phaseUpdate r.shiftEpoch).seq
              (CorrectionProgram.unitary [.ordinary (blockHForward r 256 T)] .done))))))
theorem indexedStepSource256_erase (r : IndexedStepRegisters) (T : Nat) :
    (indexedStepSource256 r T).erase=indexedStepAdaptive r 256 T := by
  rw [indexedStepAdaptive_eq_parts]
  simp [indexedStepSource256,CorrectionProgram.erase_seq,blockBSource_erase,
    blockESource_erase,phaseUpdateEpochSource_erase,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase]
/-- Selected source corrections, retaining the actual certified decoder trees. -/
def indexedStepSourceEvents256 (r : IndexedStepRegisters) (T : Nat) : Nat :=
  let w := certifiedActiveWindows 256 T
  let i := intervalTree (r.remainder w.remainder) w.remainder.start w.remainder.stop
  let c := coefficientPrefixTree (r.coefficient w.coefficient) w.coefficient.start w.coefficient.stop
  4*(i.leaves+2*i.internalNodes)+
    4*(if intervalHasTopSpecial w.remainder.start w.remainder.stop then 29 else 0)+
    4*(c.leaves+c.internalNodes)+44

theorem indexedStepSource256_events (r : IndexedStepRegisters) (T : Nat)
    (hl : IndexedStepLayout r 256 T)
    (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9)
    (hr : r.lengthRPrime.length=9) :
    (indexedStepSource256 r T).events=indexedStepSourceEvents256 r T := by
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
  simp only [indexedStepSource256,CorrectionProgram.events_seq,
    blockBSource_events _ _ _ hl.remainder hes heq,
    blockESource_events _ _ _ hl.coefficient,
    phaseUpdateEpochSource_events _ _ (by omega : r.phaseUpdate.lengthQ.length-2≤r.phaseUpdate.equalityScratch.length)
      (by omega : r.phaseUpdate.lengthRPrime.length-2≤r.phaseUpdate.equalityScratch.length)
      (by omega : r.phaseUpdate.lengthS.length+1-2≤r.phaseUpdate.equalityScratch.length),
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
  simp only [indexedStepSourceEvents256,hq,hs,pq,pr,ps]
  norm_num only
  omega

/-- Chronological source annotation; retain the literal empty unitary base case. -/
def indexedScheduleSource256 (r : IndexedStepRegisters) (start : Nat) : Nat → CorrectionProgram
  | 0 => .unitary [] .done
  | count+1 => (indexedStepSource256 r start).seq (indexedScheduleSource256 r (start+1) count)
theorem indexedScheduleSource256_erase (r : IndexedStepRegisters) (start count : Nat) :
    (indexedScheduleSource256 r start count).erase=indexedScheduleAdaptive r 256 start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [indexedScheduleSource256,indexedScheduleAdaptive,CorrectionProgram.erase_seq,
      indexedStepSource256_erase,ih]
theorem indexedScheduleSource256_events (r : IndexedStepRegisters) (start count : Nat)
    (hl : IndexedScheduleLayout r 256 start count)
    (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9) (hr : r.lengthRPrime.length=9) :
    (indexedScheduleSource256 r start count).events=
      ((List.range' start count).map (indexedStepSourceEvents256 r)).sum := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleSource256,CorrectionProgram.events_seq,
      indexedStepSource256_events r start head hq hs hr,ih]
    rfl
end ShorECDLP.Paper2607_13816
