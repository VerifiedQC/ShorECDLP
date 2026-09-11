import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.BlockBPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.BlockDPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.BlockHPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.PhasePrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Expose the actual eight-block forward stream without expanding its arithmetic circuits. -/
theorem indexedStepAdaptive_eq_parts (r : IndexedStepRegisters) (T : Nat) :
    indexedStepAdaptive r 256 T =
    (AdaptiveCircuit.unitary (blockAForward r) .done).seq
    ((blockBAdaptive r 256 (certifiedActiveWindows 256 T).remainder).seq
      ((AdaptiveCircuit.unitary (blockCForward r ++ blockDForward r (certifiedActiveWindows 256 T).quotientSwap) .done).seq
        ((blockEAdaptive r 256 (certifiedActiveWindows 256 T).coefficient).seq
          ((AdaptiveCircuit.unitary (blockFForward r) .done).seq
            ((phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch).seq
              (AdaptiveCircuit.unitary (blockHForward r 256 T) .done)))))) := by
  rfl

/-- Scalar vector of all eight production EEA blocks. The interval terms retain their
certified tree shapes; the scheduled boundary refresh is included exactly once. -/
def indexedStepPrimitiveFormula256 (r : IndexedStepRegisters) (T : Nat) : PrimitiveResources :=
  let w := certifiedActiveWindows 256 T
  let q := quotientSwapTree (r.quotient w.quotientSwap) w.quotientSwap.start w.quotientSwap.stop
  let c := coefficientPrefixTree (r.coefficient w.coefficient) w.coefficient.start w.coefficient.stop
  let core : PrimitiveResources :=
    ⟨304+4*q.internalNodes+16*c.internalNodes,
      88+8*(c.leaves+c.internalNodes),
      3168+2*q.leaves+2*q.internalNodes+16*c.leaves+12*c.internalNodes,
      2027+q.leaves+2*q.internalNodes+10*c.leaves+4*c.internalNodes,
      0,44+4*(c.leaves+c.internalNodes)⟩
  let boundary : PrimitiveResources := if T%4=0 then
    ⟨4+endIterationXFormula 9 256 (endIterationWindowsAt 256 T),0,
      1+endIterationCnotFormula 259 9 256 (endIterationWindowsAt 256 T),
      66+endIterationToffoliFormula 259 9 256 (endIterationWindowsAt 256 T),0,0⟩
    else ⟨0,0,0,0,0,0⟩
  core.add ((intervalPrimitiveFormula9 (r.remainder w.remainder) 256 w.remainder.start
    w.remainder.stop .sub true).add ((intervalPrimitiveFormula9 (r.remainder w.remainder)
      256 w.remainder.start w.remainder.stop .add false).add boundary))


private theorem indexedStep_primitive_sum (i j b : PrimitiveResources) (ql qn cl cn : Nat) :
    (⟨108,0,1599,906,0,0⟩ : PrimitiveResources).add
      (((⟨28,0,1,198,0,0⟩ : PrimitiveResources).add (i.add j)).add
        (((⟨4,0,3,35,0,0⟩ : PrimitiveResources).add
          ⟨48+4*qn,0,170+2*ql+2*qn,108+ql+2*qn,0,0⟩).add
          ((⟨44+16*cn,8*(cl+cn),280+16*cl+12*cn,160+10*cl+4*cn,0,4*(cl+cn)⟩ : PrimitiveResources).add
            ((⟨64,0,1065,566,0,0⟩ : PrimitiveResources).add
              ((⟨8,88,50,54,0,44⟩ : PrimitiveResources).add b))))) =
    (⟨304+4*qn+16*cn,88+8*(cl+cn),3168+2*ql+2*qn+16*cl+12*cn,
      2027+ql+2*qn+10*cl+4*cn,0,44+4*(cl+cn)⟩ : PrimitiveResources).add (i.add (j.add b)) := by
  cases i; cases j; cases b
  simp only [PrimitiveResources.add]
  congr 1 <;> omega

/-- Exact six-component resources of the literal forward indexed step, from its physical
layout and production counter widths. No reachable-state or arithmetic hypothesis is needed. -/
theorem indexedStepAdaptive256_primitive (r : IndexedStepRegisters) (T : Nat)
    (hl : IndexedStepLayout r 256 T)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9)
    (hs : r.lengthS.length=9) (hr : r.lengthRPrime.length=9) :
    primitiveResources (indexedStepAdaptive r 256 T)=indexedStepPrimitiveFormula256 r T := by
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
  have hf : primitiveResources (.unitary (blockFForward r) .done)=(⟨64,0,1065,566,0,0⟩ : PrimitiveResources) := by
    exact postShiftUnitary259_primitive r.postShift hl.postShift hl.work2_length hs

  simp only [indexedStepAdaptive_eq_parts,primitiveResources_seq,primitiveResources_unitary_append]
  rw [blockAForward259_primitive r hl.terminalPadding hl.preShift hl.work2_length hs hr hblock,
    blockBAdaptive9_primitive r 256 _ hl.remainder ht hq hs hr hblock he heq,
    blockCForward9_primitive r hr hblock,
    blockDForward9_primitive r _ hl.quotient ht hq (by omega),
    blockEAdaptive256_primitive r _ hl.tBoundary ht hl.coefficient]
  rw [hf,phaseUpdateEpochAdaptive9_primitive _ _ hq hr hs hp,
    blockHForward256_primitive r T hl.work1_length ht hq hs (by omega) hl.endIteration]
  exact indexedStep_primitive_sum _ _ _ _ _ _ _
/-- Exact finite sum of primitive vectors in chronological EEA order. -/
def indexedSchedulePrimitiveFormula256 (r : IndexedStepRegisters) (start count : Nat) : PrimitiveResources :=
  ((List.range' start count).map (indexedStepPrimitiveFormula256 r)).foldr
    PrimitiveResources.add ⟨0,0,0,0,0,0⟩

theorem indexedScheduleAdaptive256_primitive (r : IndexedStepRegisters) (start count : Nat)
    (hl : IndexedScheduleLayout r 256 start count)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9)
    (hs : r.lengthS.length=9) (hr : r.lengthRPrime.length=9) :
    primitiveResources (indexedScheduleAdaptive r 256 start count)=
      indexedSchedulePrimitiveFormula256 r start count := by
  induction hl with
  | done start => rfl
  | @step start count head tail ih =>
    rw [indexedScheduleAdaptive,primitiveResources_seq,
      indexedStepAdaptive256_primitive r start head ht hq hs hr,ih]
    rfl

/-- The complete forward resource vector is derived from the same 1,620-step program. -/
theorem secp256k1EEAForwardAdaptive_primitive :
    primitiveResources (secp256k1EEAForwardAdaptive indexedStepProductionRegisters)=
      indexedSchedulePrimitiveFormula256 indexedStepProductionRegisters 1 1620 :=
  indexedScheduleAdaptive256_primitive _ _ _ secp256k1ScheduleLayout_production rfl rfl rfl rfl


end ShorECDLP.Paper2607_13816
