import ShorECDLP.Submission.«2607_13816».EEA.ControlPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ShiftPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
namespace ShorECDLP.Paper2607_13816
open Quantum

private theorem terminalControl9_primitive (r : IndexedStepRegisters)
    (hr : r.lengthRPrime.length=9) (hs : 8≤r.blockScratch.length) :
    primitiveResources (.unitary (computeControl (r.phase1::r.lengthRPrime)
      (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch) .done)=
      (⟨2,0,0,17,0,0⟩ : PrimitiveResources) := by
  rw [computeControl_primitive _ _ _ _ (by simp only [List.length_cons,hr]; omega),List.length_cons,hr]
  rfl

/-- The complete production A block counts both terminal tests, padding, shift and spill. -/
theorem blockAForward259_primitive (r : IndexedStepRegisters)
    (hp : TerminalPaddingLayout r.terminalPadding) (hh : ShiftLayout r.preShift)
    (hw : r.work2.length=259) (hl : r.lengthS.length=9)
    (hr : r.lengthRPrime.length=9) (hs : 8≤r.blockScratch.length) :
    primitiveResources (.unitary (blockAForward r) .done)=
      (⟨108,0,1599,906,0,0⟩ : PrimitiveResources) := by
  change primitiveResources (.unitary ((((((computeControl (r.phase1::r.lengthRPrime)
    (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch ++ terminalPaddingForward r.terminalPadding) ++
    [.CX r.terminal r.phase1]) ++ preShiftUnitary r.preShift) ++ [.CX r.terminal r.phase1]) ++
    terminalEpochSpill r.terminal r.shiftEpoch r.quotientLow) ++
    computeControl (r.phase1::r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch) .done)=_
  simp only [primitiveResources_unitary_append]
  rw [terminalControl9_primitive r hr hs,
    terminalPaddingForward259_primitive r.terminalPadding hp hw hl,
    preShiftUnitary259_primitive r.preShift hh hw hl]
  rw [primitiveResources_unitary_HPFree _ _ (terminalEpochSpill_HPFree _ _ _),
    terminalEpochSpill_xCount,terminalEpochSpill_cnotCount,terminalEpochSpill_toffoliCount]
  rfl

/-- The production C block restores the epoch between two complete terminal tests. -/
theorem blockCForward9_primitive (r : IndexedStepRegisters)
    (hr : r.lengthRPrime.length=9) (hs : 8≤r.blockScratch.length) :
    primitiveResources (.unitary (blockCForward r) .done)=
      (⟨4,0,3,35,0,0⟩ : PrimitiveResources) := by
  change primitiveResources (.unitary ((computeControl (r.phase1::r.lengthRPrime)
    (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch ++
    terminalEpochRestore r.terminal r.shiftEpoch r.quotientLow) ++
    computeControl (r.phase1::r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch) .done)=_
  simp only [primitiveResources_unitary_append]
  rw [terminalControl9_primitive r hr hs,
    primitiveResources_unitary_HPFree _ _ (terminalEpochRestore_HPFree _ _ _),
    terminalEpochRestore_xCount,terminalEpochRestore_cnotCount,terminalEpochRestore_toffoliCount]
  rfl
/-- The explicit inverse A block includes the padding inverse's extra 32 X gates. -/
theorem blockAInverse259_primitive (r : IndexedStepRegisters)
    (hp : TerminalPaddingLayout r.terminalPadding) (hh : ShiftLayout r.preShift)
    (hw : r.work2.length=259) (hl : r.lengthS.length=9)
    (hr : r.lengthRPrime.length=9) (hs : 8≤r.blockScratch.length) :
    primitiveResources (.unitary (blockAInverse r) .done)=
      (⟨140,0,1599,906,0,0⟩ : PrimitiveResources) := by
  change primitiveResources (.unitary ((((((computeControl (r.phase1::r.lengthRPrime)
    (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch ++
    terminalEpochRestore r.terminal r.shiftEpoch r.quotientLow) ++ [.CX r.terminal r.phase1]) ++
    (preShiftUnitary r.preShift).adjoint) ++ [.CX r.terminal r.phase1]) ++
    terminalPaddingInverse r.terminalPadding) ++ computeControl (r.phase1::r.lengthRPrime)
    (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch) .done)=_
  simp only [primitiveResources_unitary_append,primitiveResources_unitary_adjoint]
  rw [terminalControl9_primitive r hr hs,terminalPaddingInverse259_primitive r.terminalPadding hp hw hl,
    preShiftUnitary259_primitive r.preShift hh hw hl,
    primitiveResources_unitary_HPFree _ _ (terminalEpochRestore_HPFree _ _ _),
    terminalEpochRestore_xCount,terminalEpochRestore_cnotCount,terminalEpochRestore_toffoliCount]
  rfl
/-- The production C block spills the epoch between two complete terminal tests. -/
theorem blockCInverse9_primitive (r : IndexedStepRegisters)
    (hr : r.lengthRPrime.length=9) (hs : 8≤r.blockScratch.length) :
    primitiveResources (.unitary (blockCInverse r) .done)=
      (⟨4,0,3,35,0,0⟩ : PrimitiveResources) := by
  change primitiveResources (.unitary ((computeControl (r.phase1::r.lengthRPrime)
    (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch ++
    terminalEpochSpill r.terminal r.shiftEpoch r.quotientLow) ++
    computeControl (r.phase1::r.lengthRPrime) (2^(r.lengthRPrime.length+1)-2) r.terminal r.blockScratch) .done)=_
  simp only [primitiveResources_unitary_append]
  rw [terminalControl9_primitive r hr hs,
    primitiveResources_unitary_HPFree _ _ (terminalEpochSpill_HPFree _ _ _),
    terminalEpochSpill_xCount,terminalEpochSpill_cnotCount,terminalEpochSpill_toffoliCount]
  rfl

end ShorECDLP.Paper2607_13816
